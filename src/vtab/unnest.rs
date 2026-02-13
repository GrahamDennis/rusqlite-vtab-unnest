//! Unnest Virtual Tables.
//!
//! This virtual table is inspired by PostgreSQL's
//! [unnest](https://www.postgresql.org/docs/current/functions-array.html) table-valued function
//!
//!
//! # Example
//!
//! ```
//! # use rusqlite::{types::Value, Connection, Result, params};
//! # use std::rc::Rc;
//! # use rusqlite_vtab_unnest::vtab::unnest::ValueArray;
//! fn example(db: &Connection) -> Result<()> {
//!     // Note: This should be done once (usually when opening the DB).
//!     rusqlite_vtab_unnest::vtab::unnest::load_module(&db)?;
//!     // Note: virtual tables need to be constructed for each number of arguments desired
//!     db.execute("CREATE VIRTUAL TABLE unnest2 using unnest(value_1, value_2)", [])?;
//!     let v1 = ValueArray::from([1i64, 2, 3, 4]);
//!     let v2 = ValueArray::from([5i64, 6, 7, 8]);
//!     let mut stmt = db.prepare("SELECT value_1, value_2 from unnest(?1, ?2);")?;
//!     let rows = stmt.query_map([v1, v2], |row| Ok((row.get::<_, i64>(0)?, row.get::<_, i64>(1)?)))?;
//!     for row in rows {
//!         println!("{:?}", row?);
//!     }
//!     Ok(())
//! }
//! ```
use std::ffi::c_int;
use std::marker::PhantomData;
use std::rc::Rc;

use rusqlite::ffi;
use rusqlite::types::{ToSql, ToSqlOutput, Value, ValueRef};
use rusqlite::vtab::value_pointer::PointerType;
use rusqlite::vtab::{
    Context, CreateVTab, Filters, IndexConstraintOp, IndexInfo, VTab, VTabConnection, VTabCursor,
    escape_double_quote, read_only_module,
};
use rusqlite::{Connection, Result};
use tracing::{Level, trace};

// http://sqlite.org/bindptr.html
/// Register the "unnest" module.
pub fn load_module(conn: &Connection) -> Result<()> {
    let aux: Option<()> = None;
    conn.create_module(c"unnest", read_only_module::<UnnestTab>(), aux)
}

#[derive(Clone, Debug, PartialEq)]
pub struct ValueArray(Rc<ValueArrayInner>);

#[derive(Clone, Debug, PartialEq)]
pub enum ValueArrayInner {
    /// The value is a `NULL` value.
    Null(usize),
    /// The value is a signed integer.
    Integer(Vec<i64>),
    /// The value is a floating point number.
    Real(Vec<f64>),
    /// The value is a text string.
    Text(Vec<String>),
    /// The value is a blob of data
    Blob(Vec<Vec<u8>>),
}

const VALUE_ARRAY_POINTER_TYPE: PointerType<ValueArrayInner> = PointerType::new(c"ValueArrayInner");

impl ToSql for ValueArray {
    fn to_sql(&self) -> Result<ToSqlOutput<'_>> {
        Ok(VALUE_ARRAY_POINTER_TYPE.to_sql(&self.0))
    }
}

// FIXME: Add more From impls
impl From<Vec<i64>> for ValueArray {
    fn from(value: Vec<i64>) -> Self {
        Self(Rc::new(ValueArrayInner::Integer(value)))
    }
}

impl From<&[i64]> for ValueArray {
    fn from(value: &[i64]) -> Self {
        Self(Rc::new(ValueArrayInner::Integer(value.to_vec())))
    }
}

impl<const N: usize> From<[i64; N]> for ValueArray {
    fn from(value: [i64; N]) -> Self {
        Self(Rc::new(ValueArrayInner::Integer(value.to_vec())))
    }
}

impl ValueArrayInner {
    fn len(&self) -> usize {
        match self {
            ValueArrayInner::Null(length) => *length,
            ValueArrayInner::Integer(items) => items.len(),
            ValueArrayInner::Real(items) => items.len(),
            ValueArrayInner::Text(items) => items.len(),
            ValueArrayInner::Blob(items) => items.len(),
        }
    }

    fn get(&self, idx: usize) -> ToSqlOutput<'_> {
        match self {
            ValueArrayInner::Null(_) => ToSqlOutput::Owned(Value::Null),
            ValueArrayInner::Integer(items) => ToSqlOutput::Owned(Value::Integer(items[idx])),
            ValueArrayInner::Real(items) => ToSqlOutput::Owned(Value::Real(items[idx])),
            ValueArrayInner::Text(items) => {
                ToSqlOutput::Borrowed(ValueRef::Text(items[idx].as_bytes()))
            }
            ValueArrayInner::Blob(items) => ToSqlOutput::Borrowed(ValueRef::Blob(&items[idx])),
        }
    }
}

/// An instance of the unnset virtual table
#[repr(C)]
#[derive(Debug)]
struct UnnestTab {
    /// Base class. Must be first
    base: ffi::sqlite3_vtab,
    column_count: usize,
}

unsafe impl<'vtab> VTab<'vtab> for UnnestTab {
    type Aux = ();
    type Cursor = UnnestTabCursor<'vtab>;

    #[tracing::instrument(
        level = Level::TRACE,
        skip_all,
        fields(args=?args.iter().map(|a| str::from_utf8(a)).collect::<Result<Vec<_>, _>>()?),
        ret,
        err
    )]
    fn connect(
        _: &mut VTabConnection,
        _aux: Option<&()>,
        args: &[&[u8]],
    ) -> Result<(String, Self)> {
        if args.len() < 3 {
            return Err(rusqlite::Error::ModuleError(format!(
                "Incorrect argument count, received {} arguments expected at least 3",
                args.len()
            )));
        }
        let column_names_bytes = &args[3..];
        let column_names_str = column_names_bytes
            .iter()
            .map(|column_name_bytes| str::from_utf8(column_name_bytes))
            .collect::<Result<Vec<_>, _>>()
            .map_err(rusqlite::Error::Utf8Error)?;
        let column_count: usize = column_names_str.len();
        let vtab = Self {
            base: ffi::sqlite3_vtab::default(),
            column_count,
        };

        let mut sql = String::from("CREATE TABLE x(");
        for (idx, column_name) in column_names_str.iter().enumerate() {
            let escaped_column_name = escape_double_quote(column_name);
            sql.push('"');
            sql.push_str(&escaped_column_name);
            sql.push_str(r#"", "pointer_"#);
            sql.push_str(&escaped_column_name);
            if idx == column_names_str.len() - 1 {
                sql.push_str(r#"" hidden);"#);
            } else {
                sql.push_str(r#"" hidden, "#);
            }
        }

        Ok((sql, vtab))
    }

    #[tracing::instrument(
        level = Level::TRACE,
        skip_all,
        ret,
        err
    )]
    fn best_index(&self, info: &mut IndexInfo) -> Result<()> {
        // Index of the pointer= constraints
        let mut pointer_constraints: usize = 0;
        let expected_constraints: usize = (1 << self.column_count) - 1;
        for (constraint, mut constraint_usage) in info.constraints_and_usages() {
            if !constraint.is_usable() {
                continue;
            }
            if constraint.operator() != IndexConstraintOp::SQLITE_INDEX_CONSTRAINT_EQ {
                continue;
            }
            if (constraint.column() % 2) == 1 {
                let col_idx = constraint.column() / 2;
                trace!(col_idx, "Accepting constraint");
                pointer_constraints |= 1 << col_idx;
                constraint_usage.set_argv_index(1 + col_idx);
                constraint_usage.set_omit(true);
            }
        }
        if pointer_constraints == expected_constraints {
            trace!(
                column_count = self.column_count,
                pointer_constraints, expected_constraints, "supported access method",
            );
            info.set_estimated_cost(1_f64);
            info.set_estimated_rows(100);
            info.set_idx_num(1);
        } else {
            trace!(
                column_count = self.column_count,
                pointer_constraints, expected_constraints, "unsupported access method",
            );
            return Err(rusqlite::Error::SqliteFailure(
                rusqlite::ffi::Error::new(rusqlite::ffi::SQLITE_CONSTRAINT),
                Some("Unsupported access method".to_string()),
            ));
        }
        Ok(())
    }

    fn open(&mut self) -> Result<UnnestTabCursor<'_>> {
        Ok(UnnestTabCursor::new(self.column_count))
    }
}

impl<'vtab> CreateVTab<'vtab> for UnnestTab {
    const KIND: rusqlite::vtab::VTabKind = rusqlite::vtab::VTabKind::Default;
}

/// A cursor for the unnset virtual table
#[repr(C)]
#[derive(Debug)]
struct UnnestTabCursor<'vtab> {
    /// Base class. Must be first
    base: ffi::sqlite3_vtab_cursor,
    /// The rowid
    row_id: usize,
    column_count: usize,
    /// The value arrays
    cols: Option<Vec<Rc<ValueArrayInner>>>,
    phantom: PhantomData<&'vtab UnnestTab>,
}

impl UnnestTabCursor<'_> {
    fn new<'vtab>(column_count: usize) -> UnnestTabCursor<'vtab> {
        UnnestTabCursor {
            base: ffi::sqlite3_vtab_cursor::default(),
            row_id: 0,
            column_count,
            cols: None,
            phantom: PhantomData,
        }
    }

    fn row_count(&self) -> usize {
        match self.cols {
            Some(ref a) => a.iter().map(|v| v.len()).min().unwrap_or(0),
            _ => 0,
        }
    }
}
unsafe impl VTabCursor for UnnestTabCursor<'_> {
    #[tracing::instrument(skip(args), level=Level::TRACE)]
    fn filter(&mut self, idx_num: c_int, _idx_str: Option<&str>, args: &Filters<'_>) -> Result<()> {
        let cols: Vec<_> = (0..self.column_count)
            .map(|idx| {
                args.get_pointer(idx, VALUE_ARRAY_POINTER_TYPE)
                    .ok_or(rusqlite::Error::InvalidColumnIndex(idx))
            })
            .collect::<Result<Vec<_>>>()?;

        trace!(?cols, "received unnest columns");
        self.cols = Some(cols);
        self.row_id = 1;
        Ok(())
    }

    fn next(&mut self) -> Result<()> {
        self.row_id += 1;
        Ok(())
    }

    fn eof(&self) -> bool {
        self.row_id > self.row_count()
    }

    fn column(&self, ctx: &mut Context, i: c_int) -> Result<()> {
        let column_idx: usize = (i as usize) / 2;
        trace!(row_id = self.row_id, column_idx, "fetching cell");
        if let Some(ref columns) = self.cols {
            if column_idx < self.column_count {
                let column = columns
                    .get(column_idx)
                    .ok_or(rusqlite::Error::InvalidColumnIndex(column_idx))?;
                let value = column.get(self.row_id - 1);
                ctx.set_result(&value)
            } else {
                Ok(())
            }
        } else {
            Ok(())
        }
    }

    fn rowid(&self) -> Result<i64> {
        Ok(self.row_id as i64)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use rusqlite::{Connection, Result};
    use std::rc::Rc;

    #[test_log::test]
    #[test]
    fn test_unnest_one_argument() -> Result<()> {
        let db = Connection::open_in_memory()?;
        load_module(&db)?;

        let values = vec![1i64, 2, 3, 4];
        let ptr = ValueArray::from(values);
        {
            db.execute("CREATE VIRTUAL TABLE unnest1 using unnest(value)", [])?;

            let mut stmt = db.prepare("SELECT value from unnest1(?1);")?;
            assert_eq!(1, Rc::strong_count(&ptr.0));

            let rows = stmt.query_map([&ptr], |row| row.get::<_, i64>(0))?;
            assert_eq!(2, Rc::strong_count(&ptr.0));
            let mut count = 0;
            for (i, value) in rows.enumerate() {
                assert_eq!(i as i64, value? - 1);
                count += 1;
            }
            assert_eq!(4, count);
        }
        assert_eq!(1, Rc::strong_count(&ptr.0));
        Ok(())
    }

    #[test_log::test]
    #[test]
    fn test_unnest_two_arguments() -> Result<()> {
        let db = Connection::open_in_memory()?;
        load_module(&db)?;

        let values1 = vec![1i64, 2, 3, 4];
        let ptr1 = ValueArray::from(values1);

        let values2 = vec![5i64, 6, 7, 8];
        let ptr2 = ValueArray::from(values2);
        {
            db.execute("CREATE VIRTUAL TABLE unnest2 using unnest(va, vb)", [])?;

            let mut stmt = db.prepare("SELECT va, vb from unnest2(?1, ?2);")?;
            assert_eq!(1, Rc::strong_count(&ptr1.0));
            assert_eq!(1, Rc::strong_count(&ptr2.0));

            let rows = stmt.query_map([&ptr1, &ptr2], |row| {
                Ok((row.get::<_, i64>(0)?, row.get::<_, i64>(1)?))
            })?;
            assert_eq!(2, Rc::strong_count(&ptr1.0));
            assert_eq!(2, Rc::strong_count(&ptr2.0));
            let mut count = 0;
            for (i, pair) in rows.enumerate() {
                let (value1, value2) = pair?;
                assert_eq!(i as i64, value1 - 1);
                assert_eq!(i as i64, value2 - 5);
                count += 1;
            }
            assert_eq!(4, count);
        }
        assert_eq!(1, Rc::strong_count(&ptr1.0));
        assert_eq!(1, Rc::strong_count(&ptr2.0));
        Ok(())
    }
}
