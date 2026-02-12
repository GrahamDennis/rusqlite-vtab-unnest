use std::ffi::{CStr, c_int};
use std::marker::PhantomData;
use std::rc::Rc;

use rusqlite::ffi;
use rusqlite::types::{ToSql, ToSqlOutput, Value, ValueRef};
use rusqlite::vtab::value_pointer::ValuePointer;
use rusqlite::vtab::{
    Context, CreateVTab, Filters, IndexConstraintOp, IndexInfo, VTab, VTabConnection, VTabCursor,
    eponymous_only_module, read_only_module,
};
use rusqlite::{Connection, Result};
use std::str::FromStr;

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

impl ToSql for ValueArray {
    fn to_sql(&self) -> Result<ToSqlOutput<'_>> {
        Ok(ToSqlOutput::ValuePointer(ValuePointer {
            value: self.0.clone(),
            pointer_type: VALUE_ARRAY_TYPE,
        }))
    }
}

impl From<Vec<i64>> for ValueArray {
    fn from(value: Vec<i64>) -> Self {
        Self(Rc::new(ValueArrayInner::Integer(value)))
    }
}

impl ValueArray {
    fn len(&self) -> usize {
        match self.0.as_ref() {
            ValueArrayInner::Null(length) => *length,
            ValueArrayInner::Integer(items) => items.len(),
            ValueArrayInner::Real(items) => items.len(),
            ValueArrayInner::Text(items) => items.len(),
            ValueArrayInner::Blob(items) => items.len(),
        }
    }

    fn get(&self, idx: usize) -> ToSqlOutput<'_> {
        match self.0.as_ref() {
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

pub(crate) const VALUE_ARRAY_TYPE: &CStr = c"value_array";

/// An instance of the unnset virtual table
#[repr(C)]
struct UnnestTab {
    /// Base class. Must be first
    base: ffi::sqlite3_vtab,
    column_count: usize,
}

unsafe impl<'vtab> VTab<'vtab> for UnnestTab {
    type Aux = ();
    type Cursor = UnnestTabCursor<'vtab>;

    fn connect(
        _: &mut VTabConnection,
        _aux: Option<&()>,
        args: &[&[u8]],
    ) -> Result<(String, Self)> {
        let vtab = Self {
            base: ffi::sqlite3_vtab::default(),
            column_count: args.len(),
        };
        if args.len() != 4 {
            return Err(rusqlite::Error::ModuleError(format!(
                "Incorrect argument count, received {} arguments expected 1",
                args.len() - 3
            )));
        }
        let column_count_bytes = args[3];
        let column_count_str =
            str::from_utf8(column_count_bytes).map_err(|err| rusqlite::Error::Utf8Error(err))?;
        let column_count: usize = usize::from_str(column_count_str).map_err(|err| {
            rusqlite::Error::ModuleError(format!(
                "failed to parse column count '{}'; error {:?}",
                column_count_str, err
            ))
        })?;
        if column_count == 0 {
            return Err(rusqlite::Error::ModuleError(
                "Cannot create an unnest table with 0 columns".to_string(),
            ));
        }
        Ok((
            format!(
                "CREATE TABLE x({}, {})",
                (0..column_count)
                    .map(|_| "value")
                    .collect::<Vec<_>>()
                    .join(", "),
                (0..column_count)
                    .map(|_| "pointer hidden")
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            vtab,
        ))
    }

    fn best_index(&self, info: &mut IndexInfo) -> Result<()> {
        // Index of the pointer= constraints
        let mut pointer_constraints: usize = 0;
        let expected_constraints: usize = (1 << self.column_count) - 1;
        let column_count_i32 = self.column_count as i32;
        for (constraint, mut constraint_usage) in info.constraints_and_usages() {
            if !constraint.is_usable() {
                continue;
            }
            if constraint.operator() != IndexConstraintOp::SQLITE_INDEX_CONSTRAINT_EQ {
                continue;
            }
            if constraint.column() >= (self.column_count as i32) {
                pointer_constraints |= 1 << (constraint.column() - column_count_i32);
                constraint_usage.set_argv_index(constraint.column() - column_count_i32);
                constraint_usage.set_omit(true);
            }
        }
        if pointer_constraints != expected_constraints {
            info.set_estimated_cost(1_f64);
            info.set_estimated_rows(100);
            info.set_idx_num(1);
        } else {
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
struct UnnestTabCursor<'vtab> {
    /// Base class. Must be first
    base: ffi::sqlite3_vtab_cursor,
    /// The rowid
    row_id: usize,
    column_count: usize,
    /// The value arrays
    cols: Option<Vec<Rc<ValueArray>>>,
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
    fn filter(&mut self, idx_num: c_int, _idx_str: Option<&str>, args: &Filters<'_>) -> Result<()> {
        let cols: Vec<_> = (0..self.column_count)
            .into_iter()
            .map(|idx| {
                args.get_pointer(idx, VALUE_ARRAY_TYPE)
                    .ok_or(rusqlite::Error::InvalidColumnIndex(idx))
            })
            .collect::<Result<Vec<_>>>()?;
        let cols = cols
            .into_iter()
            .map(|col| col.downcast().map_err(|_| rusqlite::Error::InvalidQuery))
            .collect::<Result<Vec<Rc<ValueArray>>>>()?;

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
        let column_idx: usize = i as usize;
        if let Some(ref columns) = self.cols {
            if column_idx < self.column_count {
                let column = columns
                    .get(i as usize)
                    .ok_or(rusqlite::Error::InvalidColumnIndex(column_idx))?;
                let value = column.get(self.row_id);
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
    #[cfg(all(target_family = "wasm", target_os = "unknown"))]
    use wasm_bindgen_test::wasm_bindgen_test as test;

    use super::*;

    use rusqlite::{Connection, Result};
    use std::rc::Rc;

    #[test]
    fn test_unnest_one_argument() -> Result<()> {
        let db = Connection::open_in_memory()?;
        load_module(&db)?;

        let values = vec![1i64, 2, 3, 4];
        let ptr = ValueArray::from(values);
        {
            db.execute("CREATE VIRTUAL TABLE unnest1 using unnest(1)", [])?;

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
}
