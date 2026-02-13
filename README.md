# An `unnest` table-valued function for SQLite

PostgreSQL has the table-valued function [unnest](https://www.postgresql.org/docs/current/functions-array.html#:~:text=%E2%86%92%20%7B1%2C2%2C3%2C4%7D-,unnest,-(%20anyarray%20)%20%E2%86%92) which can be used for bulk data operations, e.g.:

```sql
INSERT INTO sensors (ts, sensorid, value) 
  SELECT * 
  FROM unnest(
    $1::timestamptz[], 
    $2::text[], 
    $3::float8[]
  )
```

This simplifies bulk operations because just 3 variables need to be bound (one per column) independent of the number of rows being inserted, vs 3 * N variables if each value was being bound independently.

In SQLite, this optimisation is likely less important because it is an embedded database vs a client/server database, however it can still be a convenience.

The table-valued function supported by this module works like this:

```sql
-- The arguments to unnest are the column names of the virtual table
CREATE VIRTUAL TABLE unnest_sensors using unnest(ts, sensorid, value);

INSERT INTO sensors (ts, sensorid, value)
    SELECT *
    -- bind 1 array for each column
    FROM unnest_sensors($1, $2, $3)
```
