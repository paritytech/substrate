## Historical data

Crate for managing data and their associated history.

This covers:
- data with a sequential history, eg. transactional layers and their associated changes.

This crate is storing single historical data, for instance in a sequential list of state.
Historical collection of data will therefore be preferably a collection of individual historical data.
For instance with historical data being a list of change, a collection of historical data will
be a collection of list rather than a list of collection.

For multiple individual data, we refer to a global historical state,
query and update actions are using it as an input parameter.

This crate is `no_std` compatible if the `std` feature is not enabled.

For more information see <https://crates.io/historical-data>

License: GPL-3.0
