## Historical data

Crate with functionality to manage data that stores its own history.

This covers:
- linear history driven data, eg. transactional layers for overlay.

Design for this crate is to store history of each item in its own container.
Query and update actions can requires requires a global historical state.

This crate is `no_std` compatible as long as the `std` feature is not enabled.

For more information see <https://crates.io/historical-data>

License: GPL-3.0
