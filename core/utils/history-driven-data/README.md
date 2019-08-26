## History driven data

Crate with methods to manage data that stores its own history.

This covers:
- linear history driven data, eg. transactional layers for overlay.
- long term storage with multiple branch, eg. offchain storage.

General design is container where query and update requires global
history context.

History is serialize as a per item basis.


This crates should be `no_std` compatible, feature `std` should be use
for std usage.

For more information see <https://crates.io/substrate-wasm-builder>

License: GPL-3.0
