## Historical data

Crate with methods to manage data that stores its own history.

This covers:
- linear history driven data, eg. transactional layers for overlay.
- long term storage with multiple branch, eg. offchain storage.

General design is container where query are done depending on a local history context
and update requires a global history context.

Internally storage of multiple state is done independantly for each values, as oposed to a trie
where a global state is use to index all content. Each key value manages its own history.

This crates is `no_std` compatible as long as the `std` feature is not enabled.

For more information see <https://crates.io/historical-data>

License: GPL-3.0
