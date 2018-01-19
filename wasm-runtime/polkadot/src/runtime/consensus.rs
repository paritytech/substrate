use runtime_support::Vec;
use storable::StorageVec;
use primitives::SessionKey;

struct AuthorityStorageVec {}
impl StorageVec for AuthorityStorageVec {
	type Item = SessionKey;
	const PREFIX: &'static[u8] = b"con:aut:";
}

/// Get the current set of authorities. These are the session keys.
pub fn authorities() -> Vec<SessionKey> {
	AuthorityStorageVec::items()
}

/// Set the current set of authorities' session keys.
///
/// Called by `next_session` only.
pub fn set_authorities(authorities: &[SessionKey]) {
	AuthorityStorageVec::set_items(authorities);
}

/// Set a single authority by index.
pub fn set_authority(index: u32, key: &SessionKey) {
	AuthorityStorageVec::set_item(index, key);
}
