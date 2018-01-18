use runtime_support::Vec;
use keyedvec::KeyedVec;
use storage::Storage;
use primitives::{AccountID, SessionKey, BlockNumber};
use runtime::{system, staking};

pub fn set_authority(index: u32, authority: AccountID) {
	authority.store(&index.to_keyed_vec(b"con\0aut\0"));
}

fn authority(index: u32) -> AccountID {
	Storage::into(&index.to_keyed_vec(b"con\0aut\0"))
}

pub fn set_authority_count(count: u32) {
	(count..authority_count()).for_each(|i| set_authority(i, SessionKey::default()));
	count.store(b"con\0aut\0len");
}

fn authority_count() -> u32 {
	Storage::into(b"con\0aut\0len")
}

/// Get the current set of authorities. These are the session keys.
pub fn authorities() -> Vec<AccountID> {
	(0..authority_count()).into_iter().map(authority).collect()
}

/// Set the current set of authorities' session keys.
///
/// Called by `next_session` only.
pub fn set_authorities(authorities: &[AccountID]) {
	set_authority_count(authorities.len() as u32);
	authorities.iter().enumerate().for_each(|(v, &i)| set_authority(v as u32, i));
}
