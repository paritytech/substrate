use runtime_support::Vec;
use keyedvec::KeyedVec;
use storage::Storage;
use primitives::{AccountID, SessionKey, BlockNumber};
use storage::storage_into;

pub fn set_authority(index: u32, authority: AccountID) {
	authority.store(&index.to_keyed_vec(b"con\0aut\0"));
}

fn authority(index: u32) -> AccountID {
	storage_into(&index.to_keyed_vec(b"con\0aut\0"))
}

pub fn set_authority_count(count: u32) {
	(count..authority_count()).for_each(|i| set_authority(i, SessionKey::default()));
	count.store(b"con\0aut\0len");
}

fn authority_count() -> u32 {
	storage_into(b"con\0aut\0len")
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

/// Get the current set of validators. These are the long-term identifiers for the validators
/// and will be mapped to a session key with the most recent `set_next_session_key`.
pub fn validators() -> Vec<AccountID> {
	unimplemented!()
}

/// Set the current set of validators.
///
/// Called by staking::next_era() only.
pub fn set_validators(_new: &[AccountID]) {
	unimplemented!()
}

/// The number of blocks in each session.
pub fn session_length() -> BlockNumber {
	storage_into(b"con\0bps")
}

/// Sets the session key of `_transactor` to `_session`. This doesn't take effect until the next
/// session.
pub fn set_session_key(_transactor: &AccountID, _session: &AccountID) {
	unimplemented!()
}

/// Move onto next session: register the new authority set.
pub fn next_session() {
	// TODO: Call set_authorities().
	unimplemented!()
}

/// Hook to be called prior to transaction processing.
pub fn pre_transactions() {}

/// Hook to be called after to transaction processing.
pub fn post_transactions() {
	// TODO: check block number and call next_session if necessary.
}
