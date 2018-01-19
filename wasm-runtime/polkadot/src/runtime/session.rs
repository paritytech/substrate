use runtime_support::Vec;
use keyedvec::KeyedVec;
use storage::Storage;
use primitives::{AccountID, SessionKey, BlockNumber};
use runtime::{system, staking, consensus};

// TRANSACTION API (available to all transactors)

/// Sets the session key of `_transactor` to `_session`. This doesn't take effect until the next
/// session.
pub fn set_key(_transactor: &AccountID, _session: &AccountID) {
	// TODO: record the new session key for `_transactor`, ready for the next session.
}

// PUBLIC API (available to other runtime modules)

/// Get the current set of validators. These are the long-term identifiers for the validators
/// and will be mapped to a session key with the most recent `set_next_session_key`.
pub fn validators() -> Vec<AccountID> {
	// TODO: derive from the actual validator set
	consensus::authorities()
}

/// Set the current set of validators.
///
/// Called by staking::next_era() only.
pub fn set_validators(new: &[AccountID]) {
	// TODO: set the actual validators
	consensus::set_authorities(new);
}

/// The number of blocks in each session.
pub fn length() -> BlockNumber {
	Storage::into(b"con\0bps")
}

/// Hook to be called prior to transaction processing.
pub fn pre_transactions() {
	staking::pre_transactions();
}

/// Hook to be called after to transaction processing.
pub fn post_transactions() {
	staking::post_transactions();

	// do this last, after the staking system has had chance to switch out the authorities for the
	// new set.
	// check block number and call next_session if necessary.
	if system::block_number() % length() == 0 {
		next_session();
	}
}

// PRIVATE (not available)

/// Move onto next session: register the new authority set.
fn next_session() {
	// TODO: Call set_authorities() with any new authorities.
}
