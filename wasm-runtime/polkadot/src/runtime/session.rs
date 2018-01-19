use runtime_support::Vec;
use keyedvec::KeyedVec;
use storable::{kill, Storable, StorageVec};
use primitives::{AccountID, SessionKey, BlockNumber};
use runtime::{system, staking, consensus};

struct ValidatorStorageVec {}
impl StorageVec for ValidatorStorageVec {
	type Item = AccountID;
	const PREFIX: &'static[u8] = b"ses\0key\0";
}

// TRANSACTION API (available to all transactors)

/// Sets the session key of `_validator` to `_key`. This doesn't take effect until the next
/// session.
pub fn set_key(validator: &AccountID, key: &SessionKey) {
	// set new value for next session
	key.store(&validator.to_keyed_vec(b"ses\0nxt\0"));
}

// PUBLIC API (available to other runtime modules)

/// Get the current set of authorities. These are the session keys.
fn validators() -> Vec<AccountID> {
	ValidatorStorageVec::items()
}

/// Set the current set of validators.
///
/// Called by staking::next_era() only. `next_session` should be called after this in order to
/// update the session keys to the next validator set.
pub fn set_validators(new: &[AccountID]) {
	ValidatorStorageVec::set_items(new);
	consensus::set_authorities(new);
}

/// The number of blocks in each session.
pub fn length() -> BlockNumber {
	Storable::lookup_default(b"ses\0bps")
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
	validators().iter().enumerate().for_each(|(i, v)| {
		let k = v.to_keyed_vec(b"ses\0nxt\0");
		if let Some(n) = Storable::lookup(&k) {
			consensus::set_authority(i as u32, &n);
			kill(&k);
		}
	});
}

// TODO: tests
