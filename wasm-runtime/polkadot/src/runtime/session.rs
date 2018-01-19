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

/// Hook to be called after transaction processing.
pub fn check_rotate_session() {
	// do this last, after the staking system has had chance to switch out the authorities for the
	// new set.
	// check block number and call next_session if necessary.
	if system::block_number() % length() == 0 {
		rotate_session();
	}
}

// PRIVATE (not available for use externally)

/// Move onto next session: register the new authority set.
fn rotate_session() {
	validators().iter().enumerate().for_each(|(i, v)| {
		let k = v.to_keyed_vec(b"ses\0nxt\0");
		if let Some(n) = Storable::lookup(&k) {
			consensus::set_authority(i as u32, &n);
			kill(&k);
		}
	});
}

#[cfg(test)]
mod tests {
	use runtime_support::with_externalities;
	use keyedvec::KeyedVec;
	use joiner::Joiner;
	use testing::{one, two, TestExternalities};
	use primitives::AccountID;
	use runtime::{consensus, session};
	use environment::with_env;

	#[test]
	fn session_change_should_work() {
		let mut t = TestExternalities { storage: map![
			b"ses\0bps".to_vec() => vec![].join(&2u64),
			// the validators (10, 20, ...)
			b"ses\0key\0len".to_vec() => vec![].join(&2u32),
			0u32.to_keyed_vec(b"ses\0key\0") => vec![10; 32],
			1u32.to_keyed_vec(b"ses\0key\0") => vec![20; 32],
			// initial session keys (11, 21, ...)
			b"con\0aut\0len".to_vec() => vec![].join(&2u32),
			0u32.to_keyed_vec(b"con\0aut\0") => vec![11; 32],
			1u32.to_keyed_vec(b"con\0aut\0") => vec![21; 32]
		], };
		with_externalities(&mut t, || {
			assert_eq!(consensus::authorities(), vec![[11u8; 32], [21u8; 32]]);
			assert_eq!(session::length(), 2u64);
			assert_eq!(session::validators(), vec![[10u8; 32], [20u8; 32]]);

			// Block 1: No change
			with_env(|e| e.block_number = 1);
			session::check_rotate_session();
			assert_eq!(consensus::authorities(), vec![[11u8; 32], [21u8; 32]]);

			// Block 2: Session rollover, but no change.
			with_env(|e| e.block_number = 2);
			session::check_rotate_session();
			assert_eq!(consensus::authorities(), vec![[11u8; 32], [21u8; 32]]);

			// Block 3: Set new key for validator 2; no visible change.
			with_env(|e| e.block_number = 3);
			session::set_key(&[20; 32], &[22; 32]);
			assert_eq!(consensus::authorities(), vec![[11u8; 32], [21u8; 32]]);

			session::check_rotate_session();
			assert_eq!(consensus::authorities(), vec![[11u8; 32], [21u8; 32]]);

			// Block 4: Session rollover, authority 2 changes.
			with_env(|e| e.block_number = 4);
			session::check_rotate_session();
			assert_eq!(consensus::authorities(), vec![[11u8; 32], [22u8; 32]]);
		});
	}
}
