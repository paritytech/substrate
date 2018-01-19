use runtime_support::Vec;
use keyedvec::KeyedVec;
use storable::{kill, Storable, StorageVec};
use primitives::{AccountID, SessionKey, BlockNumber};
use runtime::{system, staking, consensus};

struct ValidatorStorageVec {}
impl StorageVec for ValidatorStorageVec {
	type Item = AccountID;
	const PREFIX: &'static[u8] = b"ses:key:";
}

// TRANSACTION API (available to all transactors)

/// Sets the session key of `_validator` to `_key`. This doesn't take effect until the next
/// session.
pub fn set_key(validator: &AccountID, key: &SessionKey) {
	// set new value for next session
	key.store(&validator.to_keyed_vec(b"ses:nxt:"));
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
	Storable::lookup_default(b"ses:len")
}

/// The current era index.
pub fn current_index() -> BlockNumber {
	Storable::lookup_default(b"ses:ind")
}

/// Set the current era index.
pub fn set_current_index(new: BlockNumber) {
	new.store(b"ses:ind");
}

/// The block number at which the era length last changed.
pub fn last_length_change() -> BlockNumber {
	Storable::lookup_default(b"ses:llc")
}

/// Set a new era length. Won't kick in until the next era change (at current length).
pub fn set_length(new: BlockNumber) {
	new.store(b"ses:nln");
}

/// Hook to be called after transaction processing.
pub fn check_rotate_session() {
	// do this last, after the staking system has had chance to switch out the authorities for the
	// new set.
	// check block number and call next_session if necessary.
	if (system::block_number() - last_length_change()) % length() == 0 {
		rotate_session();
	}
}

// PRIVATE (not available for use externally)

/// Move onto next session: register the new authority set.
fn rotate_session() {
	// Increment current session index.
	set_current_index(current_index() + 1);

	// Enact era length change.
	if let Some(next_len) = u64::lookup(b"ses:nln") {
		next_len.store(b"ses:len");
		system::block_number().store(b"ses:llc");
		kill(b"ses:nln");
	}

	// Update any changes in session keys.
	validators().iter().enumerate().for_each(|(i, v)| {
		let k = v.to_keyed_vec(b"ses:nxt:");
		if let Some(n) = Storable::lookup(&k) {
			consensus::set_authority(i as u32, &n);
			kill(&k);
		}
	});
}

#[cfg(test)]
mod tests {
	use runtime_support::{with_externalities, twox_128};
	use keyedvec::KeyedVec;
	use joiner::Joiner;
	use testing::{one, two, TestExternalities};
	use primitives::AccountID;
	use runtime::{consensus, session};
	use environment::with_env;

	fn simple_setup() -> TestExternalities {
		TestExternalities { storage: map![
			twox_128(b"ses:len").to_vec() => vec![].join(&2u64),
			// the validators (10, 20, ...)
			twox_128(b"ses:key:len").to_vec() => vec![].join(&2u32),
			twox_128(&0u32.to_keyed_vec(b"ses:key:")).to_vec() => vec![10; 32],
			twox_128(&1u32.to_keyed_vec(b"ses:key:")).to_vec() => vec![20; 32],
			// initial session keys (11, 21, ...)
			twox_128(b"con:aut:len").to_vec() => vec![].join(&2u32),
			twox_128(&0u32.to_keyed_vec(b"con:aut:")).to_vec() => vec![11; 32],
			twox_128(&1u32.to_keyed_vec(b"con:aut:")).to_vec() => vec![21; 32]
		], }
	}

	#[test]
	fn simple_setup_should_work() {
		let mut t = simple_setup();
		with_externalities(&mut t, || {
			assert_eq!(consensus::authorities(), vec![[11u8; 32], [21u8; 32]]);
			assert_eq!(session::length(), 2u64);
			assert_eq!(session::validators(), vec![[10u8; 32], [20u8; 32]]);
		});
	}

	#[test]
	fn session_length_change_should_work() {
		let mut t = simple_setup();
		with_externalities(&mut t, || {
			// Block 1: Change to length 3; no visible change.
			with_env(|e| e.block_number = 1);
			session::set_length(3);
			session::check_rotate_session();
			assert_eq!(session::length(), 2);
			assert_eq!(session::current_index(), 0);

			// Block 2: Length now changed to 3. Index incremented.
			with_env(|e| e.block_number = 2);
			session::set_length(3);
			session::check_rotate_session();
			assert_eq!(session::length(), 3);
			assert_eq!(session::current_index(), 1);

			// Block 3: Length now changed to 3. Index incremented.
			with_env(|e| e.block_number = 3);
			session::check_rotate_session();
			assert_eq!(session::length(), 3);
			assert_eq!(session::current_index(), 1);

			// Block 4: Change to length 2; no visible change.
			with_env(|e| e.block_number = 4);
			session::set_length(2);
			session::check_rotate_session();
			assert_eq!(session::length(), 3);
			assert_eq!(session::current_index(), 1);

			// Block 5: Length now changed to 2. Index incremented.
			with_env(|e| e.block_number = 5);
			session::check_rotate_session();
			assert_eq!(session::length(), 2);
			assert_eq!(session::current_index(), 2);

			// Block 6: No change.
			with_env(|e| e.block_number = 6);
			session::check_rotate_session();
			assert_eq!(session::length(), 2);
			assert_eq!(session::current_index(), 2);

			// Block 7: Next index.
			with_env(|e| e.block_number = 7);
			session::check_rotate_session();
			assert_eq!(session::length(), 2);
			assert_eq!(session::current_index(), 3);
		});
	}

	#[test]
	fn session_change_should_work() {
		let mut t = simple_setup();
		with_externalities(&mut t, || {
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
