use keyedvec::KeyedVec;
use storable::Storable;
use primitives::{BlockNumber, Balance, AccountID};
use runtime::{system, session};

// Each validator's stake has one amount in each of three states:
// - inactive: free to be transferred.
// - active: currently representing a validator.
// - deactivating: recently representing a validator and not yet ready for transfer.

/// The length of a staking era in sessions.
pub fn lockup_eras() -> BlockNumber {
	Storable::lookup_default(b"sta\0lpe")
}

/// The length of a staking era in blocks.
pub fn era_length() -> BlockNumber {
	sessions_per_era() * session::length()
}

/// The length of a staking era in sessions.
pub fn sessions_per_era() -> BlockNumber {
	Storable::lookup_default(b"sta\0spe")
}

/// The current era index.
pub fn current_era() -> BlockNumber {
	Storable::lookup_default(b"sta\0era")
}

/// The current era index.
pub fn set_current_era(new: BlockNumber) {
	new.store(b"sta\0era");
}

/// The block number at which the era length last changed.
pub fn last_era_length_change() -> BlockNumber {
	Storable::lookup_default(b"sta\0lec")
}

/// Set a new era length. Won't kick in until the next era change (at current length).
pub fn set_sessions_per_era(new: BlockNumber) {
	new.store(b"sta\0nse");
}

/// The era has changed - enact new staking set.
///
/// NOTE: This always happens on a session change.
fn new_era() {
	// Increment current era.
	set_current_era(current_era() + 1);

	// Enact era length change.
	let next_spe: u64 = Storable::lookup_default(b"sta\0nse");
	if next_spe > 0 && next_spe != sessions_per_era() {
		next_spe.store(b"sta\0spe");
		system::block_number().store(b"sta\0lec");
	}

	// TODO: evaluate desired staking amounts and nominations and optimise to find the best
	// combination of validators, then use session::set_validators().
}

/// The balance of a given account.
pub fn balance_inactive(who: &AccountID) -> Balance {
	Storable::lookup_default(&who.to_keyed_vec(b"sta\0bal\0"))
}

/// Transfer some unlocked staking balance to another staker.
pub fn transfer_inactive(transactor: &AccountID, dest: &AccountID, value: Balance) {
	let from_key = transactor.to_keyed_vec(b"sta\0bal\0");
	let from_balance: Balance = Storable::lookup_default(&from_key);
	assert!(from_balance >= value);
	let to_key = dest.to_keyed_vec(b"sta\0bal\0");
	let to_balance: Balance = Storable::lookup_default(&to_key);
	assert!(to_balance + value > to_balance);	// no overflow
	(from_balance - value).store(&from_key);
	(to_balance + value).store(&to_key);
}

/// Declare the desire to stake for the transactor.
///
/// Effects will be felt at the beginning of the next era.
pub fn stake(_transactor: &AccountID) {
	// TODO: record the desire for `_transactor` to activate their stake.
}

/// Retract the desire to stake for the transactor.
///
/// Effects will be felt at the beginning of the next era.
pub fn unstake(_transactor: &AccountID) {
	// TODO: record the desire for `_transactor` to deactivate their stake.
}

/// Hook to be called after to transaction processing.
pub fn check_new_era() {
	// check block number and call new_era if necessary.
	if (system::block_number() - last_era_length_change()) % era_length() == 0 {
		new_era();
	}
}

#[cfg(test)]
mod tests {
	use runtime_support::with_externalities;
	use keyedvec::KeyedVec;
	use joiner::Joiner;
	use testing::{one, two, TestExternalities};
	use primitives::AccountID;
	use runtime::staking;
	use environment::with_env;

	#[test]
	fn staking_eras_work() {
		let mut t = TestExternalities { storage: map![
			b"ses\0bps".to_vec() => vec![].join(&1u64),
			b"sta\0spe".to_vec() => vec![].join(&2u64)
		], };
		with_externalities(&mut t, || {
			assert_eq!(staking::era_length(), 2u64);
			assert_eq!(staking::sessions_per_era(), 2u64);
			assert_eq!(staking::last_era_length_change(), 0u64);
			assert_eq!(staking::current_era(), 0u64);

			// Block 1: No change.
			with_env(|e| e.block_number = 1);
			staking::check_new_era();
			assert_eq!(staking::sessions_per_era(), 2u64);
			assert_eq!(staking::last_era_length_change(), 0u64);
			assert_eq!(staking::current_era(), 0u64);

			// Block 2: Simple era change.
			with_env(|e| e.block_number = 2);
			staking::check_new_era();
			assert_eq!(staking::sessions_per_era(), 2u64);
			assert_eq!(staking::last_era_length_change(), 0u64);
			assert_eq!(staking::current_era(), 1u64);

			// Block 3: Schedule an era length change; no visible changes.
			with_env(|e| e.block_number = 3);
			staking::set_sessions_per_era(3);
			staking::check_new_era();
			assert_eq!(staking::sessions_per_era(), 2u64);
			assert_eq!(staking::last_era_length_change(), 0u64);
			assert_eq!(staking::current_era(), 1u64);

			// Block 4: Era change kicks in.
			with_env(|e| e.block_number = 4);
			staking::check_new_era();
			assert_eq!(staking::sessions_per_era(), 3u64);
			assert_eq!(staking::last_era_length_change(), 4u64);
			assert_eq!(staking::current_era(), 2u64);

			// Block 5: No change.
			with_env(|e| e.block_number = 5);
			staking::check_new_era();
			assert_eq!(staking::sessions_per_era(), 3u64);
			assert_eq!(staking::last_era_length_change(), 4u64);
			assert_eq!(staking::current_era(), 2u64);

			// Block 6: No change.
			with_env(|e| e.block_number = 6);
			staking::check_new_era();
			assert_eq!(staking::sessions_per_era(), 3u64);
			assert_eq!(staking::last_era_length_change(), 4u64);
			assert_eq!(staking::current_era(), 2u64);

			// Block 7: Era increment.
			with_env(|e| e.block_number = 7);
			staking::check_new_era();
			assert_eq!(staking::sessions_per_era(), 3u64);
			assert_eq!(staking::last_era_length_change(), 4u64);
			assert_eq!(staking::current_era(), 3u64);
		});
	}

	#[test]
	fn staking_balance_works() {
		let one = one();
		let two = two();

		let mut t = TestExternalities { storage: map![
			one.to_keyed_vec(b"sta\0bal\0") => vec![].join(&42u64)
		], };

		with_externalities(&mut t, || {
			assert_eq!(staking::balance_inactive(&one), 42);
			assert_eq!(staking::balance_inactive(&two), 0);
		});
	}

	#[test]
	fn staking_balance_transfer_works() {
		let one = one();
		let two = two();

		let mut t = TestExternalities { storage: map![
			one.to_keyed_vec(b"sta\0bal\0") => vec![].join(&111u64)
		], };

		with_externalities(&mut t, || {
			staking::transfer_inactive(&one, &two, 69);
			assert_eq!(staking::balance_inactive(&one), 42);
			assert_eq!(staking::balance_inactive(&two), 69);
		});
	}
}
