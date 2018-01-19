use keyedvec::KeyedVec;
use storage::Storage;
use primitives::{BlockNumber, Balance, AccountID};
use runtime::{system, session};

// Each validator's stake has one amount in each of three states:
// - inactive: free to be transferred
// - active: currently representing a validator
// - deactivating: recently representing a validator and not yet ready for transfer

/// The length of a staking era in blocks.
pub fn era_length() -> BlockNumber {
	sessions_per_era() * session::length()
}

/// The length of a staking era in sessions.
pub fn sessions_per_era() -> BlockNumber {
	Storage::into(b"sta\0spe")
}

/// The length of a staking era in sessions.
pub fn lockup_eras() -> BlockNumber {
	Storage::into(b"sta\0lpe")
}

/// The era has changed - enact new staking set.
///
/// NOTE: This always happens on a session change.
fn next_era() {
	// TODO: evaluate desired staking amounts and nominations and optimise to find the best
	// combination of validators, then use session::set_validators().
}

/// The balance of a given account.
pub fn balance_inactive(who: &AccountID) -> Balance {
	Storage::into(&who.to_keyed_vec(b"sta\0bal\0"))
}

/// Transfer some unlocked staking balance to another staker.
pub fn transfer_inactive(transactor: &AccountID, dest: &AccountID, value: Balance) {
	let from_key = transactor.to_keyed_vec(b"sta\0bal\0");
	let from_balance: Balance = Storage::into(&from_key);
	assert!(from_balance >= value);
	let to_key = dest.to_keyed_vec(b"sta\0bal\0");
	let to_balance: Balance = Storage::into(&to_key);
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

/// Hook to be called prior to transaction processing.
pub fn pre_transactions() {
}

/// Hook to be called after to transaction processing.
pub fn post_transactions() {
	// check block number and call next_era if necessary.
	if system::block_number() % era_length() == 0 {
		next_era();
	}
}

#[cfg(test)]
mod tests {
	use runtime_support::with_externalities;
	use testing::TestExternalities;
	use primitives::{AccountID};
	use runtime::staking;

	#[test]
	fn staking_balance_works() {
		let one: AccountID = [1u8; 32];
		let two: AccountID = [2u8; 32];

		let mut t = TestExternalities { storage: map![
			{ let mut r = b"sta\0bal\0".to_vec(); r.extend_from_slice(&one); r } => vec![42u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		with_externalities(&mut t, || {
			assert_eq!(staking::balance_inactive(&one), 42);
			assert_eq!(staking::balance_inactive(&two), 0);
		});
	}

	#[test]
	fn staking_balance_transfer_works() {
		let one: AccountID = [1u8; 32];
		let two: AccountID = [2u8; 32];

		let mut t = TestExternalities { storage: map![
			{ let mut r = b"sta\0bal\0".to_vec(); r.extend_from_slice(&one); r } => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		with_externalities(&mut t, || {
			staking::transfer_inactive(&one, &two, 69);
			assert_eq!(staking::balance_inactive(&one), 42);
			assert_eq!(staking::balance_inactive(&two), 69);
		});
	}
}
