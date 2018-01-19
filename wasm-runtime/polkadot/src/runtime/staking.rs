// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Staking manager: Handles balances and periodically determines the best set of validators.

use runtime_support::Vec;
use keyedvec::KeyedVec;
use storable::{Storable, StorageVec};
use primitives::{BlockNumber, AccountID};
use runtime::{system, session};

/// The balance of an account.
pub type Balance = u64;

/// The amount of bonding period left in an account. Measured in eras.
pub type Bondage = u64;

struct IntentionStorageVec {}
impl StorageVec for IntentionStorageVec {
	type Item = AccountID;
	const PREFIX: &'static[u8] = b"ses:wil:";
}

// Each identity's stake may be in one of three bondage states, given by an integer:
// - n | n <= current_era(): inactive: free to be transferred.
// - ~0: active: currently representing a validator.
// - n | n > current_era(): deactivating: recently representing a validator and not yet
//   ready for transfer.

/// The length of the bonding duration in eras.
pub fn bonding_duration() -> BlockNumber {
	Storable::lookup_default(b"sta:loc")
}

/// The length of a staking era in sessions.
pub fn validator_count() -> usize {
	u32::lookup_default(b"sta:vac") as usize
}

/// The length of a staking era in blocks.
pub fn era_length() -> BlockNumber {
	sessions_per_era() * session::length()
}

/// The length of a staking era in sessions.
pub fn sessions_per_era() -> BlockNumber {
	Storable::lookup_default(b"sta:spe")
}

/// The current era index.
pub fn current_era() -> BlockNumber {
	Storable::lookup_default(b"sta:era")
}

/// The block number at which the era length last changed.
pub fn last_era_length_change() -> BlockNumber {
	Storable::lookup_default(b"sta:lec")
}

/// The balance of a given account.
pub fn balance(who: &AccountID) -> Balance {
	Storable::lookup_default(&who.to_keyed_vec(b"sta:bal:"))
}

/// The liquidity-state of a given account.
pub fn bondage(who: &AccountID) -> Bondage {
	Storable::lookup_default(&who.to_keyed_vec(b"sta:bon:"))
}

/// Transfer some unlocked staking balance to another staker.
pub fn transfer(transactor: &AccountID, dest: &AccountID, value: Balance) {
	let from_key = transactor.to_keyed_vec(b"sta:bal:");
	let from_balance = Balance::lookup_default(&from_key);
	assert!(from_balance >= value);
	let to_key = dest.to_keyed_vec(b"sta:bal:");
	let to_balance: Balance = Storable::lookup_default(&to_key);
	assert!(bondage(transactor) <= bondage(dest));
	assert!(to_balance + value > to_balance);	// no overflow
	(from_balance - value).store(&from_key);
	(to_balance + value).store(&to_key);
}

/// Declare the desire to stake for the transactor.
///
/// Effects will be felt at the beginning of the next era.
pub fn stake(transactor: &AccountID) {
	let mut intentions = IntentionStorageVec::items();
	// can't be in the list twice.
	assert!(intentions.iter().find(|t| *t == transactor).is_none());
	intentions.push(transactor.clone());
	IntentionStorageVec::set_items(&intentions);
	u64::max_value().store(&transactor.to_keyed_vec(b"sta:bon:"));
}

/// Retract the desire to stake for the transactor.
///
/// Effects will be felt at the beginning of the next era.
pub fn unstake(transactor: &AccountID) {
	let mut intentions = IntentionStorageVec::items();
	// TODO: use swap remove.
	let intentions = intentions.into_iter().filter(|t| t != transactor).collect::<Vec<_>>();
	IntentionStorageVec::set_items(&intentions);
	(current_era() + bonding_duration()).store(&transactor.to_keyed_vec(b"sta:bon:"));
}

/// Hook to be called after to transaction processing.
pub fn check_new_era() {
	// check block number and call new_era if necessary.
	if (system::block_number() - last_era_length_change()) % era_length() == 0 {
		new_era();
	}
}

// PRIVATE

/// The era has changed - enact new staking set.
///
/// NOTE: This always happens on a session change.
fn new_era() {
	// Increment current era.
	(current_era() + 1).store(b"sta:era");

	// Enact era length change.
	let next_spe: u64 = Storable::lookup_default(b"sta:nse");
	if next_spe > 0 && next_spe != sessions_per_era() {
		next_spe.store(b"sta:spe");
		system::block_number().store(b"sta:lec");
	}

	// TODO: evaluate desired staking amounts and nominations and optimise to find the best
	// combination of validators, then use session::set_validators().

	// for now, this just orders would-be stakers by their balances and chooses the top-most
	// validator_count() of them.
	let mut intentions = IntentionStorageVec::items()
		.into_iter()
		.map(|v| (balance(&v), v))
		.collect::<Vec<_>>();
	intentions.sort_unstable_by(|&(b1, _), &(b2, _)| b2.cmp(&b1));
	session::set_validators(
		&intentions.into_iter()
			.map(|(_, v)| v)
			.take(validator_count())
			.collect::<Vec<_>>()
	);
}

/// Set a new era length. Won't kick in until the next era change (at current length).
fn set_sessions_per_era(new: BlockNumber) {
	new.store(b"sta:nse");
}

#[cfg(test)]
mod tests {
	use runtime_support::{with_externalities, twox_128};
	use keyedvec::KeyedVec;
	use joiner::Joiner;
	use testing::{one, two, TestExternalities};
	use primitives::AccountID;
	use runtime::{staking, session};
	use environment::with_env;

	#[test]
	fn staking_should_work() {
		let one = one();
		let two = two();
		let three = [3u8; 32];
		let four = [4u8; 32];

		let mut t = TestExternalities { storage: map![
			twox_128(b"ses:len").to_vec() => vec![].join(&1u64),
			twox_128(b"ses:val:len").to_vec() => vec![].join(&2u32),
			twox_128(&0u32.to_keyed_vec(b"ses:val:")).to_vec() => vec![10; 32],
			twox_128(&1u32.to_keyed_vec(b"ses:val:")).to_vec() => vec![20; 32],
			twox_128(b"sta:spe").to_vec() => vec![].join(&2u64),
			twox_128(b"sta:vac").to_vec() => vec![].join(&2u32),
			twox_128(b"sta:loc").to_vec() => vec![].join(&3u64),
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![].join(&10u64),
			twox_128(&two.to_keyed_vec(b"sta:bal:")).to_vec() => vec![].join(&20u64),
			twox_128(&three.to_keyed_vec(b"sta:bal:")).to_vec() => vec![].join(&30u64),
			twox_128(&four.to_keyed_vec(b"sta:bal:")).to_vec() => vec![].join(&40u64)
		], };

		with_externalities(&mut t, || {
			assert_eq!(staking::era_length(), 2u64);
			assert_eq!(staking::validator_count(), 2usize);
			assert_eq!(staking::bonding_duration(), 3u64);
			assert_eq!(session::validators(), vec![[10u8; 32], [20u8; 32]]);

			// Block 1: Add three validators. No obvious change.
			with_env(|e| e.block_number = 1);
			staking::stake(&one);
			staking::stake(&two);
			staking::stake(&four);
			staking::check_new_era();
			assert_eq!(session::validators(), vec![[10u8; 32], [20u8; 32]]);

			// Block 2: New validator set now.
			with_env(|e| e.block_number = 2);
			staking::check_new_era();
			assert_eq!(session::validators(), vec![four.clone(), two.clone()]);

			// Block 3: Unstake highest, introduce another staker. No change yet.
			with_env(|e| e.block_number = 3);
			staking::stake(&three);
			staking::unstake(&four);
			staking::check_new_era();

			// Block 4: New era - validators change.
			with_env(|e| e.block_number = 4);
			staking::check_new_era();
			assert_eq!(session::validators(), vec![three.clone(), two.clone()]);

			// Block 5: Transfer stake from highest to lowest. No change yet.
			with_env(|e| e.block_number = 5);
			staking::transfer(&four, &one, 40);
			staking::check_new_era();

			// Block 6: Lowest now validator.
			with_env(|e| e.block_number = 6);
			staking::check_new_era();
			assert_eq!(session::validators(), vec![one.clone(), three.clone()]);

			// Block 7: Unstake three. No change yet.
			with_env(|e| e.block_number = 7);
			staking::unstake(&three);
			staking::check_new_era();
			assert_eq!(session::validators(), vec![one.clone(), three.clone()]);

			// Block 8: Back to one and two.
			with_env(|e| e.block_number = 8);
			staking::check_new_era();
			assert_eq!(session::validators(), vec![one.clone(), two.clone()]);
		});
	}

	#[test]
	fn staking_eras_work() {
		let mut t = TestExternalities { storage: map![
			twox_128(b"ses:len").to_vec() => vec![].join(&1u64),
			twox_128(b"sta:spe").to_vec() => vec![].join(&2u64)
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
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![].join(&42u64)
		], };

		with_externalities(&mut t, || {
			assert_eq!(staking::balance(&one), 42);
			assert_eq!(staking::balance(&two), 0);
		});
	}

	#[test]
	fn staking_balance_transfer_works() {
		let one = one();
		let two = two();

		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![].join(&111u64)
		], };

		with_externalities(&mut t, || {
			staking::transfer(&one, &two, 69);
			assert_eq!(staking::balance(&one), 42);
			assert_eq!(staking::balance(&two), 69);
		});
	}

	#[test]
	#[should_panic]
	fn staking_balance_transfer_when_bonded_doesnt_work() {
		let one = one();
		let two = two();

		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![].join(&111u64)
		], };

		with_externalities(&mut t, || {
			staking::stake(&one);
			staking::transfer(&one, &two, 69);
		});
	}
}
