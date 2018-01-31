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

use runtime_std::prelude::*;
use runtime_std::cell::RefCell;
use codec::KeyedVec;
use support::{storage, StorageVec};
use primitives::{BlockNumber, AccountID};
use runtime::{system, session, governance};

/// The balance of an account.
pub type Balance = u64;

/// The amount of bonding period left in an account. Measured in eras.
pub type Bondage = u64;

struct IntentionStorageVec {}
impl StorageVec for IntentionStorageVec {
	type Item = AccountID;
	const PREFIX: &'static[u8] = b"sta:wil:";
}

const BONDING_DURATION: &[u8] = b"sta:loc";
const VALIDATOR_COUNT: &[u8] = b"sta:vac";
const SESSIONS_PER_ERA: &[u8] = b"sta:spe";
const NEXT_SESSIONS_PER_ERA: &[u8] = b"sta:nse";
const CURRENT_ERA: &[u8] = b"sta:era";
const LAST_ERA_LENGTH_CHANGE: &[u8] = b"sta:lec";
const BALANCE_OF: &[u8] = b"sta:bal:";
const BONDAGE_OF: &[u8] = b"sta:bon:";

/// The length of the bonding duration in eras.
pub fn bonding_duration() -> BlockNumber {
	storage::get_or_default(BONDING_DURATION)
}

/// The length of a staking era in sessions.
pub fn validator_count() -> usize {
	storage::get_or_default::<u32>(VALIDATOR_COUNT) as usize
}

/// The length of a staking era in blocks.
pub fn era_length() -> BlockNumber {
	sessions_per_era() * session::length()
}

/// The length of a staking era in sessions.
pub fn sessions_per_era() -> BlockNumber {
	storage::get_or_default(SESSIONS_PER_ERA)
}

/// The current era index.
pub fn current_era() -> BlockNumber {
	storage::get_or_default(CURRENT_ERA)
}

/// The block number at which the era length last changed.
pub fn last_era_length_change() -> BlockNumber {
	storage::get_or_default(LAST_ERA_LENGTH_CHANGE)
}

/// The balance of a given account.
pub fn balance(who: &AccountID) -> Balance {
	storage::get_or_default(&who.to_keyed_vec(BALANCE_OF))
}

/// The liquidity-state of a given account.
pub fn bondage(who: &AccountID) -> Bondage {
	storage::get_or_default(&who.to_keyed_vec(BONDAGE_OF))
}

// Each identity's stake may be in one of three bondage states, given by an integer:
// - n | n <= current_era(): inactive: free to be transferred.
// - ~0: active: currently representing a validator.
// - n | n > current_era(): deactivating: recently representing a validator and not yet
//   ready for transfer.

pub mod public {
	use super::*;

	/// Transfer some unlocked staking balance to another staker.
	pub fn transfer(transactor: &AccountID, dest: &AccountID, value: Balance) {
		let from_key = transactor.to_keyed_vec(BALANCE_OF);
		let from_balance = storage::get_or_default::<Balance>(&from_key);
		assert!(from_balance >= value);
		let to_key = dest.to_keyed_vec(BALANCE_OF);
		let to_balance: Balance = storage::get_or_default(&to_key);
		assert!(bondage(transactor) <= bondage(dest));
		assert!(to_balance + value > to_balance);	// no overflow
		storage::put(&from_key, &(from_balance - value));
		storage::put(&to_key, &(to_balance + value));
	}

	/// Declare the desire to stake for the transactor.
	///
	/// Effects will be felt at the beginning of the next era.
	pub fn stake(transactor: &AccountID) {
		let mut intentions = IntentionStorageVec::items();
		// can't be in the list twice.
		assert!(intentions.iter().find(|t| *t == transactor).is_none(), "Cannot stake if already staked.");
		intentions.push(transactor.clone());
		IntentionStorageVec::set_items(&intentions);
		storage::put(&transactor.to_keyed_vec(BONDAGE_OF), &u64::max_value());
	}

	/// Retract the desire to stake for the transactor.
	///
	/// Effects will be felt at the beginning of the next era.
	pub fn unstake(transactor: &AccountID) {
		let mut intentions = IntentionStorageVec::items();
		if let Some(position) = intentions.iter().position(|t| t == transactor) {
			intentions.swap_remove(position);
		} else {
			panic!("Cannot unstake if not already staked.");
		}
		IntentionStorageVec::set_items(&intentions);
		storage::put(&transactor.to_keyed_vec(BONDAGE_OF), &(current_era() + bonding_duration()));
	}
}

pub mod privileged {
	use super::*;

	/// Set the number of sessions in an era.
	pub fn set_sessions_per_era(new: BlockNumber) {
		storage::put(NEXT_SESSIONS_PER_ERA, &new);
	}

	/// The length of the bonding duration in eras.
	pub fn set_bonding_duration(new: BlockNumber) {
		storage::put(BONDING_DURATION, &new);
	}

	/// The length of a staking era in sessions.
	pub fn set_validator_count(new: usize) {
		storage::put(VALIDATOR_COUNT, &(new as u32));
	}
}

pub mod internal {
	use super::*;

	/// Hook to be called after to transaction processing.
	pub fn check_new_era() {
		// check block number and call new_era if necessary.
		if (system::block_number() - last_era_length_change()) % era_length() == 0 {
			new_era();
		}
	}
}

/// The era has changed - enact new staking set.
///
/// NOTE: This always happens immediately before a session change to ensure that new validators
/// get a chance to set their session keys.
fn new_era() {
	// Inform governance module that it's the end of an era
	governance::internal::end_of_an_era();

	// Increment current era.
	storage::put(CURRENT_ERA, &(current_era() + 1));

	// Enact era length change.
	let next_spe: u64 = storage::get_or_default(NEXT_SESSIONS_PER_ERA);
	if next_spe > 0 && next_spe != sessions_per_era() {
		storage::put(SESSIONS_PER_ERA, &next_spe);
		storage::put(LAST_ERA_LENGTH_CHANGE, &system::block_number());
	}

	// evaluate desired staking amounts and nominations and optimise to find the best
	// combination of validators, then use session::internal::set_validators().
	// for now, this just orders would-be stakers by their balances and chooses the top-most
	// validator_count() of them.
	let mut intentions = IntentionStorageVec::items()
		.into_iter()
		.map(|v| (balance(&v), v))
		.collect::<Vec<_>>();
	intentions.sort_unstable_by(|&(b1, _), &(b2, _)| b2.cmp(&b1));
	session::internal::set_validators(
		&intentions.into_iter()
			.map(|(_, v)| v)
			.take(validator_count())
			.collect::<Vec<_>>()
	);
}

#[cfg(test)]
mod tests {
	use super::*;
	use super::internal::*;
	use super::public::*;
	use super::privileged::*;

	use runtime_std::{with_externalities, twox_128, TestExternalities};
	use codec::{KeyedVec, Joiner};
	use support::{one, two, with_env};
	use primitives::AccountID;
	use runtime::{staking, session};

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
			twox_128(SESSIONS_PER_ERA).to_vec() => vec![].join(&2u64),
			twox_128(VALIDATOR_COUNT).to_vec() => vec![].join(&2u32),
			twox_128(BONDING_DURATION).to_vec() => vec![].join(&3u64),
			twox_128(&one.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].join(&10u64),
			twox_128(&two.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].join(&20u64),
			twox_128(&three.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].join(&30u64),
			twox_128(&four.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].join(&40u64)
		], };

		with_externalities(&mut t, || {
			assert_eq!(era_length(), 2u64);
			assert_eq!(validator_count(), 2usize);
			assert_eq!(bonding_duration(), 3u64);
			assert_eq!(session::validators(), vec![[10u8; 32], [20u8; 32]]);

			// Block 1: Add three validators. No obvious change.
			with_env(|e| e.block_number = 1);
			stake(&one);
			stake(&two);
			stake(&four);
			check_new_era();
			assert_eq!(session::validators(), vec![[10u8; 32], [20u8; 32]]);

			// Block 2: New validator set now.
			with_env(|e| e.block_number = 2);
			check_new_era();
			assert_eq!(session::validators(), vec![four.clone(), two.clone()]);

			// Block 3: Unstake highest, introduce another staker. No change yet.
			with_env(|e| e.block_number = 3);
			stake(&three);
			unstake(&four);
			check_new_era();

			// Block 4: New era - validators change.
			with_env(|e| e.block_number = 4);
			check_new_era();
			assert_eq!(session::validators(), vec![three.clone(), two.clone()]);

			// Block 5: Transfer stake from highest to lowest. No change yet.
			with_env(|e| e.block_number = 5);
			transfer(&four, &one, 40);
			check_new_era();

			// Block 6: Lowest now validator.
			with_env(|e| e.block_number = 6);
			check_new_era();
			assert_eq!(session::validators(), vec![one.clone(), three.clone()]);

			// Block 7: Unstake three. No change yet.
			with_env(|e| e.block_number = 7);
			unstake(&three);
			check_new_era();
			assert_eq!(session::validators(), vec![one.clone(), three.clone()]);

			// Block 8: Back to one and two.
			with_env(|e| e.block_number = 8);
			check_new_era();
			assert_eq!(session::validators(), vec![one.clone(), two.clone()]);
		});
	}

	#[test]
	fn staking_eras_work() {
		let mut t = TestExternalities { storage: map![
			twox_128(b"ses:len").to_vec() => vec![].join(&1u64),
			twox_128(SESSIONS_PER_ERA).to_vec() => vec![].join(&2u64)
		], };
		with_externalities(&mut t, || {
			assert_eq!(era_length(), 2u64);
			assert_eq!(sessions_per_era(), 2u64);
			assert_eq!(last_era_length_change(), 0u64);
			assert_eq!(current_era(), 0u64);

			// Block 1: No change.
			with_env(|e| e.block_number = 1);
			check_new_era();
			assert_eq!(sessions_per_era(), 2u64);
			assert_eq!(last_era_length_change(), 0u64);
			assert_eq!(current_era(), 0u64);

			// Block 2: Simple era change.
			with_env(|e| e.block_number = 2);
			check_new_era();
			assert_eq!(sessions_per_era(), 2u64);
			assert_eq!(last_era_length_change(), 0u64);
			assert_eq!(current_era(), 1u64);

			// Block 3: Schedule an era length change; no visible changes.
			with_env(|e| e.block_number = 3);
			set_sessions_per_era(3);
			check_new_era();
			assert_eq!(sessions_per_era(), 2u64);
			assert_eq!(last_era_length_change(), 0u64);
			assert_eq!(current_era(), 1u64);

			// Block 4: Era change kicks in.
			with_env(|e| e.block_number = 4);
			check_new_era();
			assert_eq!(sessions_per_era(), 3u64);
			assert_eq!(last_era_length_change(), 4u64);
			assert_eq!(current_era(), 2u64);

			// Block 5: No change.
			with_env(|e| e.block_number = 5);
			check_new_era();
			assert_eq!(sessions_per_era(), 3u64);
			assert_eq!(last_era_length_change(), 4u64);
			assert_eq!(current_era(), 2u64);

			// Block 6: No change.
			with_env(|e| e.block_number = 6);
			check_new_era();
			assert_eq!(sessions_per_era(), 3u64);
			assert_eq!(last_era_length_change(), 4u64);
			assert_eq!(current_era(), 2u64);

			// Block 7: Era increment.
			with_env(|e| e.block_number = 7);
			check_new_era();
			assert_eq!(sessions_per_era(), 3u64);
			assert_eq!(last_era_length_change(), 4u64);
			assert_eq!(current_era(), 3u64);
		});
	}

	#[test]
	fn staking_balance_works() {
		let one = one();
		let two = two();

		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].join(&42u64)
		], };

		with_externalities(&mut t, || {
			assert_eq!(balance(&one), 42);
			assert_eq!(balance(&two), 0);
		});
	}

	#[test]
	fn staking_balance_transfer_works() {
		let one = one();
		let two = two();

		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].join(&111u64)
		], };

		with_externalities(&mut t, || {
			transfer(&one, &two, 69);
			assert_eq!(balance(&one), 42);
			assert_eq!(balance(&two), 69);
		});
	}

	#[test]
	#[should_panic]
	fn staking_balance_transfer_when_bonded_doesnt_work() {
		let one = one();
		let two = two();

		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].join(&111u64)
		], };

		with_externalities(&mut t, || {
			stake(&one);
			transfer(&one, &two, 69);
		});
	}
}
