// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Staking manager: Handles balances and periodically determines the best set of validators.

use rstd::prelude::*;
use rstd::cell::RefCell;
use rstd::collections::btree_map::{BTreeMap, Entry};
use runtime_io::{print, blake2_256};
use codec::KeyedVec;
use runtime_support::{storage, StorageVec};
use demo_primitives::{BlockNumber, AccountId};
use runtime::{system, session, governance};

/// The balance of an account.
pub type Balance = u64;

/// The amount of bonding period left in an account. Measured in eras.
pub type Bondage = u64;

struct IntentionStorageVec {}
impl StorageVec for IntentionStorageVec {
	type Item = AccountId;
	const PREFIX: &'static[u8] = b"sta:wil:";
}

const BONDING_DURATION: &[u8] = b"sta:loc";
const VALIDATOR_COUNT: &[u8] = b"sta:vac";
const SESSIONS_PER_ERA: &[u8] = b"sta:spe";
const NEXT_SESSIONS_PER_ERA: &[u8] = b"sta:nse";
const CURRENT_ERA: &[u8] = b"sta:era";
const LAST_ERA_LENGTH_CHANGE: &[u8] = b"sta:lec";
const TOTAL_STAKE: &[u8] = b"sta:tot";

const BALANCE_OF: &[u8] = b"sta:bal:";
const BONDAGE_OF: &[u8] = b"sta:bon:";
const CODE_OF: &[u8] = b"sta:cod:";
const STORAGE_OF: &[u8] = b"sta:sto:";

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
pub fn balance(who: &AccountId) -> Balance {
	storage::get_or_default(&who.to_keyed_vec(BALANCE_OF))
}

/// The liquidity-state of a given account.
pub fn bondage(who: &AccountId) -> Bondage {
	storage::get_or_default(&who.to_keyed_vec(BONDAGE_OF))
}

/// The total amount of stake on the system.
pub fn total_stake() -> Balance {
	storage::get_or(TOTAL_STAKE, 0)
}

// Each identity's stake may be in one of three bondage states, given by an integer:
// - n | n <= current_era(): inactive: free to be transferred.
// - ~0: active: currently representing a validator.
// - n | n > current_era(): deactivating: recently representing a validator and not yet
//   ready for transfer.

pub mod public {
	use super::*;

	type State = BTreeMap<AccountId, (Option<Balance>, Option<Vec<u8>>, BTreeMap<Vec<u8>, Option<Vec<u8>>>)>;

	trait Externalities {
		fn get_storage(&self, account: &AccountId, location: &[u8]) -> Option<Vec<u8>>;
		fn get_code(&self, account: &AccountId) -> Vec<u8>;
		fn get_balance(&self, account: &AccountId) -> Balance;
	}

	struct Ext<F1, F3, F5> where
		F1 : Fn(&AccountId, &[u8]) -> Option<Vec<u8>>,
		F3 : Fn(&AccountId) -> Vec<u8>,
		F5 : Fn(&AccountId) -> Balance
	{
		do_get_storage: F1,
		do_get_code: F3,
		do_get_balance: F5,
	}

	struct DirectExt;
	impl Externalities for DirectExt {
		fn get_storage(&self, account: &AccountId, location: &[u8]) -> Option<Vec<u8>> {
			let mut v = account.to_keyed_vec(STORAGE_OF);
			v.extend(location);
			storage::get_raw(&v)
		}
		fn get_code(&self, account: &AccountId) -> Vec<u8> {
			storage::get_raw(&account.to_keyed_vec(CODE_OF)).unwrap_or_default()
		}
		fn get_balance(&self, account: &AccountId) -> Balance {
			storage::get_or_default::<Balance>(&account.to_keyed_vec(BALANCE_OF))
		}
	}

	impl<F1, F3, F5> Externalities for Ext<F1, F3, F5> where
		F1 : Fn(&AccountId, &[u8]) -> Option<Vec<u8>>,
		F3 : Fn(&AccountId) -> Vec<u8>,
		F5 : Fn(&AccountId) -> Balance
	{
		fn get_storage(&self, account: &AccountId, location: &[u8]) -> Option<Vec<u8>> {
			(self.do_get_storage)(account, location)
		}
		fn get_code(&self, account: &AccountId) -> Vec<u8> {
			(self.do_get_code)(account)
		}
		fn get_balance(&self, account: &AccountId) -> Balance {
			(self.do_get_balance)(account)
		}
	}

	fn commit_state(s: State) {
		for (address, (maybe_balance, maybe_code, storage)) in s.into_iter() {
			if let Some(balance) = maybe_balance {
				storage::put(&address.to_keyed_vec(BALANCE_OF), &balance);
			}
			if let Some(code) = maybe_code {
				storage::put(&address.to_keyed_vec(CODE_OF), &code);
			}
			let storage_key = address.to_keyed_vec(STORAGE_OF);
			for (k, v) in storage.into_iter() {
				let mut key = storage_key.clone();
				key.extend(k);
				if let Some(value) = v {
					storage::put_raw(&key, &value);
				} else {
					storage::kill(&key);
				}
			}
		}
	}

	fn merge_state(commit_state: State, local: &mut State) {
		for (address, (maybe_balance, maybe_code, storage)) in commit_state.into_iter() {
			match local.entry(address) {
				Entry::Occupied(e) => {
					let mut value = e.into_mut();
					if maybe_balance.is_some() {
						value.0 = maybe_balance;
					}
					if maybe_code.is_some() {
						value.1 = maybe_code;
					}
					value.2.extend(storage.into_iter());
				}
				Entry::Vacant(e) => {
					e.insert((maybe_balance, maybe_code, storage));
				}
			}
		}
	}

	/// Create a smart-contract account.
	pub fn create(transactor: &AccountId, code: &[u8], value: Balance) {
		// commit anything that made it this far to storage
		if let Some(commit) = effect_create(transactor, code, value, DirectExt) {
			commit_state(commit);
		}
	}

	fn effect_create<E: Externalities>(
		transactor: &AccountId,
		code: &[u8],
		value: Balance,
		ext: E
	) -> Option<State> {
		let from_balance = ext.get_balance(transactor);
		// TODO: a fee.
		assert!(from_balance >= value);

		let mut dest_pre = blake2_256(code).to_vec();
		dest_pre.extend(&transactor[..]);
		let dest = blake2_256(&dest_pre);

		// early-out if degenerate.
		if &dest == transactor {
			return None;
		}

		let mut local = BTreeMap::new();

		// two inserts are safe
		assert!(&dest != transactor);
		local.insert(dest, (Some(value), Some(code.to_vec()), Default::default()));
		local.insert(transactor.clone(), (Some(from_balance - value), None, Default::default()));

		Some(local)
	}

	/// Transfer some unlocked staking balance to another staker.
	/// TODO: probably want to state gas-limit and gas-price.
	pub fn transfer(transactor: &AccountId, dest: &AccountId, value: Balance) {
		// commit anything that made it this far to storage
		if let Some(commit) = effect_transfer(transactor, dest, value, DirectExt) {
			commit_state(commit);
		}
	}

	fn effect_transfer<E: Externalities>(
		transactor: &AccountId,
		dest: &AccountId,
		value: Balance,
		ext: E
	) -> Option<State> {
		let from_balance = ext.get_balance(transactor);
		assert!(from_balance >= value);

		let to_balance = ext.get_balance(dest);
		assert!(bondage(transactor) <= bondage(dest));
		assert!(to_balance + value > to_balance);	// no overflow

		// TODO: a fee, based upon gaslimit/gasprice.
		// TODO: consider storing upper-bound for contract's gas limit in fixed-length runtime
		// code in contract itself and use that.

		let local: RefCell<State> = RefCell::new(BTreeMap::new());

		if transactor != dest {
			let mut local = local.borrow_mut();
			local.insert(transactor.clone(), (Some(from_balance - value), None, Default::default()));
			local.insert(dest.clone(), (Some(to_balance + value), None, Default::default()));
		}

		let should_commit = {
			// Our local ext: Should be used for any transfers and creates that happen internally.
			let ext = || Ext {
				do_get_storage: |account: &AccountId, location: &[u8]|
					local.borrow().get(account)
						.and_then(|a| a.2.get(location))
						.cloned()
						.unwrap_or_else(|| ext.get_storage(account, location)),
				do_get_code: |account: &AccountId|
					local.borrow().get(account)
						.and_then(|a| a.1.clone())
						.unwrap_or_else(|| ext.get_code(account)),
				do_get_balance: |account: &AccountId|
					local.borrow().get(account)
						.and_then(|a| a.0)
						.unwrap_or_else(|| ext.get_balance(account)),
			};
			let mut transfer = |inner_dest: &AccountId, value: Balance| {
				if let Some(commit_state) = effect_transfer(dest, inner_dest, value, ext()) {
					merge_state(commit_state, &mut *local.borrow_mut());
				}
			};
			let mut create = |code: &[u8], value: Balance| {
				if let Some(commit_state) = effect_create(dest, code, value, ext()) {
					merge_state(commit_state, &mut *local.borrow_mut());
				}
			};
			let mut put_storage = |location: Vec<u8>, value: Option<Vec<u8>>| {
				local.borrow_mut()
					.entry(dest.clone())
					.or_insert((None, None, Default::default()))
					.2.insert(location, value);
			};

			// TODO: logging (logs are just appended into a notable storage-based vector and cleared every
			// block).
			// TODO: execute code with ext(), put_storage, create and transfer as externalities.
			true
		};

		if should_commit {
			Some(local.into_inner())
		} else {
			None
		}
	}

	/// Declare the desire to stake for the transactor.
	///
	/// Effects will be felt at the beginning of the next era.
	pub fn stake(transactor: &AccountId) {
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
	pub fn unstake(transactor: &AccountId) {
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
	pub fn set_validator_count(new: u32) {
		storage::put(VALIDATOR_COUNT, &new);
	}

	/// Force there to be a new era. This also forces a new session immediately after.
	pub fn force_new_era() {
		new_era();
		session::privileged::force_new_session();
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

	use runtime_io::{with_externalities, twox_128, TestExternalities};
	use codec::{KeyedVec, Joiner};
	use keyring::Keyring;
	use environment::with_env;
	use demo_primitives::AccountId;
	use runtime::{staking, session};

	#[test]
	fn staking_should_work() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();
		let three = [3u8; 32];
		let four = [4u8; 32];

		let mut t: TestExternalities = map![
			twox_128(b"ses:len").to_vec() => vec![].and(&1u64),
			twox_128(b"ses:val:len").to_vec() => vec![].and(&2u32),
			twox_128(&0u32.to_keyed_vec(b"ses:val:")).to_vec() => vec![10; 32],
			twox_128(&1u32.to_keyed_vec(b"ses:val:")).to_vec() => vec![20; 32],
			twox_128(SESSIONS_PER_ERA).to_vec() => vec![].and(&2u64),
			twox_128(VALIDATOR_COUNT).to_vec() => vec![].and(&2u32),
			twox_128(BONDING_DURATION).to_vec() => vec![].and(&3u64),
			twox_128(TOTAL_STAKE).to_vec() => vec![].and(&100u64),
			twox_128(&one.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&10u64),
			twox_128(&two.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&20u64),
			twox_128(&three.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&30u64),
			twox_128(&four.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&40u64)
		];

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
		let mut t: TestExternalities = map![
			twox_128(b"ses:len").to_vec() => vec![].and(&1u64),
			twox_128(SESSIONS_PER_ERA).to_vec() => vec![].and(&2u64)
		];
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
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();

		let mut t: TestExternalities = map![
			twox_128(&one.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&42u64)
		];

		with_externalities(&mut t, || {
			assert_eq!(balance(&one), 42);
			assert_eq!(balance(&two), 0);
		});
	}

	#[test]
	fn staking_balance_transfer_works() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();

		let mut t: TestExternalities = map![
			twox_128(&one.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&111u64)
		];

		with_externalities(&mut t, || {
			transfer(&one, &two, 69);
			assert_eq!(balance(&one), 42);
			assert_eq!(balance(&two), 69);
		});
	}

	#[test]
	#[should_panic]
	fn staking_balance_transfer_when_bonded_doesnt_work() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();

		let mut t: TestExternalities = map![
			twox_128(&one.to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&111u64)
		];

		with_externalities(&mut t, || {
			stake(&one);
			transfer(&one, &two, 69);
		});
	}
}
