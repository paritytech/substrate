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
use rstd::{ops, cmp};
use rstd::cell::RefCell;
use rstd::collections::btree_map::{BTreeMap, Entry};
use runtime_io::{print, blake2_256};
use codec::{Slicable, Input, KeyedVec};
use runtime_support::{storage, StorageVec};
use demo_primitives::{BlockNumber, AccountId};
use runtime::{system, session, democracy};

/// The balance of an account.
pub type Balance = u64;

/// The amount of bonding period left in an account. Measured in eras.
pub type Bondage = u64;

pub const BONDING_DURATION: &[u8] = b"sta:loc";
pub const VALIDATOR_COUNT: &[u8] = b"sta:vac";
pub const SESSIONS_PER_ERA: &[u8] = b"sta:spe";
pub const NEXT_SESSIONS_PER_ERA: &[u8] = b"sta:nse";
pub const CURRENT_ERA: &[u8] = b"sta:era";
pub const LAST_ERA_LENGTH_CHANGE: &[u8] = b"sta:lec";
pub const TOTAL_STAKE: &[u8] = b"sta:tot";
pub const INTENTION_AT: &[u8] = b"sta:wil:";
pub const INTENTION_COUNT: &[u8] = b"sta:wil:len";
pub const TRANSACTION_FEE: &[u8] = b"sta:fee";

pub const BALANCE_OF: &[u8] = b"sta:bal:";
pub const RESERVED_BALANCE_OF: &[u8] = b"sta:lbo:";
pub const BONDAGE_OF: &[u8] = b"sta:bon:";
pub const CODE_OF: &[u8] = b"sta:cod:";
pub const STORAGE_OF: &[u8] = b"sta:sto:";

pub struct IntentionStorageVec {}
impl StorageVec for IntentionStorageVec {
	type Item = AccountId;
	const PREFIX: &'static[u8] = INTENTION_AT;
}

/// The fee to be paid for making a transaction.
pub fn transaction_fee() -> Balance {
	storage::get(TRANSACTION_FEE).expect("All basic parameters should be defined")
}

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
	free_balance(who) + reserved_balance(who)
}

/// The balance of a given account.
pub fn free_balance(who: &AccountId) -> Balance {
	storage::get_or_default(&who.to_keyed_vec(BALANCE_OF))
}

/// The amount of the balance of a given account that is exterally reserved; this can still get
/// slashed, but gets slashed last of all.
pub fn reserved_balance(who: &AccountId) -> Balance {
	storage::get_or_default(&who.to_keyed_vec(RESERVED_BALANCE_OF))
}

/// Some result as `slash(who, value)` (but without the side-effects) asuming there are no
/// balance changes in the meantime.
pub fn can_slash(who: &AccountId, value: Balance) -> bool {
	balance(who) >= value
}

/// The block at which the `who`'s funds become entirely liquid.
pub fn bondage(who: &AccountId) -> Bondage {
	storage::get_or_default(&who.to_keyed_vec(BONDAGE_OF))
}

#[derive(PartialEq, Copy, Clone)]
#[cfg_attr(test, derive(Debug))]
pub enum LockStatus {
	Liquid,
	LockedUntil(BlockNumber),
	Staked,
}

/// The block at which the `who`'s funds become entirely liquid.
pub fn unlock_block(who: &AccountId) -> LockStatus {
	match bondage(who) {
		i if i == Bondage::max_value() => LockStatus::Staked,
		i if i <= system::block_number() => LockStatus::Liquid,
		i => LockStatus::LockedUntil(i),
	}
}

/// The total amount of stake on the system.
pub fn total_stake() -> Balance {
	storage::get_or(TOTAL_STAKE, 0)
}

pub struct PublicPass<'a> (&'a AccountId);

const NOBODY: AccountId = [0u8; 32];

impl<'a> PublicPass<'a> {
	pub fn new(transactor: &AccountId) -> PublicPass {
		let b = free_balance(&transactor);
		let transaction_fee = transaction_fee();
		assert!(b >= transaction_fee, "attempt to transact without enough funds to pay fee");
		internal::set_free_balance(&transactor, b - transaction_fee);
		PublicPass(transactor)
	}

	#[cfg(test)]
	pub fn test(signed: &AccountId) -> PublicPass {
		PublicPass(signed)
	}

	#[cfg(test)]
	pub fn nobody() -> PublicPass<'static> {
		PublicPass(&NOBODY)
	}

	/// Create a smart-contract account.
	pub fn create(self, code: &[u8], value: Balance) {
		// commit anything that made it this far to storage
		if let Some(commit) = private::effect_create(self.0, code, value, private::DirectExt) {
			private::commit_state(commit);
		}
	}
}

impl<'a> ops::Deref for PublicPass<'a> {
	type Target = AccountId;
	fn deref(&self) -> &AccountId {
		self.0
	}
}

impl_dispatch! {
	pub mod public;
	fn transfer(dest: AccountId, value: Balance) = 0;
	fn stake() = 1;
	fn unstake() = 2;
}

impl<'a> public::Dispatch for PublicPass<'a> {
	/// Transfer some unlocked staking balance to another staker.
	/// TODO: probably want to state gas-limit and gas-price.
	fn transfer(self, dest: AccountId, value: Balance) {
		// commit anything that made it this far to storage
		if let Some(commit) = private::effect_transfer(&self, &dest, value, private::DirectExt) {
			private::commit_state(commit);
		}
	}

	/// Declare the desire to stake for the transactor.
	///
	/// Effects will be felt at the beginning of the next era.
	fn stake(self) {
		let mut intentions = IntentionStorageVec::items();
		// can't be in the list twice.
		assert!(intentions.iter().find(|&t| *t == *self).is_none(), "Cannot stake if already staked.");
		intentions.push(self.clone());
		IntentionStorageVec::set_items(&intentions);
		storage::put(&self.to_keyed_vec(BONDAGE_OF), &u64::max_value());
	}

	/// Retract the desire to stake for the transactor.
	///
	/// Effects will be felt at the beginning of the next era.
	fn unstake(self) {
		let mut intentions = IntentionStorageVec::items();
		if let Some(position) = intentions.iter().position(|&t| t == *self) {
			intentions.swap_remove(position);
		} else {
			panic!("Cannot unstake if not already staked.");
		}
		IntentionStorageVec::set_items(&intentions);
		storage::put(&self.to_keyed_vec(BONDAGE_OF), &(current_era() + bonding_duration()));
	}
}

impl_dispatch! {
	pub mod privileged;
	fn set_sessions_per_era(new: BlockNumber) = 0;
	fn set_bonding_duration(new: BlockNumber) = 1;
	fn set_validator_count(new: u32) = 2;
	fn force_new_era() = 3;
}

impl privileged::Dispatch for democracy::PrivPass {
	/// Set the number of sessions in an era.
	fn set_sessions_per_era(self, new: BlockNumber) {
		storage::put(NEXT_SESSIONS_PER_ERA, &new);
	}

	/// The length of the bonding duration in eras.
	fn set_bonding_duration(self, new: BlockNumber) {
		storage::put(BONDING_DURATION, &new);
	}

	/// The length of a staking era in sessions.
	fn set_validator_count(self, new: u32) {
		storage::put(VALIDATOR_COUNT, &new);
	}

	/// Force there to be a new era. This also forces a new session immediately after.
	fn force_new_era(self) {
		new_era();
		session::internal::rotate_session();
	}
}

// Each identity's stake may be in one of three bondage states, given by an integer:
// - n | n <= current_era(): inactive: free to be transferred.
// - ~0: active: currently representing a validator.
// - n | n > current_era(): deactivating: recently representing a validator and not yet
//   ready for transfer.

mod private {
	use super::*;

	#[derive(Default)]
	pub struct ChangeEntry {
		balance: Option<Balance>,
		code: Option<Vec<u8>>,
		storage: BTreeMap<Vec<u8>, Option<Vec<u8>>>,
	}

	impl ChangeEntry {
		pub fn balance_changed(b: Balance) -> Self {
			ChangeEntry { balance: Some(b), code: None, storage: Default::default() }
		}
	}

	type State = BTreeMap<AccountId, ChangeEntry>;

	pub trait Externalities {
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

	pub struct DirectExt;
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

	pub fn commit_state(s: State) {
		for (address, changed) in s.into_iter() {
			if let Some(balance) = changed.balance {
				storage::put(&address.to_keyed_vec(BALANCE_OF), &balance);
			}
			if let Some(code) = changed.code {
				storage::put(&address.to_keyed_vec(CODE_OF), &code);
			}
			let storage_key = address.to_keyed_vec(STORAGE_OF);
			for (k, v) in changed.storage.into_iter() {
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
		for (address, changed) in commit_state.into_iter() {
			match local.entry(address) {
				Entry::Occupied(e) => {
					let mut value = e.into_mut();
					if changed.balance.is_some() {
						value.balance = changed.balance;
					}
					if changed.code.is_some() {
						value.code = changed.code;
					}
					value.storage.extend(changed.storage.into_iter());
				}
				Entry::Vacant(e) => {
					e.insert(changed);
				}
			}
		}
	}

	pub fn effect_create<E: Externalities>(
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
		local.insert(dest, ChangeEntry { balance: Some(value), code: Some(code.to_vec()), storage: Default::default() });
		local.insert(transactor.clone(), ChangeEntry::balance_changed(from_balance - value));

		Some(local)
	}

	pub fn effect_transfer<E: Externalities>(
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
			local.insert(transactor.clone(), ChangeEntry::balance_changed(from_balance - value));
			local.insert(dest.clone(), ChangeEntry::balance_changed(to_balance + value));
		}

		let should_commit = {
			// Our local ext: Should be used for any transfers and creates that happen internally.
			let ext = || Ext {
				do_get_storage: |account: &AccountId, location: &[u8]|
					local.borrow().get(account)
						.and_then(|a| a.storage.get(location))
						.cloned()
						.unwrap_or_else(|| ext.get_storage(account, location)),
				do_get_code: |account: &AccountId|
					local.borrow().get(account)
						.and_then(|a| a.code.clone())
						.unwrap_or_else(|| ext.get_code(account)),
				do_get_balance: |account: &AccountId|
					local.borrow().get(account)
						.and_then(|a| a.balance)
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
					.or_insert(Default::default())
					.storage.insert(location, value);
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
}

pub mod internal {
	use super::*;

	/// Set the balance of an account.
	/// Needless to say, this is super low-level and accordingly dangerous. Ensure any modules that
	/// use it are auditted to the hilt.
	pub fn set_free_balance(who: &AccountId, value: Balance) {
		storage::put(&who.to_keyed_vec(BALANCE_OF), &value);
	}

	/// Hook to be called after to transaction processing.
	pub fn check_new_era() {
		// check block number and call new_era if necessary.
		if (system::block_number() - last_era_length_change()) % era_length() == 0 {
			new_era();
		}
	}

	/// Deduct from an unbonded balance. true if it happened.
	pub fn deduct_unbonded(who: &AccountId, value: Balance) -> bool {
		if let LockStatus::Liquid = unlock_block(who) {
			let b = free_balance(who);
			if b >= value {
				set_free_balance(who, b - value);
				return true;
			}
		}
		false
	}

	/// Refund some balance.
	pub fn refund(who: &AccountId, value: Balance) {
		set_free_balance(who, free_balance(who) + value)
	}

	/// Will slash any balance, but prefer free over reserved.
	pub fn slash(who: &AccountId, value: Balance) -> bool {
		let free_balance = free_balance(who);
		let free_slash = cmp::min(free_balance, value);
		set_free_balance(who, free_balance - free_slash);
		if free_slash < value {
			slash_reserved(who, value - free_slash)
		} else {
			true
		}
	}

	/// Moves `value` from balance to reserved balance.
	pub fn reserve_balance(who: &AccountId, value: Balance) {
		let b = free_balance(who);
		assert!(b >= value);
		set_free_balance(who, b - value);
		set_reserved_balance(who, reserved_balance(who) + value);
	}

	/// Moves `value` from reserved balance to balance.
	pub fn unreserve_balance(who: &AccountId, value: Balance) {
		let b = reserved_balance(who);
		let value = cmp::min(b, value);
		set_reserved_balance(who, b - value);
		set_free_balance(who, free_balance(who) + value);
	}

	/// Moves `value` from reserved balance to balance.
	pub fn slash_reserved(who: &AccountId, value: Balance) -> bool {
		let b = reserved_balance(who);
		let slash = cmp::min(b, value);
		set_reserved_balance(who, b - slash);
		value == slash
	}

	/// Moves `value` from reserved balance to balance.
	pub fn transfer_reserved_balance(slashed: &AccountId, beneficiary: &AccountId, value: Balance) -> bool {
		let b = reserved_balance(slashed);
		let slash = cmp::min(b, value);
		set_reserved_balance(slashed, b - slash);
		set_free_balance(beneficiary, free_balance(beneficiary) + slash);
		slash == value
	}
}

/// Set the reserved portion of `who`'s balance.
fn set_reserved_balance(who: &AccountId, value: Balance) {
	storage::put(&who.to_keyed_vec(RESERVED_BALANCE_OF), &value);
}

/// The era has changed - enact new staking set.
///
/// NOTE: This always happens immediately before a session change to ensure that new validators
/// get a chance to set their session keys.
fn new_era() {
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

#[cfg(any(feature = "std", test))]
pub mod testing {
	use super::*;
	use runtime_io::{twox_128, TestExternalities};
	use codec::{Joiner, KeyedVec};
	use keyring::Keyring::*;
	use runtime::session;
	use super::public::{Call, Dispatch};
	use super::privileged::{Dispatch as PrivDispatch, Call as PrivCall};

	pub fn externalities(session_length: u64, sessions_per_era: u64, current_era: u64) -> TestExternalities {
		let extras: TestExternalities = map![
			twox_128(INTENTION_COUNT).to_vec() => vec![].and(&3u32),
			twox_128(&0u32.to_keyed_vec(INTENTION_AT)).to_vec() => Alice.to_raw_public_vec(),
			twox_128(&1u32.to_keyed_vec(INTENTION_AT)).to_vec() => Bob.to_raw_public_vec(),
			twox_128(&2u32.to_keyed_vec(INTENTION_AT)).to_vec() => Charlie.to_raw_public_vec(),
			twox_128(SESSIONS_PER_ERA).to_vec() => vec![].and(&sessions_per_era),
			twox_128(VALIDATOR_COUNT).to_vec() => vec![].and(&3u64),
			twox_128(TRANSACTION_FEE).to_vec() => vec![].and(&1u64),
			twox_128(CURRENT_ERA).to_vec() => vec![].and(&current_era),
			twox_128(&Alice.to_raw_public().to_keyed_vec(BALANCE_OF)).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		];
		session::testing::externalities(session_length).into_iter().chain(extras.into_iter()).collect()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use super::internal::*;
	use super::privileged::*;

	use runtime_io::{with_externalities, twox_128, TestExternalities};
	use codec::{KeyedVec, Joiner};
	use keyring::Keyring::*;
	use environment::with_env;
	use demo_primitives::AccountId;
	use runtime::{staking, session};
	use runtime::democracy::PrivPass;
	use runtime::staking::public::{Call, Dispatch};
	use runtime::staking::privileged::{Call as PCall, Dispatch as PDispatch};

	#[test]
	fn staking_should_work() {
		let mut t: TestExternalities = map![
			twox_128(session::SESSION_LENGTH).to_vec() => vec![].and(&1u64),
			twox_128(session::VALIDATOR_COUNT).to_vec() => vec![].and(&2u32),
			twox_128(&0u32.to_keyed_vec(session::VALIDATOR_AT)).to_vec() => vec![10; 32],
			twox_128(&1u32.to_keyed_vec(session::VALIDATOR_AT)).to_vec() => vec![20; 32],
			twox_128(SESSIONS_PER_ERA).to_vec() => vec![].and(&2u64),
			twox_128(VALIDATOR_COUNT).to_vec() => vec![].and(&2u32),
			twox_128(BONDING_DURATION).to_vec() => vec![].and(&3u64),
			twox_128(TOTAL_STAKE).to_vec() => vec![].and(&100u64),
			twox_128(TRANSACTION_FEE).to_vec() => vec![].and(&0u64),
			twox_128(&Alice.to_raw_public().to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&10u64),
			twox_128(&Bob.to_raw_public().to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&20u64),
			twox_128(&Charlie.to_raw_public().to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&30u64),
			twox_128(&Dave.to_raw_public().to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&40u64)
		];

		with_externalities(&mut t, || {
			assert_eq!(era_length(), 2u64);
			assert_eq!(validator_count(), 2usize);
			assert_eq!(bonding_duration(), 3u64);
			assert_eq!(session::validators(), vec![[10u8; 32], [20u8; 32]]);

			// Block 1: Add three validators. No obvious change.
			with_env(|e| e.block_number = 1);
			public::Call::stake().dispatch(PublicPass::new(&Alice));
			PublicPass::new(&Bob).stake();
			PublicPass::new(&Dave).stake();
			check_new_era();
			assert_eq!(session::validators(), vec![[10u8; 32], [20u8; 32]]);

			// Block 2: New validator set now.
			with_env(|e| e.block_number = 2);
			check_new_era();
			assert_eq!(session::validators(), vec![Dave.to_raw_public(), Bob.into()]);

			// Block 3: Unstake highest, introduce another staker. No change yet.
			with_env(|e| e.block_number = 3);
			PublicPass::new(&Charlie).stake();
			PublicPass::new(&Dave).unstake();
			check_new_era();

			// Block 4: New era - validators change.
			with_env(|e| e.block_number = 4);
			check_new_era();
			assert_eq!(session::validators(), vec![Charlie.to_raw_public(), Bob.into()]);

			// Block 5: Transfer stake from highest to lowest. No change yet.
			with_env(|e| e.block_number = 5);
			PublicPass::new(&Dave).transfer(Alice.to_raw_public(), 40);
			check_new_era();

			// Block 6: Lowest now validator.
			with_env(|e| e.block_number = 6);
			check_new_era();
			assert_eq!(session::validators(), vec![Alice.to_raw_public(), Charlie.into()]);

			// Block 7: Unstake three. No change yet.
			with_env(|e| e.block_number = 7);
			PublicPass::new(&Charlie).unstake();
			check_new_era();
			assert_eq!(session::validators(), vec![Alice.to_raw_public(), Charlie.into()]);

			// Block 8: Back to one and two.
			with_env(|e| e.block_number = 8);
			check_new_era();
			assert_eq!(session::validators(), vec![Alice.to_raw_public(), Bob.into()]);
		});
	}

	#[test]
	fn staking_eras_work() {
		let mut t: TestExternalities = map![
			twox_128(session::SESSION_LENGTH).to_vec() => vec![].and(&1u64),
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
			PrivPass::test().set_sessions_per_era(3);
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
		with_externalities(&mut TestExternalities::default(), || {
			set_free_balance(&Alice, 42);
			assert_eq!(free_balance(&Alice), 42);
			assert_eq!(reserved_balance(&Alice), 0);
			assert_eq!(balance(&Alice), 42);
			assert_eq!(free_balance(&Bob), 0);
			assert_eq!(reserved_balance(&Bob), 0);
			assert_eq!(balance(&Bob), 0);
		});
	}

	#[test]
	fn staking_balance_transfer_works() {
		with_externalities(&mut testing::externalities(1, 3, 1), || {
			set_free_balance(&Alice, 112);
			PublicPass::new(&Alice).transfer(Bob.to_raw_public(), 69);
			assert_eq!(balance(&Alice), 42);
			assert_eq!(balance(&Bob), 69);
		});
	}

	#[test]
	#[should_panic]
	fn staking_balance_transfer_when_bonded_panics() {
		with_externalities(&mut TestExternalities::default(), || {
			set_free_balance(&Alice, 111);
			PublicPass::new(&Alice).stake();
			PublicPass::new(&Alice).transfer(Bob.to_raw_public(), 69);
		});
	}

	#[test]
	fn reserving_balance_should_work() {
		with_externalities(&mut TestExternalities::default(), || {
			set_free_balance(&Alice, 111);

			assert_eq!(balance(&Alice), 111);
			assert_eq!(free_balance(&Alice), 111);
			assert_eq!(reserved_balance(&Alice), 0);

			reserve_balance(&Alice, 69);

			assert_eq!(balance(&Alice), 111);
			assert_eq!(free_balance(&Alice), 42);
			assert_eq!(reserved_balance(&Alice), 69);
		});
	}

	#[test]
	#[should_panic]
	fn staking_balance_transfer_when_reserved_panics() {
		with_externalities(&mut TestExternalities::default(), || {
			set_free_balance(&Alice, 111);
			reserve_balance(&Alice, 69);
			PublicPass::new(&Alice).transfer(Bob.to_raw_public(), 69);
		});
	}

	#[test]
	fn deducting_balance_should_work() {
		with_externalities(&mut TestExternalities::default(), || {
			set_free_balance(&Alice, 111);
			assert!(deduct_unbonded(&Alice, 69));
			assert_eq!(free_balance(&Alice), 42);
		});
	}

	#[test]
	fn deducting_balance_should_fail_when_bonded() {
		let mut t: TestExternalities = map![
			twox_128(&Alice.to_raw_public().to_keyed_vec(BALANCE_OF)).to_vec() => vec![].and(&111u64),
			twox_128(&Alice.to_raw_public().to_keyed_vec(BONDAGE_OF)).to_vec() => vec![].and(&2u64)
		];
		with_externalities(&mut t, || {
			with_env(|e| e.block_number = 1);
			assert_eq!(unlock_block(&Alice), LockStatus::LockedUntil(2));
			assert!(!deduct_unbonded(&Alice, 69));
		});
	}

	#[test]
	fn refunding_balance_should_work() {
		with_externalities(&mut TestExternalities::default(), || {
			set_free_balance(&Alice, 42);
			refund(&Alice, 69);
			assert_eq!(free_balance(&Alice), 111);
		});
	}

	#[test]
	fn slashing_balance_should_work() {
		with_externalities(&mut TestExternalities::default(), || {
			set_free_balance(&Alice, 111);
			reserve_balance(&Alice, 69);
			assert!(slash(&Alice, 69));
			assert_eq!(free_balance(&Alice), 0);
			assert_eq!(reserved_balance(&Alice), 42);
		});
	}

	#[test]
	fn slashing_incomplete_balance_should_work() {
		with_externalities(&mut TestExternalities::default(), || {
			set_free_balance(&Alice, 42);
			reserve_balance(&Alice, 21);
			assert!(!slash(&Alice, 69));
			assert_eq!(free_balance(&Alice), 0);
			assert_eq!(reserved_balance(&Alice), 0);
		});
	}

	#[test]
	fn unreserving_balance_should_work() {
		with_externalities(&mut TestExternalities::default(), || {
			set_free_balance(&Alice, 111);
			reserve_balance(&Alice, 111);
			unreserve_balance(&Alice, 42);
			assert_eq!(reserved_balance(&Alice), 69);
			assert_eq!(free_balance(&Alice), 42);
		});
	}

	#[test]
	fn slashing_reserved_balance_should_work() {
		with_externalities(&mut TestExternalities::default(), || {
			set_free_balance(&Alice, 111);
			reserve_balance(&Alice, 111);
			assert!(slash_reserved(&Alice, 42));
			assert_eq!(reserved_balance(&Alice), 69);
			assert_eq!(free_balance(&Alice), 0);
		});
	}

	#[test]
	fn slashing_incomplete_reserved_balance_should_work() {
		with_externalities(&mut TestExternalities::default(), || {
			set_free_balance(&Alice, 111);
			reserve_balance(&Alice, 42);
			assert!(!slash_reserved(&Alice, 69));
			assert_eq!(free_balance(&Alice), 69);
			assert_eq!(reserved_balance(&Alice), 0);
		});
	}

	#[test]
	fn transferring_reserved_balance_should_work() {
		with_externalities(&mut TestExternalities::default(), || {
			set_free_balance(&Alice, 111);
			reserve_balance(&Alice, 111);
			assert!(transfer_reserved_balance(&Alice, &Bob, 42));
			assert_eq!(reserved_balance(&Alice), 69);
			assert_eq!(free_balance(&Alice), 0);
			assert_eq!(reserved_balance(&Bob), 0);
			assert_eq!(free_balance(&Bob), 42);
		});
	}

	#[test]
	fn transferring_incomplete_reserved_balance_should_work() {
		with_externalities(&mut TestExternalities::default(), || {
			set_free_balance(&Alice, 111);
			reserve_balance(&Alice, 42);
			assert!(!transfer_reserved_balance(&Alice, &Bob, 69));
			assert_eq!(reserved_balance(&Alice), 0);
			assert_eq!(free_balance(&Alice), 69);
			assert_eq!(reserved_balance(&Bob), 0);
			assert_eq!(free_balance(&Bob), 42);
		});
	}
}
