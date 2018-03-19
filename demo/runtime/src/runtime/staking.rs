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
use runtime_support::{storage, StorageValue, StorageList, StorageMap};
use demo_primitives::{BlockNumber, AccountId};
use runtime::{system, session, democracy};

/// The balance of an account.
pub type Balance = u64;

/// The amount of bonding period left in an account. Measured in eras.
pub type Bondage = u64;

storage_items! {
	// The length of the bonding duration in eras.
	pub BondingDuration get(bonding_duration): b"sta:loc" => required BlockNumber;
	// The length of a staking era in sessions.
	pub ValidatorCount get(validator_count): b"sta:vac" => required u32;
	// The length of a staking era in sessions.
	pub SessionsPerEra get(sessions_per_era): b"sta:spe" => required BlockNumber;
	// The total amount of stake on the system.
	pub TotalStake get(total_stake): b"sta:tot" => required Balance;
	// The fee to be paid for making a transaction.
	pub TransactionFee get(transaction_fee): b"sta:fee" => required Balance;

	// The current era index.
	pub CurrentEra get(current_era): b"sta:era" => required BlockNumber;
	// All the accounts with a desire to stake.
	pub Intention: b"sta:wil:" => list [ AccountId ];
	// The next value of sessions per era.
	pub NextSessionsPerEra get(next_sessions_per_era): b"sta:nse" => BlockNumber;
	// The block number at which the era length last changed.
	pub LastEraLengthChange get(last_era_length_change): b"sta:lec" => default BlockNumber;

	// The balance of a given account.
	pub FreeBalanceOf get(free_balance_of): b"sta:bal:" => default map [ AccountId => Balance ];

	// The amount of the balance of a given account that is exterally reserved; this can still get
	// slashed, but gets slashed last of all.
	pub ReservedBalanceOf get(reserved_balance_of): b"sta:lbo:" => default map [ AccountId => Balance ];

	// The block at which the `who`'s funds become entirely liquid.
	pub BondageOf get(bondage_of): b"sta:bon:" => default map [ AccountId => Bondage ];

	// The code associated with an account.
	pub CodeOf: b"sta:cod:" => default map [ AccountId => Vec<u8> ];	// TODO Vec<u8> values should be optimised to not do a length prefix.

	// The storage items associated with an account/key.
	pub StorageOf: b"sta:sto:" => map [ (AccountId, Vec<u8>) => Vec<u8> ];	// TODO: keys should also be able to take AsRef<KeyType> to ensure Vec<u8>s can be passed as &[u8]
}

/// The length of a staking era in blocks.
pub fn era_length() -> BlockNumber {
	SessionsPerEra::get() * session::length()
}

/// The combined balance of `who`.
pub fn balance(who: &AccountId) -> Balance {
	FreeBalanceOf::get(who) + ReservedBalanceOf::get(who)
}

/// Some result as `slash(who, value)` (but without the side-effects) asuming there are no
/// balance changes in the meantime.
pub fn can_slash(who: &AccountId, value: Balance) -> bool {
	balance(who) >= value
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
	match BondageOf::get(who) {
		i if i == Bondage::max_value() => LockStatus::Staked,
		i if i <= system::block_number() => LockStatus::Liquid,
		i => LockStatus::LockedUntil(i),
	}
}

pub struct PublicPass<'a> (&'a AccountId);

const NOBODY: AccountId = [0u8; 32];

impl<'a> PublicPass<'a> {
	pub fn new(transactor: &AccountId) -> PublicPass {
		let b = FreeBalanceOf::get(transactor);
		let transaction_fee = TransactionFee::get();
		assert!(b >= transaction_fee, "attempt to transact without enough funds to pay fee");
		FreeBalanceOf::insert(transactor, b - transaction_fee);
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
		let mut intentions = Intention::items();
		// can't be in the list twice.
		assert!(intentions.iter().find(|&t| *t == *self).is_none(), "Cannot stake if already staked.");
		intentions.push(self.clone());
		Intention::set_items(&intentions);
		BondageOf::insert(*self, u64::max_value());
	}

	/// Retract the desire to stake for the transactor.
	///
	/// Effects will be felt at the beginning of the next era.
	fn unstake(self) {
		let mut intentions = Intention::items();
		if let Some(position) = intentions.iter().position(|&t| t == *self) {
			intentions.swap_remove(position);
		} else {
			panic!("Cannot unstake if not already staked.");
		}
		Intention::set_items(&intentions);
		BondageOf::insert(*self, CurrentEra::get() + BondingDuration::get());
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
		NextSessionsPerEra::put(&new);
	}

	/// The length of the bonding duration in eras.
	fn set_bonding_duration(self, new: BlockNumber) {
		BondingDuration::put(&new);
	}

	/// The length of a staking era in sessions.
	fn set_validator_count(self, new: u32) {
		ValidatorCount::put(&new);
	}

	/// Force there to be a new era. This also forces a new session immediately after.
	fn force_new_era(self) {
		new_era();
		session::internal::rotate_session();
	}
}

// Each identity's stake may be in one of three bondage states, given by an integer:
// - n | n <= CurrentEra::get(): inactive: free to be transferred.
// - ~0: active: currently representing a validator.
// - n | n > CurrentEra::get(): deactivating: recently representing a validator and not yet
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
			StorageOf::get(&(*account, location.to_vec()))
		}
		fn get_code(&self, account: &AccountId) -> Vec<u8> {
			CodeOf::get(account)
		}
		fn get_balance(&self, account: &AccountId) -> Balance {
			FreeBalanceOf::get(account)
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
				FreeBalanceOf::insert(address, balance);
			}
			if let Some(code) = changed.code {
				CodeOf::insert(&address, &code);
			}
			for (k, v) in changed.storage.into_iter() {
				if let Some(value) = v {
					StorageOf::insert(&(address, k), &value);
				} else {
					StorageOf::remove(&(address, k));
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
		assert!(BondageOf::get(transactor) <= BondageOf::get(dest));
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

	/// Hook to be called after to transaction processing.
	pub fn check_new_era() {
		// check block number and call new_era if necessary.
		if (system::block_number() - LastEraLengthChange::get()) % era_length() == 0 {
			new_era();
		}
	}

	/// Deduct from an unbonded balance. true if it happened.
	pub fn deduct_unbonded(who: &AccountId, value: Balance) -> bool {
		if let LockStatus::Liquid = unlock_block(who) {
			let b = FreeBalanceOf::get(who);
			if b >= value {
				FreeBalanceOf::insert(who, &(b - value));
				return true;
			}
		}
		false
	}

	/// Refund some balance.
	pub fn refund(who: &AccountId, value: Balance) {
		FreeBalanceOf::insert(who, &(FreeBalanceOf::get(who) + value))
	}

	/// Will slash any balance, but prefer free over reserved.
	pub fn slash(who: &AccountId, value: Balance) -> bool {
		let free_balance = FreeBalanceOf::get(who);
		let free_slash = cmp::min(free_balance, value);
		FreeBalanceOf::insert(who, &(free_balance - free_slash));
		if free_slash < value {
			slash_reserved(who, value - free_slash)
		} else {
			true
		}
	}

	/// Moves `value` from balance to reserved balance.
	pub fn reserve_balance(who: &AccountId, value: Balance) {
		let b = FreeBalanceOf::get(who);
		assert!(b >= value);
		FreeBalanceOf::insert(who, &(b - value));
		ReservedBalanceOf::insert(who, &(ReservedBalanceOf::get(who) + value));
	}

	/// Moves `value` from reserved balance to balance.
	pub fn unreserve_balance(who: &AccountId, value: Balance) {
		let b = ReservedBalanceOf::get(who);
		let value = cmp::min(b, value);
		ReservedBalanceOf::insert(who, &(b - value));
		FreeBalanceOf::insert(who, &(FreeBalanceOf::get(who) + value));
	}

	/// Moves `value` from reserved balance to balance.
	pub fn slash_reserved(who: &AccountId, value: Balance) -> bool {
		let b = ReservedBalanceOf::get(who);
		let slash = cmp::min(b, value);
		ReservedBalanceOf::insert(who, &(b - slash));
		value == slash
	}

	/// Moves `value` from reserved balance to balance.
	pub fn transfer_reserved_balance(slashed: &AccountId, beneficiary: &AccountId, value: Balance) -> bool {
		let b = ReservedBalanceOf::get(slashed);
		let slash = cmp::min(b, value);
		ReservedBalanceOf::insert(slashed, &(b - slash));
		FreeBalanceOf::insert(beneficiary, &(FreeBalanceOf::get(beneficiary) + slash));
		slash == value
	}
}

/// The era has changed - enact new staking set.
///
/// NOTE: This always happens immediately before a session change to ensure that new validators
/// get a chance to set their session keys.
fn new_era() {
	// Increment current era.
	CurrentEra::put(&(CurrentEra::get() + 1));

	// Enact era length change.
	if let Some(next_spe) = NextSessionsPerEra::get() {
		if next_spe != SessionsPerEra::get() {
			SessionsPerEra::put(&next_spe);
			LastEraLengthChange::put(&system::block_number());
		}
	}

	// evaluate desired staking amounts and nominations and optimise to find the best
	// combination of validators, then use session::internal::set_validators().
	// for now, this just orders would-be stakers by their balances and chooses the top-most
	// ValidatorCount::get() of them.
	let mut intentions = Intention::items()
		.into_iter()
		.map(|v| (balance(&v), v))
		.collect::<Vec<_>>();
	intentions.sort_unstable_by(|&(b1, _), &(b2, _)| b2.cmp(&b1));
	session::internal::set_validators(
		&intentions.into_iter()
			.map(|(_, v)| v)
			.take(ValidatorCount::get() as usize)
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
			twox_128(&Intention::len_key()).to_vec() => vec![].and(&3u32),
			twox_128(&Intention::key_for(0)).to_vec() => Alice.to_raw_public_vec(),
			twox_128(&Intention::key_for(1)).to_vec() => Bob.to_raw_public_vec(),
			twox_128(&Intention::key_for(2)).to_vec() => Charlie.to_raw_public_vec(),
			twox_128(SessionsPerEra::key()).to_vec() => vec![].and(&sessions_per_era),
			twox_128(ValidatorCount::key()).to_vec() => vec![].and(&3u64),
			twox_128(BondingDuration::key()).to_vec() => vec![].and(&0u64),
			twox_128(TransactionFee::key()).to_vec() => vec![].and(&1u64),
			twox_128(CurrentEra::key()).to_vec() => vec![].and(&current_era),
			twox_128(&FreeBalanceOf::key_for(*Alice)).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
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
			twox_128(session::SessionLength::key()).to_vec() => vec![].and(&1u64),
			twox_128(session::Validators::key()).to_vec() => vec![].and(&vec![[10u8; 32], [20; 32]]),
			twox_128(CurrentEra::key()).to_vec() => vec![].and(&0u64),
			twox_128(SessionsPerEra::key()).to_vec() => vec![].and(&2u64),
			twox_128(ValidatorCount::key()).to_vec() => vec![].and(&2u32),
			twox_128(BondingDuration::key()).to_vec() => vec![].and(&3u64),
			twox_128(TotalStake::key()).to_vec() => vec![].and(&100u64),
			twox_128(TransactionFee::key()).to_vec() => vec![].and(&0u64),
			twox_128(&FreeBalanceOf::key_for(*Alice)).to_vec() => vec![].and(&10u64),
			twox_128(&FreeBalanceOf::key_for(*Bob)).to_vec() => vec![].and(&20u64),
			twox_128(&FreeBalanceOf::key_for(*Charlie)).to_vec() => vec![].and(&30u64),
			twox_128(&FreeBalanceOf::key_for(*Dave)).to_vec() => vec![].and(&40u64)
		];

		with_externalities(&mut t, || {
			assert_eq!(era_length(), 2u64);
			assert_eq!(ValidatorCount::get(), 2);
			assert_eq!(BondingDuration::get(), 3);
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
			twox_128(session::SessionLength::key()).to_vec() => vec![].and(&1u64),
			twox_128(SessionsPerEra::key()).to_vec() => vec![].and(&2u64),
			twox_128(ValidatorCount::key()).to_vec() => vec![].and(&2u32),
			twox_128(CurrentEra::key()).to_vec() => vec![].and(&0u64)
		];
		with_externalities(&mut t, || {
			assert_eq!(era_length(), 2u64);
			assert_eq!(SessionsPerEra::get(), 2u64);
			assert_eq!(LastEraLengthChange::get(), 0u64);
			assert_eq!(CurrentEra::get(), 0u64);

			// Block 1: No change.
			with_env(|e| e.block_number = 1);
			check_new_era();
			assert_eq!(SessionsPerEra::get(), 2u64);
			assert_eq!(LastEraLengthChange::get(), 0u64);
			assert_eq!(CurrentEra::get(), 0u64);

			// Block 2: Simple era change.
			with_env(|e| e.block_number = 2);
			check_new_era();
			assert_eq!(SessionsPerEra::get(), 2u64);
			assert_eq!(LastEraLengthChange::get(), 0u64);
			assert_eq!(CurrentEra::get(), 1u64);

			// Block 3: Schedule an era length change; no visible changes.
			with_env(|e| e.block_number = 3);
			PrivPass::test().set_sessions_per_era(3);
			check_new_era();
			assert_eq!(SessionsPerEra::get(), 2u64);
			assert_eq!(LastEraLengthChange::get(), 0u64);
			assert_eq!(CurrentEra::get(), 1u64);

			// Block 4: Era change kicks in.
			with_env(|e| e.block_number = 4);
			check_new_era();
			assert_eq!(SessionsPerEra::get(), 3u64);
			assert_eq!(LastEraLengthChange::get(), 4u64);
			assert_eq!(CurrentEra::get(), 2u64);

			// Block 5: No change.
			with_env(|e| e.block_number = 5);
			check_new_era();
			assert_eq!(SessionsPerEra::get(), 3u64);
			assert_eq!(LastEraLengthChange::get(), 4u64);
			assert_eq!(CurrentEra::get(), 2u64);

			// Block 6: No change.
			with_env(|e| e.block_number = 6);
			check_new_era();
			assert_eq!(SessionsPerEra::get(), 3u64);
			assert_eq!(LastEraLengthChange::get(), 4u64);
			assert_eq!(CurrentEra::get(), 2u64);

			// Block 7: Era increment.
			with_env(|e| e.block_number = 7);
			check_new_era();
			assert_eq!(SessionsPerEra::get(), 3u64);
			assert_eq!(LastEraLengthChange::get(), 4u64);
			assert_eq!(CurrentEra::get(), 3u64);
		});
	}

	#[test]
	fn staking_balance_works() {
		with_externalities(&mut TestExternalities::default(), || {
			FreeBalanceOf::insert(*Alice, 42);
			assert_eq!(FreeBalanceOf::get(*Alice), 42);
			assert_eq!(ReservedBalanceOf::get(*Alice), 0);
			assert_eq!(balance(&Alice), 42);
			assert_eq!(FreeBalanceOf::get(*Bob), 0);
			assert_eq!(ReservedBalanceOf::get(*Bob), 0);
			assert_eq!(balance(&Bob), 0);
		});
	}

	#[test]
	fn staking_balance_transfer_works() {
		with_externalities(&mut testing::externalities(1, 3, 1), || {
			FreeBalanceOf::insert(*Alice, 112);
			PublicPass::new(&Alice).transfer(Bob.to_raw_public(), 69);
			assert_eq!(balance(&Alice), 42);
			assert_eq!(balance(&Bob), 69);
		});
	}

	#[test]
	#[should_panic]
	fn staking_balance_transfer_when_bonded_panics() {
		with_externalities(&mut TestExternalities::default(), || {
			FreeBalanceOf::insert(*Alice, 111);
			PublicPass::new(&Alice).stake();
			PublicPass::new(&Alice).transfer(Bob.to_raw_public(), 69);
		});
	}

	#[test]
	fn reserving_balance_should_work() {
		with_externalities(&mut TestExternalities::default(), || {
			FreeBalanceOf::insert(*Alice, 111);

			assert_eq!(balance(&Alice), 111);
			assert_eq!(FreeBalanceOf::get(*Alice), 111);
			assert_eq!(ReservedBalanceOf::get(*Alice), 0);

			reserve_balance(&Alice, 69);

			assert_eq!(balance(&Alice), 111);
			assert_eq!(FreeBalanceOf::get(*Alice), 42);
			assert_eq!(ReservedBalanceOf::get(*Alice), 69);
		});
	}

	#[test]
	#[should_panic]
	fn staking_balance_transfer_when_reserved_panics() {
		with_externalities(&mut TestExternalities::default(), || {
			FreeBalanceOf::insert(*Alice, 111);
			reserve_balance(&Alice, 69);
			PublicPass::new(&Alice).transfer(Bob.to_raw_public(), 69);
		});
	}

	#[test]
	fn deducting_balance_should_work() {
		with_externalities(&mut TestExternalities::default(), || {
			FreeBalanceOf::insert(*Alice, 111);
			assert!(deduct_unbonded(&Alice, 69));
			assert_eq!(FreeBalanceOf::get(*Alice), 42);
		});
	}

	#[test]
	fn deducting_balance_should_fail_when_bonded() {
		let mut t: TestExternalities = map![
			twox_128(&FreeBalanceOf::key_for(*Alice)).to_vec() => vec![].and(&111u64),
			twox_128(&BondageOf::key_for(*Alice)).to_vec() => vec![].and(&2u64)
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
			FreeBalanceOf::insert(*Alice, 42);
			refund(&Alice, 69);
			assert_eq!(FreeBalanceOf::get(*Alice), 111);
		});
	}

	#[test]
	fn slashing_balance_should_work() {
		with_externalities(&mut TestExternalities::default(), || {
			FreeBalanceOf::insert(*Alice, 111);
			reserve_balance(&Alice, 69);
			assert!(slash(&Alice, 69));
			assert_eq!(FreeBalanceOf::get(*Alice), 0);
			assert_eq!(ReservedBalanceOf::get(*Alice), 42);
		});
	}

	#[test]
	fn slashing_incomplete_balance_should_work() {
		with_externalities(&mut TestExternalities::default(), || {
			FreeBalanceOf::insert(*Alice, 42);
			reserve_balance(&Alice, 21);
			assert!(!slash(&Alice, 69));
			assert_eq!(FreeBalanceOf::get(*Alice), 0);
			assert_eq!(ReservedBalanceOf::get(*Alice), 0);
		});
	}

	#[test]
	fn unreserving_balance_should_work() {
		with_externalities(&mut TestExternalities::default(), || {
			FreeBalanceOf::insert(*Alice, 111);
			reserve_balance(&Alice, 111);
			unreserve_balance(&Alice, 42);
			assert_eq!(ReservedBalanceOf::get(*Alice), 69);
			assert_eq!(FreeBalanceOf::get(*Alice), 42);
		});
	}

	#[test]
	fn slashing_reserved_balance_should_work() {
		with_externalities(&mut TestExternalities::default(), || {
			FreeBalanceOf::insert(*Alice, 111);
			reserve_balance(&Alice, 111);
			assert!(slash_reserved(&Alice, 42));
			assert_eq!(ReservedBalanceOf::get(*Alice), 69);
			assert_eq!(FreeBalanceOf::get(*Alice), 0);
		});
	}

	#[test]
	fn slashing_incomplete_reserved_balance_should_work() {
		with_externalities(&mut TestExternalities::default(), || {
			FreeBalanceOf::insert(*Alice, 111);
			reserve_balance(&Alice, 42);
			assert!(!slash_reserved(&Alice, 69));
			assert_eq!(FreeBalanceOf::get(*Alice), 69);
			assert_eq!(ReservedBalanceOf::get(*Alice), 0);
		});
	}

	#[test]
	fn transferring_reserved_balance_should_work() {
		with_externalities(&mut TestExternalities::default(), || {
			FreeBalanceOf::insert(*Alice, 111);
			reserve_balance(&Alice, 111);
			assert!(transfer_reserved_balance(&Alice, &Bob, 42));
			assert_eq!(ReservedBalanceOf::get(*Alice), 69);
			assert_eq!(FreeBalanceOf::get(*Alice), 0);
			assert_eq!(ReservedBalanceOf::get(*Bob), 0);
			assert_eq!(FreeBalanceOf::get(*Bob), 42);
		});
	}

	#[test]
	fn transferring_incomplete_reserved_balance_should_work() {
		with_externalities(&mut TestExternalities::default(), || {
			FreeBalanceOf::insert(*Alice, 111);
			reserve_balance(&Alice, 42);
			assert!(!transfer_reserved_balance(&Alice, &Bob, 69));
			assert_eq!(ReservedBalanceOf::get(*Alice), 0);
			assert_eq!(FreeBalanceOf::get(*Alice), 69);
			assert_eq!(ReservedBalanceOf::get(*Bob), 0);
			assert_eq!(FreeBalanceOf::get(*Bob), 42);
		});
	}
}
