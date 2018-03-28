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

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")] extern crate serde;

#[cfg(any(feature = "std", test))] extern crate substrate_keyring as keyring;

extern crate substrate_codec as codec;
#[cfg_attr(feature = "std", macro_use)] extern crate substrate_runtime_std as rstd;
extern crate substrate_runtime_io as runtime_io;
#[macro_use] extern crate substrate_runtime_support as runtime_support;
extern crate substrate_runtime_primitives as primitives;
extern crate substrate_runtime_session as session;
extern crate substrate_runtime_system as system;

#[cfg(test)] use std::fmt::Debug;
use rstd::prelude::*;
use rstd::cmp;
use rstd::cell::RefCell;
use rstd::marker::PhantomData;
use rstd::collections::btree_map::{BTreeMap, Entry};
use codec::Slicable;
use runtime_support::{StorageValue, StorageMap, Parameter};
use primitives::{Zero, One, Bounded, RefInto, SimpleArithmetic, Executable, MakePayment};

#[cfg(test)]
#[derive(Debug, PartialEq, Clone)]
pub enum LockStatus<BlockNumber: Debug + PartialEq + Clone> {
	Liquid,
	LockedUntil(BlockNumber),
	Staked,
}

#[cfg(not(test))]
#[derive(PartialEq, Clone)]
pub enum LockStatus<BlockNumber: PartialEq + Clone> {
	Liquid,
	LockedUntil(BlockNumber),
	Staked,
}

pub trait ContractAddressFor<AccountId: Sized> {
	fn contract_address_for(code: &[u8], origin: &AccountId) -> AccountId;
}

impl<Hashing, AccountId> ContractAddressFor<AccountId> for Hashing where
	Hashing: runtime_io::Hashing,
	AccountId: Sized + Slicable + From<Hashing::Output>,
	Hashing::Output: Slicable
{
	fn contract_address_for(code: &[u8], origin: &AccountId) -> AccountId {
		let mut dest_pre = Hashing::hash(code).encode();
		origin.using_encoded(|s| dest_pre.extend(s));
		AccountId::from(Hashing::hash(&dest_pre))
	}
}

pub trait Trait: system::Trait + session::Trait {
	/// The balance of an account.
	type Balance: Parameter + SimpleArithmetic + Default + Copy;
	type DetermineContractAddress: ContractAddressFor<Self::AccountId>;
}

decl_module! {
	pub struct Module<T: Trait>;
	pub enum Call where aux: T::PublicAux {
		fn transfer(aux, dest: T::AccountId, value: T::Balance) = 0;
		fn stake(aux) = 1;
		fn unstake(aux) = 2;
	}
	pub enum PrivCall {
		fn set_sessions_per_era(new: T::BlockNumber) = 0;
		fn set_bonding_duration(new: T::BlockNumber) = 1;
		fn set_validator_count(new: u32) = 2;
		fn force_new_era() = 3;
	}
}

decl_storage! {
	trait Store for Module<T: Trait>;

	// The length of the bonding duration in eras.
	pub BondingDuration get(bonding_duration): b"sta:loc" => required T::BlockNumber;
	// The length of a staking era in sessions.
	pub ValidatorCount get(validator_count): b"sta:vac" => required u32;
	// The length of a staking era in sessions.
	pub SessionsPerEra get(sessions_per_era): b"sta:spe" => required T::BlockNumber;
	// The total amount of stake on the system.
	pub TotalStake get(total_stake): b"sta:tot" => required T::Balance;
	// The fee to be paid for making a transaction.
	pub TransactionFee get(transaction_fee): b"sta:fee" => required T::Balance;

	// The current era index.
	pub CurrentEra get(current_era): b"sta:era" => required T::BlockNumber;
	// All the accounts with a desire to stake.
	pub Intentions: b"sta:wil:" => default Vec<T::AccountId>;
	// The next value of sessions per era.
	pub NextSessionsPerEra get(next_sessions_per_era): b"sta:nse" => T::BlockNumber;
	// The block number at which the era length last changed.
	pub LastEraLengthChange get(last_era_length_change): b"sta:lec" => default T::BlockNumber;

	// The balance of a given account.
	pub FreeBalance get(free_balance): b"sta:bal:" => default map [ T::AccountId => T::Balance ];

	// The amount of the balance of a given account that is exterally reserved; this can still get
	// slashed, but gets slashed last of all.
	pub ReservedBalance get(reserved_balance): b"sta:lbo:" => default map [ T::AccountId => T::Balance ];

	// The block at which the `who`'s funds become entirely liquid.
	pub Bondage get(bondage): b"sta:bon:" => default map [ T::AccountId => T::BlockNumber ];

	// The code associated with an account.
	pub CodeOf: b"sta:cod:" => default map [ T::AccountId => Vec<u8> ];	// TODO Vec<u8> values should be optimised to not do a length prefix.

	// The storage items associated with an account/key.
	pub StorageOf: b"sta:sto:" => map [ (T::AccountId, Vec<u8>) => Vec<u8> ];	// TODO: keys should also be able to take AsRef<KeyType> to ensure Vec<u8>s can be passed as &[u8]
}

impl<T: Trait> Module<T> {

	// PUBLIC IMMUTABLES

	/// The length of a staking era in blocks.
	pub fn era_length() -> T::BlockNumber {
		Self::sessions_per_era() * <session::Module<T>>::length()
	}

	/// The combined balance of `who`.
	pub fn balance(who: &T::AccountId) -> T::Balance {
		Self::free_balance(who) + Self::reserved_balance(who)
	}

	/// Some result as `slash(who, value)` (but without the side-effects) asuming there are no
	/// balance changes in the meantime.
	pub fn can_slash(who: &T::AccountId, value: T::Balance) -> bool {
		Self::balance(who) >= value
	}

	/// The block at which the `who`'s funds become entirely liquid.
	pub fn unlock_block(who: &T::AccountId) -> LockStatus<T::BlockNumber> {
		match Self::bondage(who) {
			i if i == T::BlockNumber::max_value() => LockStatus::Staked,
			i if i <= <system::Module<T>>::block_number() => LockStatus::Liquid,
			i => LockStatus::LockedUntil(i),
		}
	}

	/// Create a smart-contract account.
	pub fn create(aux: &T::PublicAux, code: &[u8], value: T::Balance) {
		// commit anything that made it this far to storage
		if let Some(commit) = Self::effect_create(aux.ref_into(), code, value, DirectExt) {
			Self::commit_state(commit);
		}
	}

	// PUBLIC DISPATCH

	/// Transfer some unlocked staking balance to another staker.
	/// TODO: probably want to state gas-limit and gas-price.
	fn transfer(aux: &T::PublicAux, dest: T::AccountId, value: T::Balance) {
		// commit anything that made it this far to storage
		if let Some(commit) = Self::effect_transfer(aux.ref_into(), &dest, value, DirectExt) {
			Self::commit_state(commit);
		}
	}

	/// Declare the desire to stake for the transactor.
	///
	/// Effects will be felt at the beginning of the next era.
	fn stake(aux: &T::PublicAux) {
		let mut intentions = <Intentions<T>>::get();
		// can't be in the list twice.
		assert!(intentions.iter().find(|&t| t == aux.ref_into()).is_none(), "Cannot stake if already staked.");
		intentions.push(aux.ref_into().clone());
		<Intentions<T>>::put(intentions);
		<Bondage<T>>::insert(aux.ref_into(), T::BlockNumber::max_value());
	}

	/// Retract the desire to stake for the transactor.
	///
	/// Effects will be felt at the beginning of the next era.
	fn unstake(aux: &T::PublicAux) {
		let mut intentions = <Intentions<T>>::get();
		if let Some(position) = intentions.iter().position(|t| t == aux.ref_into()) {
			intentions.swap_remove(position);
		} else {
			panic!("Cannot unstake if not already staked.");
		}
		<Intentions<T>>::put(intentions);
		<Bondage<T>>::insert(aux.ref_into(), Self::current_era() + Self::bonding_duration());
	}

	// PRIV DISPATCH

	/// Set the number of sessions in an era.
	fn set_sessions_per_era(new: T::BlockNumber) {
		<NextSessionsPerEra<T>>::put(&new);
	}

	/// The length of the bonding duration in eras.
	fn set_bonding_duration(new: T::BlockNumber) {
		<BondingDuration<T>>::put(&new);
	}

	/// The length of a staking era in sessions.
	fn set_validator_count(new: u32) {
		<ValidatorCount<T>>::put(&new);
	}

	/// Force there to be a new era. This also forces a new session immediately after.
	fn force_new_era() {
		Self::new_era();
		<session::Module<T>>::rotate_session();
	}

	// PUBLIC MUTABLES (DANGEROUS)

	/// Deduct from an unbonded balance. true if it happened.
	pub fn deduct_unbonded(who: &T::AccountId, value: T::Balance) -> bool {
		if let LockStatus::Liquid = Self::unlock_block(who) {
			let b = Self::free_balance(who);
			if b >= value {
				<FreeBalance<T>>::insert(who, b - value);
				return true;
			}
		}
		false
	}

	/// Refund some balance.
	pub fn refund(who: &T::AccountId, value: T::Balance) {
		<FreeBalance<T>>::insert(who, Self::free_balance(who) + value)
	}

	/// Will slash any balance, but prefer free over reserved.
	pub fn slash(who: &T::AccountId, value: T::Balance) -> bool {
		let free_balance = Self::free_balance(who);
		let free_slash = cmp::min(free_balance, value);
		<FreeBalance<T>>::insert(who, &(free_balance - free_slash));
		if free_slash < value {
			Self::slash_reserved(who, value - free_slash)
		} else {
			true
		}
	}

	/// Moves `value` from balance to reserved balance.
	pub fn reserve_balance(who: &T::AccountId, value: T::Balance) {
		let b = Self::free_balance(who);
		assert!(b >= value);
		<FreeBalance<T>>::insert(who, b - value);
		<ReservedBalance<T>>::insert(who, Self::reserved_balance(who) + value);
	}

	/// Moves `value` from reserved balance to balance.
	pub fn unreserve_balance(who: &T::AccountId, value: T::Balance) {
		let b = Self::reserved_balance(who);
		let value = cmp::min(b, value);
		<ReservedBalance<T>>::insert(who, b - value);
		<FreeBalance<T>>::insert(who, Self::free_balance(who) + value);
	}

	/// Moves `value` from reserved balance to balance.
	pub fn slash_reserved(who: &T::AccountId, value: T::Balance) -> bool {
		let b = Self::reserved_balance(who);
		let slash = cmp::min(b, value);
		<ReservedBalance<T>>::insert(who, b - slash);
		value == slash
	}

	/// Moves `value` from reserved balance to balance.
	pub fn transfer_reserved_balance(slashed: &T::AccountId, beneficiary: &T::AccountId, value: T::Balance) -> bool {
		let b = Self::reserved_balance(slashed);
		let slash = cmp::min(b, value);
		<ReservedBalance<T>>::insert(slashed, b - slash);
		<FreeBalance<T>>::insert(beneficiary, Self::free_balance(beneficiary) + slash);
		slash == value
	}

	/// The era has changed - enact new staking set.
	///
	/// NOTE: This always happens immediately before a session change to ensure that new validators
	/// get a chance to set their session keys.
	fn new_era() {
		// Increment current era.
		<CurrentEra<T>>::put(&(<CurrentEra<T>>::get() + One::one()));

		// Enact era length change.
		if let Some(next_spe) = <NextSessionsPerEra<T>>::get() {
			if next_spe != <SessionsPerEra<T>>::get() {
				<SessionsPerEra<T>>::put(&next_spe);
				<LastEraLengthChange<T>>::put(&<system::Module<T>>::block_number());
			}
		}

		// evaluate desired staking amounts and nominations and optimise to find the best
		// combination of validators, then use session::internal::set_validators().
		// for now, this just orders would-be stakers by their balances and chooses the top-most
		// <ValidatorCount<T>>::get() of them.
		let mut intentions = <Intentions<T>>::get()
			.into_iter()
			.map(|v| (Self::balance(&v), v))
			.collect::<Vec<_>>();
		intentions.sort_unstable_by(|&(ref b1, _), &(ref b2, _)| b2.cmp(&b1));
		<session::Module<T>>::set_validators(
			&intentions.into_iter()
				.map(|(_, v)| v)
				.take(<ValidatorCount<T>>::get() as usize)
				.collect::<Vec<_>>()
		);
	}

	// NON-PUBLIC

	/// Hook to be called after to transaction processing.
	fn check_new_era() {
		// check block number and call new_era if necessary.
		if (<system::Module<T>>::block_number() - <LastEraLengthChange<T>>::get()) % Self::era_length() == Zero::zero() {
			Self::new_era();
		}
	}
}

impl<T: Trait> Executable for Module<T> {
	fn execute() {
		Self::check_new_era();
	}
}

// Each identity's stake may be in one of three bondage states, given by an integer:
// - n | n <= <CurrentEra<T>>::get(): inactive: free to be transferred.
// - ~0: active: currently representing a validator.
// - n | n > <CurrentEra<T>>::get(): deactivating: recently representing a validator and not yet
//   ready for transfer.

struct ChangeEntry<T: Trait> {
	balance: Option<T::Balance>,
	code: Option<Vec<u8>>,
	storage: BTreeMap<Vec<u8>, Option<Vec<u8>>>,
}

// Cannot derive(Default) since it erroneously bounds T by Default.
impl<T: Trait> Default for ChangeEntry<T> {
	fn default() -> Self {
		ChangeEntry {
			balance: Default::default(),
			code: Default::default(),
			storage: Default::default(),
		}
	}
}

impl<T: Trait> ChangeEntry<T> {
	pub fn balance_changed(b: T::Balance) -> Self {
		ChangeEntry { balance: Some(b), code: None, storage: Default::default() }
	}
}

// Compiler bug: https://github.com/rust-lang/rust/issues/40640. Will cause a warning and there's
// not much we can do about it.
type State<T: Trait> = BTreeMap<T::AccountId, ChangeEntry<T>>;

trait Externalities<T: Trait> {
	fn get_storage(&self, account: &T::AccountId, location: &[u8]) -> Option<Vec<u8>>;
	fn get_code(&self, account: &T::AccountId) -> Vec<u8>;
	fn get_balance(&self, account: &T::AccountId) -> T::Balance;
}

struct Ext<T: Trait, F1, F3, F5> where
	F1 : Fn(&T::AccountId, &[u8]) -> Option<Vec<u8>>,
	F3 : Fn(&T::AccountId) -> Vec<u8>,
	F5 : Fn(&T::AccountId) -> T::Balance
{
	do_get_storage: F1,
	do_get_code: F3,
	do_get_balance: F5,
	_unused: PhantomData<T>,
}

struct DirectExt;
impl<T: Trait> Externalities<T> for DirectExt {
	fn get_storage(&self, account: &T::AccountId, location: &[u8]) -> Option<Vec<u8>> {
		<StorageOf<T>>::get(&(account.clone(), location.to_vec()))
	}
	fn get_code(&self, account: &T::AccountId) -> Vec<u8> {
		<CodeOf<T>>::get(account)
	}
	fn get_balance(&self, account: &T::AccountId) -> T::Balance {
		<FreeBalance<T>>::get(account)
	}
}

impl<T: Trait, F1, F3, F5> Externalities<T> for Ext<T, F1, F3, F5> where
	F1 : Fn(&T::AccountId, &[u8]) -> Option<Vec<u8>>,
	F3 : Fn(&T::AccountId) -> Vec<u8>,
	F5 : Fn(&T::AccountId) -> T::Balance
{
	fn get_storage(&self, account: &T::AccountId, location: &[u8]) -> Option<Vec<u8>> {
		(self.do_get_storage)(account, location)
	}
	fn get_code(&self, account: &T::AccountId) -> Vec<u8> {
		(self.do_get_code)(account)
	}
	fn get_balance(&self, account: &T::AccountId) -> T::Balance {
		(self.do_get_balance)(account)
	}
}

impl<T: Trait> Module<T> {
	fn commit_state(s: State<T>) {
		for (address, changed) in s.into_iter() {
			if let Some(balance) = changed.balance {
				<FreeBalance<T>>::insert(&address, balance);
			}
			if let Some(code) = changed.code {
				<CodeOf<T>>::insert(&address, &code);
			}
			for (k, v) in changed.storage.into_iter() {
				if let Some(value) = v {
					<StorageOf<T>>::insert((address.clone(), k), &value);
				} else {
					<StorageOf<T>>::remove((address.clone(), k));
				}
			}
		}
	}

	fn merge_state(commit_state: State<T>, local: &mut State<T>) {
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

	fn effect_create<E: Externalities<T>>(
		transactor: &T::AccountId,
		code: &[u8],
		value: T::Balance,
		ext: E
	) -> Option<State<T>> {
		let from_balance = ext.get_balance(transactor);
		// TODO: a fee.
		assert!(from_balance >= value);

		let dest = T::DetermineContractAddress::contract_address_for(code, transactor);

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

	fn effect_transfer<E: Externalities<T>>(
		transactor: &T::AccountId,
		dest: &T::AccountId,
		value: T::Balance,
		ext: E
	) -> Option<State<T>> {
		let from_balance = ext.get_balance(transactor);
		assert!(from_balance >= value);

		let to_balance = ext.get_balance(dest);
		assert!(<Bondage<T>>::get(transactor) <= <Bondage<T>>::get(dest));
		assert!(to_balance + value > to_balance);	// no overflow

		// TODO: a fee, based upon gaslimit/gasprice.
		// TODO: consider storing upper-bound for contract's gas limit in fixed-length runtime
		// code in contract itself and use that.

		let local: RefCell<State<T>> = RefCell::new(BTreeMap::new());

		if transactor != dest {
			let mut local = local.borrow_mut();
			local.insert(transactor.clone(), ChangeEntry::balance_changed(from_balance - value));
			local.insert(dest.clone(), ChangeEntry::balance_changed(to_balance + value));
		}

		let should_commit = {
			// Our local ext: Should be used for any transfers and creates that happen internally.
			let ext = || Ext {
				do_get_storage: |account: &T::AccountId, location: &[u8]|
					local.borrow().get(account)
						.and_then(|a| a.storage.get(location))
						.cloned()
						.unwrap_or_else(|| ext.get_storage(account, location)),
				do_get_code: |account: &T::AccountId|
					local.borrow().get(account)
						.and_then(|a| a.code.clone())
						.unwrap_or_else(|| ext.get_code(account)),
				do_get_balance: |account: &T::AccountId|
					local.borrow().get(account)
						.and_then(|a| a.balance)
						.unwrap_or_else(|| ext.get_balance(account)),
				_unused: Default::default(),
			};
			let mut _transfer = |inner_dest: &T::AccountId, value: T::Balance| {
				if let Some(commit_state) = Self::effect_transfer(dest, inner_dest, value, ext()) {
					Self::merge_state(commit_state, &mut *local.borrow_mut());
				}
			};
			let mut _create = |code: &[u8], value: T::Balance| {
				if let Some(commit_state) = Self::effect_create(dest, code, value, ext()) {
					Self::merge_state(commit_state, &mut *local.borrow_mut());
				}
			};
			let mut _put_storage = |location: Vec<u8>, value: Option<Vec<u8>>| {
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

impl<T: Trait> MakePayment<T::AccountId> for Module<T> {
	fn make_payment(transactor: &T::AccountId) {
		let b = Self::free_balance(transactor);
		let transaction_fee = Self::transaction_fee();
		assert!(b >= transaction_fee, "attempt to transact without enough funds to pay fee");
		<FreeBalance<T>>::insert(transactor, b - transaction_fee);
	}
}

#[cfg(any(feature = "std", test))]
pub struct DummyContractAddressFor;
impl ContractAddressFor<u64> for DummyContractAddressFor {
	fn contract_address_for(_code: &[u8], origin: &u64) -> u64 {
		origin + 1
	}
}

#[cfg(any(feature = "std", test))]
pub struct TestingConfig<T: Trait> {
	pub sessions_per_era: T::BlockNumber,
	pub current_era: T::BlockNumber,
	pub balances: Vec<(T::AccountId, T::Balance)>,
	pub intentions: Vec<T::AccountId>,
	pub validator_count: u64,
	pub bonding_duration: T::BlockNumber,
	pub transaction_fee: T::Balance,
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> TestingConfig<T> where T::AccountId: From<keyring::Keyring> {
	pub fn simple() -> Self {
		use primitives::As;
		use keyring::Keyring::*;
		TestingConfig {
			sessions_per_era: T::BlockNumber::sa(2),
			current_era: T::BlockNumber::sa(0),
			balances: vec![(T::AccountId::from(Alice), T::Balance::sa(111))],
			intentions: vec![T::AccountId::from(Alice), T::AccountId::from(Bob), T::AccountId::from(Charlie)],
			validator_count: 3u64,
			bonding_duration: T::BlockNumber::sa(0),
			transaction_fee: T::Balance::sa(0),
		}
	}

	pub fn extended() -> Self {
		use primitives::As;
		use keyring::Keyring::*;
		TestingConfig {
			sessions_per_era: T::BlockNumber::sa(3),
			current_era: T::BlockNumber::sa(1),
			balances: vec![
				(T::AccountId::from(Alice), T::Balance::sa(10)),
				(T::AccountId::from(Bob), T::Balance::sa(20)),
				(T::AccountId::from(Charlie), T::Balance::sa(30)),
				(T::AccountId::from(Dave), T::Balance::sa(40)),
				(T::AccountId::from(Eve), T::Balance::sa(50)),
				(T::AccountId::from(Ferdie), T::Balance::sa(60)),
				(T::AccountId::from(One), T::Balance::sa(1))
			],
			intentions: vec![T::AccountId::from(Alice), T::AccountId::from(Bob), T::AccountId::from(Charlie)],
			validator_count: 3u64,
			bonding_duration: T::BlockNumber::sa(0),
			transaction_fee: T::Balance::sa(1),
		}
	}
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> primitives::MakeTestExternalities for TestingConfig<T> {
	fn test_externalities(self) -> runtime_io::TestExternalities {
		use runtime_io::twox_128;
		use codec::Slicable;

		let total_stake: T::Balance = self.balances.iter().fold(Zero::zero(), |acc, &(_, n)| acc + n);

		let mut r: runtime_io::TestExternalities = map![
			twox_128(<Intentions<T>>::key()).to_vec() => self.intentions.encode(),
			twox_128(<SessionsPerEra<T>>::key()).to_vec() => self.sessions_per_era.encode(),
			twox_128(<ValidatorCount<T>>::key()).to_vec() => self.validator_count.encode(),
			twox_128(<BondingDuration<T>>::key()).to_vec() => self.bonding_duration.encode(),
			twox_128(<TransactionFee<T>>::key()).to_vec() => self.transaction_fee.encode(),
			twox_128(<CurrentEra<T>>::key()).to_vec() => self.current_era.encode(),
			twox_128(<TotalStake<T>>::key()).to_vec() => total_stake.encode()
		];

		for (who, value) in self.balances.into_iter() {
			r.insert(twox_128(&<FreeBalance<T>>::key_for(who)).to_vec(), value.encode());
		}
		r
	}
}
/*
#[cfg(test)]
mod tests {
	use super::*;
	use super::internal::*;
	use super::privileged::*;

	use runtime_io::{with_externalities, twox_128, TestExternalities};
	use codec::{KeyedVec, Joiner};
	use keyring::Keyring::*;
	use demo_primitives::AccountId;
	use runtime::{staking, session};
	use runtime_support::PrivPass;
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
			twox_128(&FreeBalance::key_for(*Alice)).to_vec() => vec![].and(&10u64),
			twox_128(&FreeBalance::key_for(*Bob)).to_vec() => vec![].and(&20u64),
			twox_128(&FreeBalance::key_for(*Charlie)).to_vec() => vec![].and(&30u64),
			twox_128(&FreeBalance::key_for(*Dave)).to_vec() => vec![].and(&40u64)
		];

		with_externalities(&mut t, || {
			assert_eq!(era_length(), 2u64);
			assert_eq!(<ValidatorCount<T>>::get(), 2);
			assert_eq!(<BondingDuration<T>>::get(), 3);
			assert_eq!(session::validators(), vec![[10u8; 32], [20u8; 32]]);

			// Block 1: Add three validators. No obvious change.
			system::testing::set_block_number(1);
			public::Call::stake().dispatch(public_pass_from_payment(&Alice));
			public_pass_from_payment(&Bob).stake();
			public_pass_from_payment(&Dave).stake();
			check_new_era();
			assert_eq!(session::validators(), vec![[10u8; 32], [20u8; 32]]);

			// Block 2: New validator set now.
			system::testing::set_block_number(2);
			check_new_era();
			assert_eq!(session::validators(), vec![Dave.to_raw_public(), Bob.into()]);

			// Block 3: Unstake highest, introduce another staker. No change yet.
			system::testing::set_block_number(3);
			public_pass_from_payment(&Charlie).stake();
			public_pass_from_payment(&Dave).unstake();
			check_new_era();

			// Block 4: New era - validators change.
			system::testing::set_block_number(4);
			check_new_era();
			assert_eq!(session::validators(), vec![Charlie.to_raw_public(), Bob.into()]);

			// Block 5: Transfer stake from highest to lowest. No change yet.
			system::testing::set_block_number(5);
			public_pass_from_payment(&Dave).transfer(Alice.to_raw_public(), 40);
			check_new_era();

			// Block 6: Lowest now validator.
			system::testing::set_block_number(6);
			check_new_era();
			assert_eq!(session::validators(), vec![Alice.to_raw_public(), Charlie.into()]);

			// Block 7: Unstake three. No change yet.
			system::testing::set_block_number(7);
			public_pass_from_payment(&Charlie).unstake();
			check_new_era();
			assert_eq!(session::validators(), vec![Alice.to_raw_public(), Charlie.into()]);

			// Block 8: Back to one and two.
			system::testing::set_block_number(8);
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
			assert_eq!(<SessionsPerEra<T>>::get(), 2u64);
			assert_eq!(<LastEraLengthChange<T>>::get(), 0u64);
			assert_eq!(<CurrentEra<T>>::get(), 0u64);

			// Block 1: No change.
			system::testing::set_block_number(1);
			check_new_era();
			assert_eq!(<SessionsPerEra<T>>::get(), 2u64);
			assert_eq!(<LastEraLengthChange<T>>::get(), 0u64);
			assert_eq!(<CurrentEra<T>>::get(), 0u64);

			// Block 2: Simple era change.
			system::testing::set_block_number(2);
			check_new_era();
			assert_eq!(<SessionsPerEra<T>>::get(), 2u64);
			assert_eq!(<LastEraLengthChange<T>>::get(), 0u64);
			assert_eq!(<CurrentEra<T>>::get(), 1u64);

			// Block 3: Schedule an era length change; no visible changes.
			system::testing::set_block_number(3);
			PrivPass::test().set_sessions_per_era(3);
			check_new_era();
			assert_eq!(<SessionsPerEra<T>>::get(), 2u64);
			assert_eq!(<LastEraLengthChange<T>>::get(), 0u64);
			assert_eq!(<CurrentEra<T>>::get(), 1u64);

			// Block 4: Era change kicks in.
			system::testing::set_block_number(4);
			check_new_era();
			assert_eq!(<SessionsPerEra<T>>::get(), 3u64);
			assert_eq!(<LastEraLengthChange<T>>::get(), 4u64);
			assert_eq!(<CurrentEra<T>>::get(), 2u64);

			// Block 5: No change.
			system::testing::set_block_number(5);
			check_new_era();
			assert_eq!(<SessionsPerEra<T>>::get(), 3u64);
			assert_eq!(<LastEraLengthChange<T>>::get(), 4u64);
			assert_eq!(<CurrentEra<T>>::get(), 2u64);

			// Block 6: No change.
			system::testing::set_block_number(6);
			check_new_era();
			assert_eq!(<SessionsPerEra<T>>::get(), 3u64);
			assert_eq!(<LastEraLengthChange<T>>::get(), 4u64);
			assert_eq!(<CurrentEra<T>>::get(), 2u64);

			// Block 7: Era increment.
			system::testing::set_block_number(7);
			check_new_era();
			assert_eq!(<SessionsPerEra<T>>::get(), 3u64);
			assert_eq!(<LastEraLengthChange<T>>::get(), 4u64);
			assert_eq!(<CurrentEra<T>>::get(), 3u64);
		});
	}

	#[test]
	fn staking_balance_works() {
		with_externalities(&mut testing::externalities(1, 3, 1), || {
			<FreeBalance<T>>::insert(*Alice, 42);
			assert_eq!(<FreeBalance<T>>::get(*Alice), 42);
			assert_eq!(<ReservedBalance<T>>::get(*Alice), 0);
			assert_eq!(balance(&Alice), 42);
			assert_eq!(<FreeBalance<T>>::get(*Bob), 0);
			assert_eq!(<ReservedBalance<T>>::get(*Bob), 0);
			assert_eq!(balance(&Bob), 0);
		});
	}

	#[test]
	fn staking_balance_transfer_works() {
		with_externalities(&mut testing::externalities(1, 3, 1), || {
			<FreeBalance<T>>::insert(*Alice, 112);
			public_pass_from_payment(&Alice).transfer(Bob.to_raw_public(), 69);
			assert_eq!(balance(&Alice), 42);
			assert_eq!(balance(&Bob), 69);
		});
	}

	#[test]
	#[should_panic]
	fn staking_balance_transfer_when_bonded_panics() {
		with_externalities(&mut testing::externalities(1, 3, 1), || {
			<FreeBalance<T>>::insert(*Alice, 111);
			public_pass_from_payment(&Alice).stake();
			public_pass_from_payment(&Alice).transfer(Bob.to_raw_public(), 69);
		});
	}

	#[test]
	fn reserving_balance_should_work() {
		with_externalities(&mut testing::externalities(1, 3, 1), || {
			<FreeBalance<T>>::insert(*Alice, 111);

			assert_eq!(balance(&Alice), 111);
			assert_eq!(<FreeBalance<T>>::get(*Alice), 111);
			assert_eq!(<ReservedBalance<T>>::get(*Alice), 0);

			reserve_balance(&Alice, 69);

			assert_eq!(balance(&Alice), 111);
			assert_eq!(<FreeBalance<T>>::get(*Alice), 42);
			assert_eq!(<ReservedBalance<T>>::get(*Alice), 69);
		});
	}

	#[test]
	#[should_panic]
	fn staking_balance_transfer_when_reserved_panics() {
		with_externalities(&mut testing::externalities(1, 3, 1), || {
			<FreeBalance<T>>::insert(*Alice, 111);
			reserve_balance(&Alice, 69);
			public_pass_from_payment(&Alice).transfer(Bob.to_raw_public(), 69);
		});
	}

	#[test]
	fn deducting_balance_should_work() {
		with_externalities(&mut testing::externalities(1, 3, 1), || {
			<FreeBalance<T>>::insert(*Alice, 111);
			assert!(deduct_unbonded(&Alice, 69));
			assert_eq!(<FreeBalance<T>>::get(*Alice), 42);
		});
	}

	#[test]
	fn deducting_balance_should_fail_when_bonded() {
		let mut t: TestExternalities = map![
			twox_128(&FreeBalance::key_for(*Alice)).to_vec() => vec![].and(&111u64),
			twox_128(&Bondage::key_for(*Alice)).to_vec() => vec![].and(&2u64)
		];
		with_externalities(&mut t, || {
			system::testing::set_block_number(1);
			assert_eq!(unlock_block(&Alice), LockStatus::LockedUntil(2));
			assert!(!deduct_unbonded(&Alice, 69));
		});
	}

	#[test]
	fn refunding_balance_should_work() {
		with_externalities(&mut testing::externalities(1, 3, 1), || {
			<FreeBalance<T>>::insert(*Alice, 42);
			refund(&Alice, 69);
			assert_eq!(<FreeBalance<T>>::get(*Alice), 111);
		});
	}

	#[test]
	fn slashing_balance_should_work() {
		with_externalities(&mut testing::externalities(1, 3, 1), || {
			<FreeBalance<T>>::insert(*Alice, 111);
			reserve_balance(&Alice, 69);
			assert!(slash(&Alice, 69));
			assert_eq!(<FreeBalance<T>>::get(*Alice), 0);
			assert_eq!(<ReservedBalance<T>>::get(*Alice), 42);
		});
	}

	#[test]
	fn slashing_incomplete_balance_should_work() {
		with_externalities(&mut testing::externalities(1, 3, 1), || {
			<FreeBalance<T>>::insert(*Alice, 42);
			reserve_balance(&Alice, 21);
			assert!(!slash(&Alice, 69));
			assert_eq!(<FreeBalance<T>>::get(*Alice), 0);
			assert_eq!(<ReservedBalance<T>>::get(*Alice), 0);
		});
	}

	#[test]
	fn unreserving_balance_should_work() {
		with_externalities(&mut testing::externalities(1, 3, 1), || {
			<FreeBalance<T>>::insert(*Alice, 111);
			reserve_balance(&Alice, 111);
			unreserve_balance(&Alice, 42);
			assert_eq!(<ReservedBalance<T>>::get(*Alice), 69);
			assert_eq!(<FreeBalance<T>>::get(*Alice), 42);
		});
	}

	#[test]
	fn slashing_reserved_balance_should_work() {
		with_externalities(&mut testing::externalities(1, 3, 1), || {
			<FreeBalance<T>>::insert(*Alice, 111);
			reserve_balance(&Alice, 111);
			assert!(slash_reserved(&Alice, 42));
			assert_eq!(<ReservedBalance<T>>::get(*Alice), 69);
			assert_eq!(<FreeBalance<T>>::get(*Alice), 0);
		});
	}

	#[test]
	fn slashing_incomplete_reserved_balance_should_work() {
		with_externalities(&mut testing::externalities(1, 3, 1), || {
			<FreeBalance<T>>::insert(*Alice, 111);
			reserve_balance(&Alice, 42);
			assert!(!slash_reserved(&Alice, 69));
			assert_eq!(<FreeBalance<T>>::get(*Alice), 69);
			assert_eq!(<ReservedBalance<T>>::get(*Alice), 0);
		});
	}

	#[test]
	fn transferring_reserved_balance_should_work() {
		with_externalities(&mut testing::externalities(1, 3, 1), || {
			<FreeBalance<T>>::insert(*Alice, 111);
			reserve_balance(&Alice, 111);
			assert!(transfer_reserved_balance(&Alice, &Bob, 42));
			assert_eq!(<ReservedBalance<T>>::get(*Alice), 69);
			assert_eq!(<FreeBalance<T>>::get(*Alice), 0);
			assert_eq!(<ReservedBalance<T>>::get(*Bob), 0);
			assert_eq!(<FreeBalance<T>>::get(*Bob), 42);
		});
	}

	#[test]
	fn transferring_incomplete_reserved_balance_should_work() {
		with_externalities(&mut testing::externalities(1, 3, 1), || {
			<FreeBalance<T>>::insert(*Alice, 111);
			reserve_balance(&Alice, 42);
			assert!(!transfer_reserved_balance(&Alice, &Bob, 69));
			assert_eq!(<ReservedBalance<T>>::get(*Alice), 0);
			assert_eq!(<FreeBalance<T>>::get(*Alice), 69);
			assert_eq!(<ReservedBalance<T>>::get(*Bob), 0);
			assert_eq!(<FreeBalance<T>>::get(*Bob), 42);
		});
	}
}
*/
