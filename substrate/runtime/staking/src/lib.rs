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

#[cfg(feature = "std")]
extern crate serde;

#[cfg(test)]
#[macro_use]
extern crate serde_derive;

#[cfg(test)]
extern crate wabt;

#[macro_use]
extern crate substrate_runtime_support as runtime_support;

#[cfg_attr(feature = "std", macro_use)]
extern crate substrate_runtime_std as rstd;

extern crate substrate_codec as codec;
extern crate substrate_primitives;
extern crate substrate_runtime_contract as contract;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_runtime_primitives as primitives;
extern crate substrate_runtime_consensus as consensus;
extern crate substrate_runtime_sandbox as sandbox;
extern crate substrate_runtime_session as session;
extern crate substrate_runtime_system as system;

#[cfg(test)] use std::fmt::Debug;
use rstd::prelude::*;
use rstd::{cmp, result};
use rstd::cell::RefCell;
use rstd::collections::btree_map::{BTreeMap, Entry};
use codec::{Input, Slicable};
use runtime_support::{StorageValue, StorageMap, Parameter};
use runtime_support::dispatch::Result;
use primitives::traits::{Zero, One, Bounded, RefInto, SimpleArithmetic, Executable, MakePayment,
	As, Lookup};
use primitives::generic::{Member, MaybeSerializeDebug};

pub mod address;
#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

/// Number of account IDs stored per enum set.
const ENUM_SET_SIZE: usize = 64;

/// The byte to identify intention to reclaim an existing account index.
const RECLAIM_INDEX_MAGIC: usize = 0x69;

pub type Address<T> = address::Address<<T as system::Trait>::AccountId, <T as Trait>::AccountIndex>;

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

// MaybeSerializeDebug is workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
pub trait Trait: system::Trait + session::Trait + MaybeSerializeDebug {
	/// The balance of an account.
	type Balance: Parameter + SimpleArithmetic + Slicable + Default + Copy + As<Self::AccountIndex> + As<usize>;
	/// Function type to get the contract address given the creator.
	type DetermineContractAddress: ContractAddressFor<Self::AccountId>;
	/// Type used for storing an account's index; implies the maximum number of accounts the system
	/// can hold.
	type AccountIndex: Parameter + Member + Slicable + SimpleArithmetic + As<u8> + As<u16> + As<u32> + As<usize> + Copy;
}

decl_module! {
	pub struct Module<T: Trait>;
	pub enum Call where aux: T::PublicAux {
		fn transfer(aux, dest: Address<T>, value: T::Balance) -> Result = 0;
		fn stake(aux) -> Result = 1;
		fn unstake(aux) -> Result = 2;
	}
	pub enum PrivCall {
		fn set_sessions_per_era(new: T::BlockNumber) -> Result = 0;
		fn set_bonding_duration(new: T::BlockNumber) -> Result = 1;
		fn set_validator_count(new: u32) -> Result = 2;
		fn force_new_era() -> Result = 3;
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
	// The fee to be paid for making a transaction; the base.
	pub TransactionBaseFee get(transaction_base_fee): b"sta:basefee" => required T::Balance;
	// The fee to be paid for making a transaction; the per-byte portion.
	pub TransactionByteFee get(transaction_byte_fee): b"sta:bytefee" => required T::Balance;
	// The minimum amount allowed to keep an account open.
	pub ExistentialDeposit get(existential_deposit): b"sta:existential_deposit" => required T::Balance;
	// The amount credited to a destination's account whose index was reclaimed.
	pub ReclaimRebate get(reclaim_rebate): b"sta:reclaim_rebate" => required T::Balance;
	// The fee required to make a transfer.
	pub TransferFee get(transfer_fee): b"sta:transfer_fee" => required T::Balance;
	// The fee required to create an account. At least as big as ReclaimRebate.
	pub CreationFee get(creation_fee): b"sta:creation_fee" => required T::Balance;
	// The fee required to create a contract. At least as big as ReclaimRebate.
	pub ContractFee get(contract_fee): b"sta:contract_fee" => required T::Balance;

	// The current era index.
	pub CurrentEra get(current_era): b"sta:era" => required T::BlockNumber;
	// All the accounts with a desire to stake.
	pub Intentions: b"sta:wil:" => default Vec<T::AccountId>;
	// The next value of sessions per era.
	pub NextSessionsPerEra get(next_sessions_per_era): b"sta:nse" => T::BlockNumber;
	// The block number at which the era length last changed.
	pub LastEraLengthChange get(last_era_length_change): b"sta:lec" => default T::BlockNumber;

	// The next free enumeration set.
	pub NextEnumSet get(next_enum_set): b"sta:next_enum" => required T::AccountIndex;
	// The enumeration sets.
	pub EnumSet get(enum_set): b"sta:enum_set" => default map [ T::AccountIndex => Vec<T::AccountId> ];

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
	// TODO: keys should also be able to take AsRef<KeyType> to ensure Vec<u8>s can be passed as &[u8]
	// TODO: This will need to be stored as a double-map, with `T::AccountId` using the usual XX hash
	// function, and then the output of this concatenated onto a separate blake2 hash of the `Vec<u8>`
	// key. We will then need a `remove_prefix` in addition to `set_storage` which removes all
	// storage items with a particular prefix otherwise we'll suffer leakage with the removal
	// of smart contracts.
//	pub StorageOf: b"sta:sto:" => map [ T::AccountId => map(blake2) Vec<u8> => Vec<u8> ];
	pub StorageOf: b"sta:sto:" => map [ (T::AccountId, Vec<u8>) => Vec<u8> ];
}

enum NewAccountOutcome {
	NoHint,
	GoodHint,
	BadHint,
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

	/// Some result as `slash(who, value)` (but without the side-effects) assuming there are no
	/// balance changes in the meantime.
	pub fn can_slash(who: &T::AccountId, value: T::Balance) -> bool {
		Self::balance(who) >= value
	}

	/// Same result as `deduct_unbonded(who, value)` (but without the side-effects) assuming there
	/// are no balance changes in the meantime.
	pub fn can_deduct_unbonded(who: &T::AccountId, value: T::Balance) -> bool {
		if let LockStatus::Liquid = Self::unlock_block(who) {
			Self::free_balance(who) >= value
		} else {
			false
		}
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
	pub fn create(aux: &T::PublicAux, code: &[u8], value: T::Balance) -> Result {
		// commit anything that made it this far to storage
		if let Some(commit) = Self::effect_create(aux.ref_into(), code, value, &DirectAccountDb)? {
			<AccountDb<T>>::merge(&mut DirectAccountDb, commit);
		}
		Ok(())
	}

	// PUBLIC DISPATCH

	/// Transfer some unlocked staking balance to another staker.
	/// TODO: probably want to state gas-limit and gas-price.
	fn transfer(aux: &T::PublicAux, dest: Address<T>, value: T::Balance) -> Result {
		let dest = Self::lookup(dest)?;
		// commit anything that made it this far to storage
		if let Some(commit) = Self::effect_transfer(aux.ref_into(), &dest, value, &DirectAccountDb)? {
			<AccountDb<T>>::merge(&mut DirectAccountDb, commit);
		}
		Ok(())
	}

	/// Declare the desire to stake for the transactor.
	///
	/// Effects will be felt at the beginning of the next era.
	fn stake(aux: &T::PublicAux) -> Result {
		let mut intentions = <Intentions<T>>::get();
		// can't be in the list twice.
		ensure!(intentions.iter().find(|&t| t == aux.ref_into()).is_none(), "Cannot stake if already staked.");
		intentions.push(aux.ref_into().clone());
		<Intentions<T>>::put(intentions);
		<Bondage<T>>::insert(aux.ref_into(), T::BlockNumber::max_value());
		Ok(())
	}

	/// Retract the desire to stake for the transactor.
	///
	/// Effects will be felt at the beginning of the next era.
	fn unstake(aux: &T::PublicAux) -> Result {
		let mut intentions = <Intentions<T>>::get();
		let position = intentions.iter().position(|t| t == aux.ref_into()).ok_or("Cannot unstake if not already staked.")?;
		intentions.swap_remove(position);
		<Intentions<T>>::put(intentions);
		<Bondage<T>>::insert(aux.ref_into(), Self::current_era() + Self::bonding_duration());
		Ok(())
	}

	// PRIV DISPATCH

	/// Set the number of sessions in an era.
	fn set_sessions_per_era(new: T::BlockNumber) -> Result {
		<NextSessionsPerEra<T>>::put(&new);
		Ok(())
	}

	/// The length of the bonding duration in eras.
	fn set_bonding_duration(new: T::BlockNumber) -> Result {
		<BondingDuration<T>>::put(&new);
		Ok(())
	}

	/// The length of a staking era in sessions.
	fn set_validator_count(new: u32) -> Result {
		<ValidatorCount<T>>::put(&new);
		Ok(())
	}

	/// Force there to be a new era. This also forces a new session immediately after.
	fn force_new_era() -> Result {
		Self::new_era();
		<session::Module<T>>::rotate_session();
		Ok(())
	}

	// PUBLIC MUTABLES (DANGEROUS)

	/// Deduct from an unbonded balance. true if it happened.
	pub fn deduct_unbonded(who: &T::AccountId, value: T::Balance) -> Result {
		if let LockStatus::Liquid = Self::unlock_block(who) {
			let b = Self::free_balance(who);
			if b >= value {
				<FreeBalance<T>>::insert(who, b - value);
				return Ok(())
			}
		}
		Err("not enough liquid funds")
	}

	/// Refund some balance.
	pub fn refund(who: &T::AccountId, value: T::Balance) {
		<FreeBalance<T>>::insert(who, Self::free_balance(who) + value)
	}

	/// Will slash any balance, but prefer free over reserved.
	pub fn slash(who: &T::AccountId, value: T::Balance) -> Result {
		let free_balance = Self::free_balance(who);
		let free_slash = cmp::min(free_balance, value);
		<FreeBalance<T>>::insert(who, &(free_balance - free_slash));
		if free_slash < value {
			Self::slash_reserved(who, value - free_slash)
				.map_err(|_| "not enough funds")
		} else {
			Ok(())
		}
	}

	/// Moves `value` from balance to reserved balance.
	pub fn reserve_balance(who: &T::AccountId, value: T::Balance) -> Result {
		let b = Self::free_balance(who);
		if b < value {
			return Err("not enough free funds")
		}
		<FreeBalance<T>>::insert(who, b - value);
		<ReservedBalance<T>>::insert(who, Self::reserved_balance(who) + value);
		Ok(())
	}

	/// Moves `value` from reserved balance to balance.
	pub fn unreserve_balance(who: &T::AccountId, value: T::Balance) {
		let b = Self::reserved_balance(who);
		let value = cmp::min(b, value);
		<ReservedBalance<T>>::insert(who, b - value);
		<FreeBalance<T>>::insert(who, Self::free_balance(who) + value);
	}

	/// Moves `value` from reserved balance to balance.
	pub fn slash_reserved(who: &T::AccountId, value: T::Balance) -> Result {
		let b = Self::reserved_balance(who);
		let slash = cmp::min(b, value);
		<ReservedBalance<T>>::insert(who, b - slash);
		if value == slash {
			Ok(())
		} else {
			Err("not enough (reserved) funds")
		}
	}

	/// Moves `value` from reserved balance to balance.
	pub fn transfer_reserved_balance(slashed: &T::AccountId, beneficiary: &T::AccountId, value: T::Balance) -> Result {
		let b = Self::reserved_balance(slashed);
		let slash = cmp::min(b, value);
		<ReservedBalance<T>>::insert(slashed, b - slash);
		<FreeBalance<T>>::insert(beneficiary, Self::free_balance(beneficiary) + slash);
		if value == slash {
			Ok(())
		} else {
			Err("not enough (reserved) funds")
		}
	}

	/// Hook to be called after to transaction processing.
	pub fn check_new_era() {
		// check block number and call new_era if necessary.
		if (<system::Module<T>>::block_number() - Self::last_era_length_change()) % Self::era_length() == Zero::zero() {
			Self::new_era();
		}
	}

	/// The era has changed - enact new staking set.
	///
	/// NOTE: This always happens immediately before a session change to ensure that new validators
	/// get a chance to set their session keys.
	fn new_era() {
		// Increment current era.
		<CurrentEra<T>>::put(&(<CurrentEra<T>>::get() + One::one()));

		// Enact era length change.
		if let Some(next_spe) = Self::next_sessions_per_era() {
			if next_spe != Self::sessions_per_era() {
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

	/// Lookup an T::AccountIndex to get an Id, if there's one there.
	pub fn lookup_index(index: T::AccountIndex) -> Option<T::AccountId> {
		let usize_index: usize = As::<usize>::as_(index);
		let mut set = Self::enum_set(T::AccountIndex::sa(usize_index / ENUM_SET_SIZE));
		let i = usize_index % ENUM_SET_SIZE;
		if i < set.len() {
			Some(set.swap_remove(i))
		} else {
			None
		}
	}

	/// Register a new account (with existential balance).
	fn new_account(who: &T::AccountId, balance: T::Balance) -> NewAccountOutcome {
		let next_set_index = Self::next_enum_set();

		// A little easter-egg for reclaiming dead indexes..
		let ret = {
			let next_set_index: usize = next_set_index.as_();

			// we quantise the number of accounts so it stays constant over a reasonable
			// period of time.
			const QUANTIZATION: usize = 256;
			let quantized_account_count = (next_set_index * ENUM_SET_SIZE / QUANTIZATION + 1) * QUANTIZATION;
			// then modify the starting balance to be modulo this to allow it to potentially
			// identify an account index for reuse.
			let maybe_try_index = balance % T::Balance::sa(quantized_account_count * 256);
			let maybe_try_index = As::<T::AccountIndex>::as_(maybe_try_index);
			let maybe_try_index = As::<usize>::as_(maybe_try_index);

			// this identifier must end with magic byte 0x69 to trigger this check (a minor
			// optimisation to ensure we don't check most unintended account creations).
			if maybe_try_index % 256 == RECLAIM_INDEX_MAGIC {
				// reuse is probably intended. first, remove magic byte.
				let try_index = maybe_try_index / 256;

				// then check to see if this balance identifies a dead account index.
				let set_index = T::AccountIndex::sa(try_index / ENUM_SET_SIZE);
				let mut try_set = Self::enum_set(set_index);
				let item_index = try_index % ENUM_SET_SIZE;
				if item_index < try_set.len() {
					if Self::balance(&try_set[item_index]).is_zero() {
						// yup - this index refers to a dead account. can be reused.
						try_set[item_index] = who.clone();
						<EnumSet<T>>::insert(set_index, try_set);

						return NewAccountOutcome::GoodHint;
					}
				}
				NewAccountOutcome::BadHint
			} else {
				NewAccountOutcome::NoHint
			}
		};

		// insert normally as a back up
		let mut set_index = next_set_index;
		// defensive only: this loop should never iterate since we keep NextEnumSet up to date later.
		let mut set = loop {
			let set = Self::enum_set(set_index);
			if set.len() < ENUM_SET_SIZE {
				break set;
			}
			set_index += One::one();
		};

		// update set.
		set.push(who.clone());

		// keep NextEnumSet up to date
		if set.len() == ENUM_SET_SIZE {
			<NextEnumSet<T>>::put(set_index + One::one());
		}

		// write set.
		<EnumSet<T>>::insert(set_index, set);

		ret
	}

	/// Kill an account.
	fn kill_account(who: &T::AccountId) {
		<system::AccountNonce<T>>::remove(who);
		<FreeBalance<T>>::remove(who);
		<Bondage<T>>::remove(who);
		<CodeOf<T>>::remove(who);
		// TODO: <StorageOf<T>>::remove_prefix(address.clone());
	}
}

impl<T: Trait> Executable for Module<T> {
	fn execute() {
		Self::check_new_era();
	}
}

impl<T: Trait> Lookup<address::Address<T::AccountId, T::AccountIndex>> for Module<T> {
	type Target = T::AccountId;
	fn lookup(a: address::Address<T::AccountId, T::AccountIndex>) -> result::Result<T::AccountId, &'static str> {
		match a {
			address::Address::Id(i) => Ok(i),
			address::Address::Index(i) => <Module<T>>::lookup_index(i).ok_or("invalid account index"),
		}
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
	pub fn contract_created(b: T::Balance, c: Vec<u8>) -> Self {
		ChangeEntry { balance: Some(b), code: Some(c), storage: Default::default() }
	}
	pub fn balance_changed(b: T::Balance) -> Self {
		ChangeEntry { balance: Some(b), code: None, storage: Default::default() }
	}
}

type State<T> = BTreeMap<<T as system::Trait>::AccountId, ChangeEntry<T>>;

trait AccountDb<T: Trait> {
	fn get_storage(&self, account: &T::AccountId, location: &[u8]) -> Option<Vec<u8>>;
	fn get_code(&self, account: &T::AccountId) -> Vec<u8>;
	fn get_balance(&self, account: &T::AccountId) -> T::Balance;

	fn merge(&mut self, state: State<T>);
}

struct DirectAccountDb;
impl<T: Trait> AccountDb<T> for DirectAccountDb {
	fn get_storage(&self, account: &T::AccountId, location: &[u8]) -> Option<Vec<u8>> {
		<StorageOf<T>>::get(&(account.clone(), location.to_vec()))
	}
	fn get_code(&self, account: &T::AccountId) -> Vec<u8> {
		<CodeOf<T>>::get(account)
	}
	fn get_balance(&self, account: &T::AccountId) -> T::Balance {
		<FreeBalance<T>>::get(account)
	}
	fn merge(&mut self, s: State<T>) {
		let ed = <Module<T>>::existential_deposit();
		for (address, changed) in s.into_iter() {
			if let Some(balance) = changed.balance {
				// If the balance is too low, then the account is reaped.
				// NOTE: There are two balances for every account: `reserved_balance` and
				// `free_balance`. This contract subsystem only cares about the latter: whenever
				// the term "balance" is used *here* it should be assumed to mean "free balance"
				// in the rest of the module.
				// Free balance can never be less than ED. If that happens, it gets reduced to zero
				// and the account information relevant to this subsystem is deleted (i.e. the
				// account is reaped).
				// NOTE: This is orthogonal to the `Bondage` value that an account has, a high
				// value of which makes even the `free_balance` unspendable.
				// TODO: enforce this for the other balance-altering functions.
				if balance < ed {
					<Module<T>>::kill_account(&address);
					continue;
				} else {
					if !<FreeBalance<T>>::exists(&address) {
						let outcome = <Module<T>>::new_account(&address, balance);
						let credit = match outcome {
							NewAccountOutcome::GoodHint => balance + <Module<T>>::reclaim_rebate(),
							_ => balance,
						};
						<FreeBalance<T>>::insert(&address, credit);
					} else {
						<FreeBalance<T>>::insert(&address, balance);
					}
				}
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
}

struct OverlayAccountDb<'a, T: Trait + 'a> {
	local: RefCell<State<T>>,
	underlying: &'a AccountDb<T>,
}
impl<'a, T: Trait> OverlayAccountDb<'a, T> {
	fn new(underlying: &'a AccountDb<T>) -> OverlayAccountDb<'a, T> {
		OverlayAccountDb {
			local: RefCell::new(State::new()),
			underlying,
		}
	}

	fn into_state(self) -> State<T> {
		self.local.into_inner()
	}

	fn set_storage(&mut self, account: &T::AccountId, location: Vec<u8>, value: Option<Vec<u8>>) {
		self.local
			.borrow_mut()
			.entry(account.clone())
			.or_insert(Default::default())
			.storage
			.insert(location, value);
	}
	fn set_balance(&mut self, account: &T::AccountId, balance: T::Balance) {
		self.local
			.borrow_mut()
			.entry(account.clone())
			.or_insert(Default::default())
			.balance = Some(balance);
	}
}

impl<'a, T: Trait> AccountDb<T> for OverlayAccountDb<'a, T> {
	fn get_storage(&self, account: &T::AccountId, location: &[u8]) -> Option<Vec<u8>> {
		self.local
			.borrow()
			.get(account)
			.and_then(|a| a.storage.get(location))
			.cloned()
			.unwrap_or_else(|| self.underlying.get_storage(account, location))
	}
	fn get_code(&self, account: &T::AccountId) -> Vec<u8> {
		self.local
			.borrow()
			.get(account)
			.and_then(|a| a.code.clone())
			.unwrap_or_else(|| self.underlying.get_code(account))
	}
	fn get_balance(&self, account: &T::AccountId) -> T::Balance {
		self.local
			.borrow()
			.get(account)
			.and_then(|a| a.balance)
			.unwrap_or_else(|| self.underlying.get_balance(account))
	}
	fn merge(&mut self, s: State<T>) {
		let mut local = self.local.borrow_mut();

		for (address, changed) in s.into_iter() {
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
}

impl<T: Trait> Module<T> {
	fn effect_create<DB: AccountDb<T>>(
		transactor: &T::AccountId,
		code: &[u8],
		value: T::Balance,
		account_db: &DB,
	) -> result::Result<Option<State<T>>, &'static str> {
		let from_balance = account_db.get_balance(transactor);

		let liability = value + Self::contract_fee();

		if from_balance < liability {
			return Err("balance too low to send value");
		}
		if value < Self::existential_deposit() {
			return Err("value too low to create account");
		}
		if <Bondage<T>>::get(transactor) > <system::Module<T>>::block_number() {
			return Err("bondage too high to send value");
		}

		let dest = T::DetermineContractAddress::contract_address_for(code, transactor);

		// early-out if degenerate.
		if &dest == transactor {
			return Ok(None);
		}

		let mut local = BTreeMap::new();
		// two inserts are safe
		// note that we now know that `&dest != transactor` due to early-out before.
		local.insert(dest, ChangeEntry::contract_created(value, code.to_vec()));
		local.insert(transactor.clone(), ChangeEntry::balance_changed(from_balance - liability));
		Ok(Some(local))
	}

	fn effect_transfer<DB: AccountDb<T>>(
		transactor: &T::AccountId,
		dest: &T::AccountId,
		value: T::Balance,
		account_db: &DB,
	) -> result::Result<Option<State<T>>, &'static str> {
		let would_create = account_db.get_balance(transactor).is_zero();
		let fee = if would_create { Self::creation_fee() } else { Self::transfer_fee() };
		let liability = value + fee;

		let from_balance = account_db.get_balance(transactor);
		if from_balance < liability {
			return Err("balance too low to send value");
		}
		if would_create && value < Self::existential_deposit() {
			return Err("value too low to create account");
		}
		if <Bondage<T>>::get(transactor) > <system::Module<T>>::block_number() {
			return Err("bondage too high to send value");
		}

		let to_balance = account_db.get_balance(dest);
		if to_balance + value <= to_balance {
			return Err("destination balance too high to receive value");
		}

		// TODO: an additional fee, based upon gaslimit/gasprice.
		let gas_limit = 100_000;

		// TODO: consider storing upper-bound for contract's gas limit in fixed-length runtime
		// code in contract itself and use that.

		// Our local overlay: Should be used for any transfers and creates that happen internally.
		let mut overlay = OverlayAccountDb::new(account_db);

		if transactor != dest {
			overlay.set_balance(transactor, from_balance - liability);
			overlay.set_balance(dest, to_balance + value);
		}

		let dest_code = overlay.get_code(dest);
		let should_commit = if dest_code.is_empty() {
			true
		} else {
			// TODO: logging (logs are just appended into a notable storage-based vector and
			// cleared every block).
			let mut staking_ext = StakingExt {
				account_db: &mut overlay,
				account: dest.clone(),
			};
			contract::execute(&dest_code, &mut staking_ext, gas_limit).is_ok()
		};

		Ok(if should_commit {
			Some(overlay.into_state())
		} else {
			None
		})
	}
}

struct StakingExt<'a, 'b: 'a, T: Trait + 'b> {
	account_db: &'a mut OverlayAccountDb<'b, T>,
	account: T::AccountId,
}
impl<'a, 'b: 'a, T: Trait> contract::Ext for StakingExt<'a, 'b, T> {
	type AccountId = T::AccountId;
	type Balance = T::Balance;

	fn get_storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.account_db.get_storage(&self.account, key)
	}
	fn set_storage(&mut self, key: &[u8], value: Option<Vec<u8>>) {
		self.account_db.set_storage(&self.account, key.to_vec(), value);
	}
	fn create(&mut self, code: &[u8], value: Self::Balance) {
		if let Ok(Some(commit_state)) =
			Module::<T>::effect_create(&self.account, code, value, self.account_db)
		{
			self.account_db.merge(commit_state);
		}
	}
	fn transfer(&mut self, to: &Self::AccountId, value: Self::Balance) {
		if let Ok(Some(commit_state)) =
			Module::<T>::effect_transfer(&self.account, to, value, self.account_db)
		{
			self.account_db.merge(commit_state);
		}
	}
}

impl<T: Trait> MakePayment<T::AccountId> for Module<T> {
	fn make_payment(transactor: &T::AccountId, encoded_len: usize) -> Result {
		let b = Self::free_balance(transactor);
		let transaction_fee = Self::transaction_base_fee() + Self::transaction_byte_fee() * <T::Balance as As<usize>>::sa(encoded_len);
		if b < transaction_fee {
			return Err("not enough funds for transaction fee");
		}
		<FreeBalance<T>>::insert(transactor, b - transaction_fee);
		Ok(())
	}
}

#[cfg(any(feature = "std", test))]
pub struct DummyContractAddressFor;
#[cfg(any(feature = "std", test))]
impl ContractAddressFor<u64> for DummyContractAddressFor {
	fn contract_address_for(_code: &[u8], origin: &u64) -> u64 {
		origin + 1
	}
}

#[cfg(any(feature = "std", test))]
pub struct GenesisConfig<T: Trait> {
	pub sessions_per_era: T::BlockNumber,
	pub current_era: T::BlockNumber,
	pub balances: Vec<(T::AccountId, T::Balance)>,
	pub intentions: Vec<T::AccountId>,
	pub validator_count: u64,
	pub bonding_duration: T::BlockNumber,
	pub transaction_base_fee: T::Balance,
	pub transaction_byte_fee: T::Balance,
	pub transfer_fee: T::Balance,
	pub creation_fee: T::Balance,
	pub contract_fee: T::Balance,
	pub reclaim_rebate: T::Balance,
	pub existential_deposit: T::Balance,
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> GenesisConfig<T> where T::AccountId: From<u64> {
	pub fn simple() -> Self {
		use primitives::traits::As;
		GenesisConfig {
			sessions_per_era: T::BlockNumber::sa(2),
			current_era: T::BlockNumber::sa(0),
			balances: vec![(T::AccountId::from(1), T::Balance::sa(111))],
			intentions: vec![T::AccountId::from(1), T::AccountId::from(2), T::AccountId::from(3)],
			validator_count: 3,
			bonding_duration: T::BlockNumber::sa(0),
			transaction_base_fee: T::Balance::sa(0),
			transaction_byte_fee: T::Balance::sa(0),
			transfer_fee: T::Balance::sa(0),
			creation_fee: T::Balance::sa(0),
			contract_fee: T::Balance::sa(0),
			existential_deposit: T::Balance::sa(0),
			reclaim_rebate: T::Balance::sa(0),
		}
	}

	pub fn extended() -> Self {
		use primitives::traits::As;
		GenesisConfig {
			sessions_per_era: T::BlockNumber::sa(3),
			current_era: T::BlockNumber::sa(1),
			balances: vec![
				(T::AccountId::from(1), T::Balance::sa(10)),
				(T::AccountId::from(2), T::Balance::sa(20)),
				(T::AccountId::from(3), T::Balance::sa(30)),
				(T::AccountId::from(4), T::Balance::sa(40)),
				(T::AccountId::from(5), T::Balance::sa(50)),
				(T::AccountId::from(6), T::Balance::sa(60)),
				(T::AccountId::from(7), T::Balance::sa(1))
			],
			intentions: vec![T::AccountId::from(1), T::AccountId::from(2), T::AccountId::from(3)],
			validator_count: 3,
			bonding_duration: T::BlockNumber::sa(0),
			transaction_base_fee: T::Balance::sa(1),
			transaction_byte_fee: T::Balance::sa(0),
			transfer_fee: T::Balance::sa(0),
			creation_fee: T::Balance::sa(0),
			contract_fee: T::Balance::sa(0),
			existential_deposit: T::Balance::sa(0),
			reclaim_rebate: T::Balance::sa(0),
		}
	}
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> Default for GenesisConfig<T> {
	fn default() -> Self {
		use primitives::traits::As;
		GenesisConfig {
			sessions_per_era: T::BlockNumber::sa(1000),
			current_era: T::BlockNumber::sa(0),
			balances: vec![],
			intentions: vec![],
			validator_count: 0,
			bonding_duration: T::BlockNumber::sa(1000),
			transaction_base_fee: T::Balance::sa(0),
			transaction_byte_fee: T::Balance::sa(0),
			transfer_fee: T::Balance::sa(0),
			creation_fee: T::Balance::sa(0),
			contract_fee: T::Balance::sa(0),
			existential_deposit: T::Balance::sa(0),
			reclaim_rebate: T::Balance::sa(0),
		}
	}
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> primitives::BuildExternalities for GenesisConfig<T> {
	fn build_externalities(self) -> runtime_io::TestExternalities {
		use runtime_io::twox_128;
		use codec::Slicable;

		let total_stake: T::Balance = self.balances.iter().fold(Zero::zero(), |acc, &(_, n)| acc + n);

		let mut r: runtime_io::TestExternalities = map![
			twox_128(<NextEnumSet<T>>::key()).to_vec() => T::AccountIndex::sa(self.balances.len() / ENUM_SET_SIZE).encode(),
			twox_128(<Intentions<T>>::key()).to_vec() => self.intentions.encode(),
			twox_128(<SessionsPerEra<T>>::key()).to_vec() => self.sessions_per_era.encode(),
			twox_128(<ValidatorCount<T>>::key()).to_vec() => self.validator_count.encode(),
			twox_128(<BondingDuration<T>>::key()).to_vec() => self.bonding_duration.encode(),
			twox_128(<TransactionBaseFee<T>>::key()).to_vec() => self.transaction_base_fee.encode(),
			twox_128(<TransactionByteFee<T>>::key()).to_vec() => self.transaction_byte_fee.encode(),
			twox_128(<TransferFee<T>>::key()).to_vec() => self.transfer_fee.encode(),
			twox_128(<CreationFee<T>>::key()).to_vec() => self.creation_fee.encode(),
			twox_128(<ContractFee<T>>::key()).to_vec() => self.contract_fee.encode(),
			twox_128(<ExistentialDeposit<T>>::key()).to_vec() => self.existential_deposit.encode(),
			twox_128(<ReclaimRebate<T>>::key()).to_vec() => self.reclaim_rebate.encode(),
			twox_128(<CurrentEra<T>>::key()).to_vec() => self.current_era.encode(),
			twox_128(<TotalStake<T>>::key()).to_vec() => total_stake.encode()
		];

		let ids: Vec<_> = self.balances.iter().map(|x| x.0.clone()).collect();
		for i in 0..(ids.len() + ENUM_SET_SIZE - 1) / ENUM_SET_SIZE {
			r.insert(twox_128(&<EnumSet<T>>::key_for(T::AccountIndex::sa(i))).to_vec(),
				ids[i * ENUM_SET_SIZE..ids.len().min((i + 1) * ENUM_SET_SIZE)].to_owned().encode());
		}
		for (who, value) in self.balances.into_iter() {
			r.insert(twox_128(&<FreeBalance<T>>::key_for(who)).to_vec(), value.encode());
		}
		r
	}
}
