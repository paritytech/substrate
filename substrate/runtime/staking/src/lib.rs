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

#[cfg(feature = "std")]
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
extern crate substrate_runtime_timestamp as timestamp;

#[cfg(test)] use std::fmt::Debug;
use account_db::State;
use rstd::prelude::*;
use rstd::{cmp, result};
use rstd::collections::btree_map::BTreeMap;
use codec::{Input, Slicable};
use runtime_support::{StorageValue, StorageMap, Parameter};
use runtime_support::dispatch::Result;
use session::OnSessionChange;
use primitives::traits::{Zero, One, Bounded, RefInto, SimpleArithmetic, Executable, MakePayment,
	As, AuxLookup, Hashing as HashingT, Member};
use address::Address as RawAddress;

pub mod address;
mod mock;
mod tests;
mod genesis_config;
mod account_db;

#[cfg(feature = "std")]
pub use genesis_config::GenesisConfig;

pub use account_db::*;

/// Number of account IDs stored per enum set.
const ENUM_SET_SIZE: usize = 64;

/// The byte to identify intention to reclaim an existing account index.
const RECLAIM_INDEX_MAGIC: usize = 0x69;

pub type Address<T> = RawAddress<<T as system::Trait>::AccountId, <T as Trait>::AccountIndex>;

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

#[cfg(feature = "std")]
pub struct DummyContractAddressFor;
#[cfg(feature = "std")]
impl ContractAddressFor<u64> for DummyContractAddressFor {
	fn contract_address_for(_code: &[u8], origin: &u64) -> u64 {
		origin + 1
	}
}

impl<Hashing, AccountId> ContractAddressFor<AccountId> for Hashing where
	Hashing: HashingT,
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
	type Balance: Parameter + SimpleArithmetic + Slicable + Default + Copy + As<Self::AccountIndex> + As<usize>;
	/// Function type to get the contract address given the creator.
	type DetermineContractAddress: ContractAddressFor<Self::AccountId>;
	/// Type used for storing an account's index; implies the maximum number of accounts the system
	/// can hold.
	type AccountIndex: Parameter + Member + Slicable + SimpleArithmetic + As<u8> + As<u16> + As<u32> + As<usize> + Copy;
}

decl_module! {
	pub struct Module<T: Trait>;

	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	pub enum Call where aux: T::PublicAux {
		fn transfer(aux, dest: RawAddress<T::AccountId, T::AccountIndex>, value: T::Balance) -> Result = 0;
		fn stake(aux) -> Result = 1;
		fn unstake(aux) -> Result = 2;
	}

	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
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

	// Maximum reward, per validator, that is provided per acceptable session.
	pub SessionReward get(session_reward): b"sta:session_reward" => required T::Balance;
	// Slash, per validator that is taken per abnormal era end.
	pub EarlyEraSlash get(early_era_slash): b"sta:early_era_slash" => required T::Balance;

	// The current era index.
	pub CurrentEra get(current_era): b"sta:era" => required T::BlockNumber;
	// All the accounts with a desire to stake.
	pub Intentions: b"sta:wil:" => default Vec<T::AccountId>;
	// The next value of sessions per era.
	pub NextSessionsPerEra get(next_sessions_per_era): b"sta:nse" => T::BlockNumber;
	// The session index at which the era length last changed.
	pub LastEraLengthChange get(last_era_length_change): b"sta:lec" => default T::BlockNumber;

	// The next free enumeration set.
	pub NextEnumSet get(next_enum_set): b"sta:next_enum" => required T::AccountIndex;
	// The enumeration sets.
	pub EnumSet get(enum_set): b"sta:enum_set" => default map [ T::AccountIndex => Vec<T::AccountId> ];

	// The "free" balance of a given account.
	//
	// This is the only balance that matters in terms of most operations on tokens. It is
	// alone used to determine the balance when in the contract execution environment. When this
	// balance falls below the value of `ExistentialDeposit`, then the "current account" is
	// deleted: specifically, `Bondage`, `StorageOf`, `CodeOf` and `FreeBalance`.
	//
	// `system::AccountNonce` is also deleted if `ReservedBalance` is also zero (it also gets
	// collapsed to zero if it ever becomes less than `ExistentialDeposit`.
	pub FreeBalance get(free_balance): b"sta:bal:" => default map [ T::AccountId => T::Balance ];

	// The amount of the balance of a given account that is exterally reserved; this can still get
	// slashed, but gets slashed last of all.
	//
	// This balance is a "reserve" balance that other subsystems use in order to set aside tokens
	// that are still "owned" by the account holder, but which are unspendable. This is different
	// and wholly unrelated to the `Bondage` system used for staking.
	//
	// When this balance falls below the value of `ExistentialDeposit`, then this "reserve account"
	// is deleted: specifically, `ReservedBalance`.
	//
	// `system::AccountNonce` is also deleted if `FreeBalance` is also zero (it also gets
	// collapsed to zero if it ever becomes less than `ExistentialDeposit`.
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
	pub fn voting_balance(who: &T::AccountId) -> T::Balance {
		Self::free_balance(who) + Self::reserved_balance(who)
	}

	/// Some result as `slash(who, value)` (but without the side-effects) assuming there are no
	/// balance changes in the meantime and only the reserved balance is not taken into account.
	pub fn can_slash(who: &T::AccountId, value: T::Balance) -> bool {
		Self::free_balance(who) >= value
	}

	/// Same result as `reserve(who, value)` (but without the side-effects) assuming there
	/// are no balance changes in the meantime.
	pub fn can_reserve(who: &T::AccountId, value: T::Balance) -> bool {
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
		<session::Module<T>>::rotate_session(false);
		Ok(())
	}

	// PUBLIC MUTABLES (DANGEROUS)

	/// Set the free balance of an account to some new value. Will enforce ExistentialDeposit law,
	/// anulling the account as needed.
	pub fn set_reserved_balance(who: &T::AccountId, balance: T::Balance) -> bool {
		if balance < Self::existential_deposit() {
			Self::on_reserved_too_low(who);
			false
		} else {
			<ReservedBalance<T>>::insert(who, balance);
			true
		}
	}

	/// Set the free balance of an account to some new value. Will enforce ExistentialDeposit
	/// law anulling the account as needed.
	///
	/// Doesn't do any preparatory work for creating a new account, so should only be used when it
	/// is known that the account already exists.
	pub fn set_free_balance(who: &T::AccountId, balance: T::Balance) -> bool {
		// Commented out for no - but consider it instructive.
//		assert!(!Self::voting_balance(who).is_zero());
		if balance < Self::existential_deposit() {
			Self::on_free_too_low(who);
			false
		} else {
			<FreeBalance<T>>::insert(who, balance);
			true
		}
	}

	/// Deducts up to `value` from the combined balance of `who`, preferring to deduct from the
	/// free balance. This function cannot fail.
	///
	/// As much funds up to `value` will be deducted as possible. If this is less than `value`,
	/// then `Some(remaining)` will be retutned. Full completion is given by `None`.
	pub fn slash(who: &T::AccountId, value: T::Balance) -> Option<T::Balance> {
		let free_balance = Self::free_balance(who);
		let free_slash = cmp::min(free_balance, value);
		Self::set_free_balance(who, free_balance - free_slash);
		if free_slash < value {
			Self::slash_reserved(who, value - free_slash)
		} else {
			None
		}
	}

	/// Adds up to `value` to the free balance of `who`.
	///
	/// If `who` doesn't exist, nothing is done and an Err returned.
	pub fn reward(who: &T::AccountId, value: T::Balance) -> Result {
		if Self::voting_balance(who).is_zero() {
			return Err("beneficiary account must pre-exist");
		}
		Self::set_free_balance(who, Self::free_balance(who) + value);
		Ok(())
	}

	/// Moves `value` from balance to reserved balance.
	///
	/// If the free balance is lower than `value`, then no funds will be moved and an `Err` will
	/// be returned to notify of this. This is different behaviour to `unreserve`.
	pub fn reserve(who: &T::AccountId, value: T::Balance) -> Result {
		let b = Self::free_balance(who);
		if b < value {
			return Err("not enough free funds")
		}
		if Self::unlock_block(who) != LockStatus::Liquid {
			return Err("free funds are still bonded")
		}
		Self::set_reserved_balance(who, Self::reserved_balance(who) + value);
		Self::set_free_balance(who, b - value);
		Ok(())
	}

	/// Moves up to `value` from reserved balance to balance. This function cannot fail.
	///
	/// As much funds up to `value` will be deducted as possible. If this is less than `value`,
	/// then `Some(remaining)` will be retutned. Full completion is given by `None`.
	/// NOTE: This is different to `reserve`.
	pub fn unreserve(who: &T::AccountId, value: T::Balance) -> Option<T::Balance> {
		let b = Self::reserved_balance(who);
		let actual = cmp::min(b, value);
		Self::set_free_balance(who, Self::free_balance(who) + actual);
		Self::set_reserved_balance(who, b - actual);
		if actual == value {
			None
		} else {
			Some(value - actual)
		}
	}

	/// Deducts up to `value` from reserved balance of `who`. This function cannot fail.
	///
	/// As much funds up to `value` will be deducted as possible. If this is less than `value`,
	/// then `Some(remaining)` will be retutned. Full completion is given by `None`.
	pub fn slash_reserved(who: &T::AccountId, value: T::Balance) -> Option<T::Balance> {
		let b = Self::reserved_balance(who);
		let slash = cmp::min(b, value);
		Self::set_reserved_balance(who, b - slash);
		if value == slash {
			None
		} else {
			Some(value - slash)
		}
	}

	/// Moves up to `value` from reserved balance of account `slashed` to free balance of account
	/// `beneficiary`. `beneficiary` must exist for this to succeed. If it does not, `Err` will be
	/// returned.
	///
	/// As much funds up to `value` will be moved as possible. If this is less than `value`, then
	/// `Ok(Some(remaining))` will be retutned. Full completion is given by `Ok(None)`.
	pub fn transfer_reserved(
		slashed: &T::AccountId,
		beneficiary: &T::AccountId,
		value: T::Balance
	) -> result::Result<Option<T::Balance>, &'static str> {
		if Self::voting_balance(beneficiary).is_zero() {
			return Err("beneficiary account must pre-exist");
		}
		let b = Self::reserved_balance(slashed);
		let slash = cmp::min(b, value);
		Self::set_free_balance(beneficiary, Self::free_balance(beneficiary) + slash);
		Self::set_reserved_balance(slashed, b - slash);
		if value == slash {
			Ok(None)
		} else {
			Ok(Some(value - slash))
		}
	}

	/// Session has just changed. We need to determine whether we pay a reward, slash and/or
	/// move to a new era.
	fn new_session(normal_rotation: bool, actual_elapsed: T::Moment) {
		let session_index = <session::Module<T>>::current_index();

		if normal_rotation {
			// reward
			let ideal_elapsed = <session::Module<T>>::ideal_session_duration();
			let percent: usize = (T::Moment::sa(65536usize) * ideal_elapsed.clone() / actual_elapsed.max(ideal_elapsed)).as_();
			let reward = Self::session_reward() * T::Balance::sa(percent) / T::Balance::sa(65536usize);
			// apply good session reward
			for v in <session::Module<T>>::validators().iter() {
				let _ = Self::reward(v, reward);	// will never fail as validator accounts must be created, but even if it did, it's just a missed reward.
			}
		} else {
			// slash
			let early_era_slash = Self::early_era_slash();
			for v in <session::Module<T>>::validators().iter() {
				Self::slash(v, early_era_slash);
			}
		}
		if ((session_index - Self::last_era_length_change()) % Self::sessions_per_era()).is_zero() || !normal_rotation {
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
				<LastEraLengthChange<T>>::put(&<session::Module<T>>::current_index());
			}
		}

		// evaluate desired staking amounts and nominations and optimise to find the best
		// combination of validators, then use session::internal::set_validators().
		// for now, this just orders would-be stakers by their balances and chooses the top-most
		// <ValidatorCount<T>>::get() of them.
		let mut intentions = <Intentions<T>>::get()
			.into_iter()
			.map(|v| (Self::voting_balance(&v), v))
			.collect::<Vec<_>>();
		intentions.sort_unstable_by(|&(ref b1, _), &(ref b2, _)| b2.cmp(&b1));
		<session::Module<T>>::set_validators(
			&intentions.into_iter()
				.map(|(_, v)| v)
				.take(<ValidatorCount<T>>::get() as usize)
				.collect::<Vec<_>>()
		);
	}

	fn enum_set_size() -> T::AccountIndex {
		T::AccountIndex::sa(ENUM_SET_SIZE)
	}

	/// Lookup an T::AccountIndex to get an Id, if there's one there.
	pub fn lookup_index(index: T::AccountIndex) -> Option<T::AccountId> {
		let enum_set_size = Self::enum_set_size();
		let set = Self::enum_set(index / enum_set_size);
		let i: usize = (index % enum_set_size).as_();
		set.get(i).map(|x| x.clone())
	}

	/// `true` if the account `index` is ready for reclaim.
	pub fn can_reclaim(try_index: T::AccountIndex) -> bool {
		let enum_set_size = Self::enum_set_size();
		let try_set = Self::enum_set(try_index / enum_set_size);
		let i = (try_index % enum_set_size).as_();
		i < try_set.len() && Self::voting_balance(&try_set[i]).is_zero()
	}

	/// Register a new account (with existential balance).
	fn new_account(who: &T::AccountId, balance: T::Balance) -> NewAccountOutcome {
		let enum_set_size = Self::enum_set_size();
		let next_set_index = Self::next_enum_set();
		let reclaim_index_magic = T::AccountIndex::sa(RECLAIM_INDEX_MAGIC);
		let reclaim_index_modulus = T::AccountIndex::sa(256usize);
		let quantization = T::AccountIndex::sa(256usize);

		// A little easter-egg for reclaiming dead indexes..
		let ret = {
			// we quantise the number of accounts so it stays constant over a reasonable
			// period of time.
			let quantized_account_count: T::AccountIndex = (next_set_index * enum_set_size / quantization + One::one()) * quantization;
			// then modify the starting balance to be modulo this to allow it to potentially
			// identify an account index for reuse.
			let maybe_try_index = balance % <T::Balance as As<T::AccountIndex>>::sa(quantized_account_count * reclaim_index_modulus);
			let maybe_try_index = As::<T::AccountIndex>::as_(maybe_try_index);

			// this identifier must end with magic byte 0x69 to trigger this check (a minor
			// optimisation to ensure we don't check most unintended account creations).
			if maybe_try_index % reclaim_index_modulus == reclaim_index_magic {
				// reuse is probably intended. first, remove magic byte.
				let try_index = maybe_try_index / reclaim_index_modulus;

				// then check to see if this balance identifies a dead account index.
				let set_index = try_index / enum_set_size;
				let mut try_set = Self::enum_set(set_index);
				let item_index = (try_index % enum_set_size).as_();
				if item_index < try_set.len() {
					if Self::voting_balance(&try_set[item_index]).is_zero() {
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

	/// Kill an account's free portion.
	fn on_free_too_low(who: &T::AccountId) {
		<FreeBalance<T>>::remove(who);
		<Bondage<T>>::remove(who);
		<CodeOf<T>>::remove(who);
		// TODO: <StorageOf<T>>::remove_prefix(address.clone());

		if Self::reserved_balance(who).is_zero() {
			<system::AccountNonce<T>>::remove(who);
		}
	}

	/// Kill an account's reserved portion.
	fn on_reserved_too_low(who: &T::AccountId) {
		<ReservedBalance<T>>::remove(who);
		if Self::free_balance(who).is_zero() {
			<system::AccountNonce<T>>::remove(who);
		}
	}

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

impl<T: Trait> Executable for Module<T> {
	fn execute() {
	}
}

impl<T: Trait> OnSessionChange<T::Moment> for Module<T> {
	fn on_session_change(normal_rotation: bool, elapsed: T::Moment) {
		Self::new_session(normal_rotation, elapsed);
	}
}

impl<T: Trait> AuxLookup for Module<T> {
	type Source = address::Address<T::AccountId, T::AccountIndex>;
	type Target = T::AccountId;
	fn lookup(a: Self::Source) -> result::Result<Self::Target, &'static str> {
		match a {
			address::Address::Id(i) => Ok(i),
			address::Address::Index(i) => <Module<T>>::lookup_index(i).ok_or("invalid account index"),
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
