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

#[macro_use]
extern crate substrate_codec_derive;

extern crate substrate_codec as codec;
extern crate substrate_primitives;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_runtime_primitives as primitives;
extern crate substrate_runtime_consensus as consensus;
extern crate substrate_runtime_sandbox as sandbox;
extern crate substrate_runtime_session as session;
extern crate substrate_runtime_system as system;
extern crate substrate_runtime_timestamp as timestamp;

#[cfg(test)] use std::fmt::Debug;
use rstd::prelude::*;
use rstd::{cmp, result};
use codec::{Encode, Decode, Codec, Input, Output};
use runtime_support::{StorageValue, StorageMap, Parameter};
use runtime_support::dispatch::Result;
use session::OnSessionChange;
use primitives::traits::{Zero, One, Bounded, RefInto, SimpleArithmetic, Executable, MakePayment,
	As, AuxLookup, Member, CheckedAdd, CheckedSub, MaybeEmpty};
use address::Address as RawAddress;

mod mock;

pub mod address;
mod tests;
mod genesis_config;

#[cfg(feature = "std")]
pub use genesis_config::GenesisConfig;

const DEFAULT_MINIMUM_VALIDATOR_COUNT: usize = 4;

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

/// The account was the given id was killed.
pub trait OnAccountKill<AccountId> {
	/// The account was the given id was killed.
	fn on_account_kill(who: &AccountId);
}

impl<AccountId> OnAccountKill<AccountId> for () {
	fn on_account_kill(_who: &AccountId) {}
}

/// Preference of what happens on a slash event.
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
#[derive(Encode, Decode, Eq, PartialEq, Clone, Copy)]
pub struct SlashPreference {
	/// Validator should ensure this many more slashes than is necessary before being unstaked.
	pub unstake_threshold: u32,
}

impl Default for SlashPreference {
	fn default() -> Self {
		SlashPreference {
			unstake_threshold: 3,
		}
	}
}

pub trait Trait: system::Trait + session::Trait {
	/// The allowed extrinsic position for `missed_proposal` inherent.
//	const NOTE_MISSED_PROPOSAL_POSITION: u32;	// TODO: uncomment when removed from session::Trait

	/// The balance of an account.
	type Balance: Parameter + SimpleArithmetic + Codec + Default + Copy + As<Self::AccountIndex> + As<usize> + As<u64>;
	/// Type used for storing an account's index; implies the maximum number of accounts the system
	/// can hold.
	type AccountIndex: Parameter + Member + Codec + SimpleArithmetic + As<u8> + As<u16> + As<u32> + As<u64> + As<usize> + Copy;
	/// A function which is invoked when the given account is dead.
	///
	/// Gives a chance to clean up resources associated with the given account.
	type OnAccountKill: OnAccountKill<Self::AccountId>;
}

decl_module! {
	pub struct Module<T: Trait>;

	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	pub enum Call where aux: T::PublicAux {
		fn transfer(aux, dest: RawAddress<T::AccountId, T::AccountIndex>, value: T::Balance) -> Result = 0;
		fn stake(aux) -> Result = 1;
		fn unstake(aux, intentions_index: u32) -> Result = 2;
		fn nominate(aux, target: RawAddress<T::AccountId, T::AccountIndex>) -> Result = 3;
		fn unnominate(aux, target_index: u32) -> Result = 4;
		fn register_slash_preference(aux, intentions_index: u32, p: SlashPreference) -> Result = 5;
		fn note_missed_proposal(aux, offline_val_indices: Vec<u32>) -> Result = 6;
	}

	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	pub enum PrivCall {
		fn set_sessions_per_era(new: T::BlockNumber) -> Result = 0;
		fn set_bonding_duration(new: T::BlockNumber) -> Result = 1;
		fn set_validator_count(new: u32) -> Result = 2;
		fn force_new_era(apply_rewards: bool) -> Result = 3;
		fn set_offline_slash_grace(new: u32) -> Result = 4;
		fn set_balance(who: RawAddress<T::AccountId, T::AccountIndex>, free: T::Balance, reserved: T::Balance) -> Result = 5;
	}
}

decl_storage! {
	trait Store for Module<T: Trait>;

	// The length of the bonding duration in eras.
	pub BondingDuration get(bonding_duration): b"sta:loc" => required T::BlockNumber;
	// The ideal number of staking participants.
	pub ValidatorCount get(validator_count): b"sta:vac" => required u32;
	// Minimum number of staking participants before emergency conditions are imposed.
	pub MinimumValidatorCount: b"sta:minimum_validator_count" => u32;
	// The length of a staking era in sessions.
	pub SessionsPerEra get(sessions_per_era): b"sta:spe" => required T::BlockNumber;
	// The total amount of stake on the system.
	// TODO: this doesn't actually track total stake yet - it should do.
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
	// Maximum reward, per validator, that is provided per acceptable session.
	pub SessionReward get(session_reward): b"sta:session_reward" => required T::Balance;
	// Slash, per validator that is taken per abnormal era end.
	pub EarlyEraSlash get(early_era_slash): b"sta:early_era_slash" => required T::Balance;
	// Number of instances of offline reports before slashing begins for validators.
	pub OfflineSlashGrace get(offline_slash_grace): b"sta:offline_slash_grace" => default u32;

	// The current era index.
	pub CurrentEra get(current_era): b"sta:era" => required T::BlockNumber;
	// Preference over how many times the validator should get slashed for being offline before they are automatically unstaked.
	pub SlashPreferenceOf get(slash_preference_of): b"sta:slash_preference_of" => default map [ T::AccountId => SlashPreference ];
	// All the accounts with a desire to stake.
	pub Intentions get(intentions): b"sta:wil:" => default Vec<T::AccountId>;
	// All nominator -> nominee relationships.
	pub Nominating get(nominating): b"sta:nominating" => map [ T::AccountId => T::AccountId ];
	// Nominators for a particular account.
	pub NominatorsFor get(nominators_for): b"sta:nominators_for" => default map [ T::AccountId => Vec<T::AccountId> ];
	// Nominators for a particular account that is in action right now.
	pub CurrentNominatorsFor get(current_nominators_for): b"sta:current_nominators_for" => default map [ T::AccountId => Vec<T::AccountId> ];
	// The next value of sessions per era.
	pub NextSessionsPerEra get(next_sessions_per_era): b"sta:nse" => T::BlockNumber;
	// The session index at which the era length last changed.
	pub LastEraLengthChange get(last_era_length_change): b"sta:lec" => default T::BlockNumber;
	// The current era stake threshold
	pub StakeThreshold get(stake_threshold): b"sta:stake_threshold" => required T::Balance;

	// The number of times a given validator has been reported offline. This gets decremented by one each era that passes.
	pub SlashCount get(slash_count): b"sta:slash_count" => default map [ T::AccountId => u32 ];

	// The next free enumeration set.
	pub NextEnumSet get(next_enum_set): b"sta:next_enum" => required T::AccountIndex;
	// The enumeration sets.
	pub EnumSet get(enum_set): b"sta:enum_set" => default map [ T::AccountIndex => Vec<T::AccountId> ];

	// We are forcing a new era.
	pub ForcingNewEra get(forcing_new_era): b"sta:forcing_new_era" => ();

	// The "free" balance of a given account.
	//
	// This is the only balance that matters in terms of most operations on tokens. It is
	// alone used to determine the balance when in the contract execution environment. When this
	// balance falls below the value of `ExistentialDeposit`, then the "current account" is
	// deleted: specifically, `Bondage` and `FreeBalance`. Furthermore, `OnAccountKill` callback
	// is invoked, giving a chance to external modules to cleanup data associated with
	// the deleted account.
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
}

enum NewAccountOutcome {
	NoHint,
	GoodHint,
	BadHint,
}

/// Outcome of a balance update.
pub enum UpdateBalanceOutcome {
	/// Account balance was simply updated.
	Updated,
	/// The update has led to killing of the account.
	AccountKilled,
}

impl<T: Trait> Module<T> {

	// PUBLIC IMMUTABLES

	pub fn minimum_validator_count() -> usize {
		<MinimumValidatorCount<T>>::get().map(|v| v as usize).unwrap_or(DEFAULT_MINIMUM_VALIDATOR_COUNT)
	}

	/// The length of a staking era in blocks.
	pub fn era_length() -> T::BlockNumber {
		Self::sessions_per_era() * <session::Module<T>>::length()
	}

	/// The combined balance of `who`.
	pub fn voting_balance(who: &T::AccountId) -> T::Balance {
		Self::free_balance(who) + Self::reserved_balance(who)
	}

	/// Balance of a (potential) validator that includes all nominators.
	pub fn nomination_balance(who: &T::AccountId) -> T::Balance {
		Self::nominators_for(who).iter()
			.map(Self::voting_balance)
			.fold(Zero::zero(), |acc, x| acc + x)
	}

	/// The total balance that can be slashed from an account.
	pub fn slashable_balance(who: &T::AccountId) -> T::Balance {
		Self::nominators_for(who).iter()
			.map(Self::voting_balance)
			.fold(Self::voting_balance(who), |acc, x| acc + x)
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

	/// The block at which the `who`'s funds become entirely liquid.
	pub fn unlock_block(who: &T::AccountId) -> LockStatus<T::BlockNumber> {
		match Self::bondage(who) {
			i if i == T::BlockNumber::max_value() => LockStatus::Staked,
			i if i <= <system::Module<T>>::block_number() => LockStatus::Liquid,
			i => LockStatus::LockedUntil(i),
		}
	}

	/// Lookup an address to get an Id, if there's one there.
	pub fn lookup_address(a: address::Address<T::AccountId, T::AccountIndex>) -> Option<T::AccountId> {
		match a {
			address::Address::Id(i) => Some(i),
			address::Address::Index(i) => Self::lookup_index(i),
		}
	}

	// PUBLIC DISPATCH

	/// Transfer some unlocked staking balance to another staker.
	pub fn transfer(aux: &T::PublicAux, dest: Address<T>, value: T::Balance) -> Result {
		let dest = Self::lookup(dest)?;

		let transactor = aux.ref_into();
		let from_balance = Self::free_balance(transactor);
		let would_create = from_balance.is_zero();
		let fee = if would_create { Self::creation_fee() } else { Self::transfer_fee() };
		let liability = value + fee;

		let new_from_balance = match from_balance.checked_sub(&liability) {
			Some(b) => b,
			None => return Err("balance too low to send value"),
		};
		if would_create && value < Self::existential_deposit() {
			return Err("value too low to create account");
		}
		if <Bondage<T>>::get(transactor) > <system::Module<T>>::block_number() {
			return Err("bondage too high to send value");
		}

		let to_balance = Self::free_balance(&dest);
		let new_to_balance = match to_balance.checked_add(&value) {
			Some(b) => b,
			None => return Err("destination balance too high to receive value"),
		};

		if transactor != &dest {
			Self::set_free_balance(transactor, new_from_balance);			
			Self::decrease_total_stake_by(fee);
			Self::set_free_balance_creating(&dest, new_to_balance);
		}

		Ok(())
	}

	/// Declare the desire to stake for the transactor.
	///
	/// Effects will be felt at the beginning of the next era.
	fn stake(aux: &T::PublicAux) -> Result {
		let aux = aux.ref_into();
		ensure!(Self::nominating(aux).is_none(), "Cannot stake if already nominating.");
		let mut intentions = <Intentions<T>>::get();
		// can't be in the list twice.
		ensure!(intentions.iter().find(|&t| t == aux).is_none(), "Cannot stake if already staked.");
		intentions.push(aux.clone());
		<Intentions<T>>::put(intentions);
		<Bondage<T>>::insert(aux, T::BlockNumber::max_value());
		Ok(())
	}

	/// Retract the desire to stake for the transactor.
	///
	/// Effects will be felt at the beginning of the next era.
	fn unstake(aux: &T::PublicAux, intentions_index: u32) -> Result {
		// unstake fails in degenerate case of having too few existing staked parties
		if Self::intentions().len() <= Self::minimum_validator_count() {
			return Err("cannot unstake when there are too few staked participants")
		}
		Self::apply_unstake(aux.ref_into(), intentions_index as usize)
	}

	fn nominate(aux: &T::PublicAux, target: RawAddress<T::AccountId, T::AccountIndex>) -> Result {
		let target = Self::lookup(target)?;
		let aux = aux.ref_into();

		ensure!(Self::nominating(aux).is_none(), "Cannot nominate if already nominating.");
		ensure!(Self::intentions().iter().find(|&t| t == aux.ref_into()).is_none(), "Cannot nominate if already staked.");

		// update nominators_for
		let mut t = Self::nominators_for(&target);
		t.push(aux.clone());
		<NominatorsFor<T>>::insert(&target, t);

		// update nominating
		<Nominating<T>>::insert(aux, &target);

		// Update bondage
		<Bondage<T>>::insert(aux.ref_into(), T::BlockNumber::max_value());

		Ok(())
	}

	/// Will panic if called when source isn't currently nominating target.
	/// Updates Nominating, NominatorsFor and NominationBalance.
	fn unnominate(aux: &T::PublicAux, target_index: u32) -> Result {
		let source = aux.ref_into();
		let target_index = target_index as usize;

		let target = <Nominating<T>>::get(source).ok_or("Account must be nominating")?;

		let mut t = Self::nominators_for(&target);
		if t.get(target_index) != Some(source) {
			return Err("Invalid target index")
		}

		// Ok - all valid.

		// update nominators_for
		t.swap_remove(target_index);
		<NominatorsFor<T>>::insert(&target, t);

		// update nominating
		<Nominating<T>>::remove(source);

		// update bondage
		<Bondage<T>>::insert(aux.ref_into(), Self::current_era() + Self::bonding_duration());
		Ok(())
	}

	/// Set the given account's preference for slashing behaviour should they be a validator. 
	/// 
	/// An error (no-op) if `Self::intentions()[intentions_index] != aux`.
	fn register_slash_preference(
		aux: &T::PublicAux,
		intentions_index: u32,
		p: SlashPreference
	) -> Result {
		let aux = aux.ref_into();

		if Self::intentions().get(intentions_index as usize) != Some(aux) {
			return Err("Invalid index")
		}
		
		<SlashPreferenceOf<T>>::insert(aux, p);

		Ok(())
	}

	/// Note the previous block's validator missed their opportunity to propose a block. This only comes in
	/// if 2/3+1 of the validators agree that no proposal was submitted. It's only relevant
	/// for the previous block.
	fn note_missed_proposal(aux: &T::PublicAux, offline_val_indices: Vec<u32>) -> Result {
		assert!(aux.is_empty());
		assert!(
			<system::Module<T>>::extrinsic_index() == T::NOTE_MISSED_PROPOSAL_POSITION,
			"note_missed_proposal extrinsic must be at position {} in the block",
			T::NOTE_MISSED_PROPOSAL_POSITION
		);

		for validator_index in offline_val_indices.into_iter() {
			let v = <session::Module<T>>::validators()[validator_index as usize].clone();
			let slash_count = Self::slash_count(&v);
			<SlashCount<T>>::insert(v.clone(), slash_count + 1);
			let grace = Self::offline_slash_grace();

			if slash_count >= grace {
				let instances = slash_count - grace;
				let slash = Self::early_era_slash() << instances;
				let next_slash = slash << 1u32;
				let _ = Self::slash_validator(&v, slash);
				if instances >= Self::slash_preference_of(&v).unstake_threshold
					|| Self::slashable_balance(&v) < next_slash
				{
					if let Some(pos) = Self::intentions().into_iter().position(|x| &x == &v) {
						Self::apply_unstake(&v, pos)
							.expect("pos derived correctly from Self::intentions(); \
								apply_unstake can only fail if pos wrong; \
								Self::intentions() doesn't change; qed");
					}
					let _ = Self::force_new_era(false);
				}
			}
		}
		
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
	/// `apply_rewards` should be true for validators to get the session reward.
	fn force_new_era(apply_rewards: bool) -> Result {
		<ForcingNewEra<T>>::put(());
		<session::Module<T>>::force_new_session(apply_rewards)
	}

	/// Set the offline slash grace period.
	fn set_offline_slash_grace(new: u32) -> Result {
		<OfflineSlashGrace<T>>::put(&new);
		Ok(())
	}

	/// Set the balances of a given account.
	fn set_balance(who: Address<T>, free: T::Balance, reserved: T::Balance) -> Result {
		let who = Self::lookup(who)?;
		Self::set_free_balance(&who, free);
		Self::set_reserved_balance(&who, reserved);
		Ok(())
	}

	// PUBLIC MUTABLES (DANGEROUS)

	/// Set the free balance of an account to some new value.
	///
	/// Will enforce ExistentialDeposit law, anulling the account as needed.
	/// In that case it will return `AccountKilled`.
	pub fn set_reserved_balance(who: &T::AccountId, balance: T::Balance) -> UpdateBalanceOutcome {
		if balance < Self::existential_deposit() {
			<ReservedBalance<T>>::insert(who, balance);
			Self::on_reserved_too_low(who);
			UpdateBalanceOutcome::AccountKilled
		} else {
			<ReservedBalance<T>>::insert(who, balance);
			UpdateBalanceOutcome::Updated
		}
	}

	/// Set the free balance of an account to some new value. Will enforce ExistentialDeposit
	/// law anulling the account as needed.
	///
	/// Doesn't do any preparatory work for creating a new account, so should only be used when it
	/// is known that the account already exists.
	///
	/// Returns if the account was successfully updated or update has led to killing of the account.
	pub fn set_free_balance(who: &T::AccountId, balance: T::Balance) -> UpdateBalanceOutcome {
		// Commented out for no - but consider it instructive.
		// assert!(!Self::voting_balance(who).is_zero());
		if balance < Self::existential_deposit() {
			<FreeBalance<T>>::insert(who, balance);
			Self::on_free_too_low(who);
			UpdateBalanceOutcome::AccountKilled
		} else {
			<FreeBalance<T>>::insert(who, balance);
			UpdateBalanceOutcome::Updated
		}
	}

	/// Set the free balance on an account to some new value.
	///
	/// Same as [`set_free_balance`], but will create a new account.
	///
	/// Returns if the account was successfully updated or update has led to killing of the account.
	///
	/// [`set_free_balance`]: #method.set_free_balance
	pub fn set_free_balance_creating(who: &T::AccountId, balance: T::Balance) -> UpdateBalanceOutcome {
		let ed = <Module<T>>::existential_deposit();
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
			Self::set_free_balance(who, balance);
			UpdateBalanceOutcome::AccountKilled
		} else {
			if !<FreeBalance<T>>::exists(who) {
				let outcome = Self::new_account(&who, balance);
				let credit = match outcome {
					NewAccountOutcome::GoodHint => balance + <Module<T>>::reclaim_rebate(),
					_ => balance,
				};
				Self::set_free_balance(who, credit);
				Self::increase_total_stake_by(credit - balance);
			} else {	
				Self::set_free_balance(who, balance);
			}

			UpdateBalanceOutcome::Updated
		}
	}

	/// Deducts up to `value` from the combined balance of `who`, preferring to deduct from the
	/// free balance. This function cannot fail.
	///
	/// As much funds up to `value` will be deducted as possible. If this is less than `value`,
	/// then `Some(remaining)` will be returned. Full completion is given by `None`.
	pub fn slash(who: &T::AccountId, value: T::Balance) -> Option<T::Balance> {
		let free_balance = Self::free_balance(who);
		let free_slash = cmp::min(free_balance, value);
		Self::set_free_balance(who, free_balance - free_slash);
		Self::decrease_total_stake_by(free_slash);
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
		Self::increase_total_stake_by(value);
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
	/// then `Some(remaining)` will be returned. Full completion is given by `None`.
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
	/// then `Some(remaining)` will be returned. Full completion is given by `None`.
	pub fn slash_reserved(who: &T::AccountId, value: T::Balance) -> Option<T::Balance> {
		let b = Self::reserved_balance(who);
		let slash = cmp::min(b, value);
		Self::set_reserved_balance(who, b - slash);
		Self::decrease_total_stake_by(slash);
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
	/// `Ok(Some(remaining))` will be returned. Full completion is given by `Ok(None)`.
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

	/// Slash a given validator by a specific amount. Removes the slash from their balance by preference,
	/// and reduces the nominators' balance if needed.
	fn slash_validator(v: &T::AccountId, slash: T::Balance) {
		// skip the slash in degenerate case of having only 4 staking participants despite having a larger
		// desired number of validators (validator_count).
		if Self::intentions().len() <= Self::minimum_validator_count() {
			return
		}

		if let Some(rem) = Self::slash(v, slash) {
			let noms = Self::current_nominators_for(v);
			let total = noms.iter().map(Self::voting_balance).fold(T::Balance::zero(), |acc, x| acc + x);
			if !total.is_zero() {
				let safe_mul_rational = |b| b * rem / total;// TODO: avoid overflow
				for n in noms.iter() {
					let _ = Self::slash(n, safe_mul_rational(Self::voting_balance(n)));	// best effort - not much that can be done on fail.
				}
			}
		}
	}

	/// Reward a given validator by a specific amount. Add the reward to their, and their nominators'
	/// balance, pro-rata.
	fn reward_validator(who: &T::AccountId, reward: T::Balance) {
		let noms = Self::current_nominators_for(who);
		let total = noms.iter().map(Self::voting_balance).fold(Self::voting_balance(who), |acc, x| acc + x);
		if !total.is_zero() {
			let safe_mul_rational = |b| b * reward / total;// TODO: avoid overflow
			for n in noms.iter() {
				let _ = Self::reward(n, safe_mul_rational(Self::voting_balance(n)));
			}
			let _ = Self::reward(who, safe_mul_rational(Self::voting_balance(who)));
		}
	}

	/// Actually carry out the unstake operation.
	/// Assumes `intentions()[intentions_index] == who`.
	fn apply_unstake(who: &T::AccountId, intentions_index: usize) -> Result {
		let mut intentions = Self::intentions();
		if intentions.get(intentions_index) != Some(who) {
			return Err("Invalid index");
		}
		intentions.swap_remove(intentions_index);
		<Intentions<T>>::put(intentions);
		<SlashPreferenceOf<T>>::remove(who);
		<SlashCount<T>>::remove(who);
		<Bondage<T>>::insert(who, Self::current_era() + Self::bonding_duration());
		Ok(())
	}

	/// Get the reward for the session, assuming it ends with this block.
	fn this_session_reward(actual_elapsed: T::Moment) -> T::Balance {
		let ideal_elapsed = <session::Module<T>>::ideal_session_duration();
		let per65536: u64 = (T::Moment::sa(65536u64) * ideal_elapsed.clone() / actual_elapsed.max(ideal_elapsed)).as_();
		Self::session_reward() * T::Balance::sa(per65536) / T::Balance::sa(65536u64)
	}

	/// Session has just changed. We need to determine whether we pay a reward, slash and/or
	/// move to a new era.
	fn new_session(actual_elapsed: T::Moment, should_reward: bool) {
		if should_reward {
			// apply good session reward
			let reward = Self::this_session_reward(actual_elapsed);
			for v in <session::Module<T>>::validators().iter() {
				Self::reward_validator(v, reward);
			}
		}

		let session_index = <session::Module<T>>::current_index();
		if <ForcingNewEra<T>>::take().is_some()
			|| ((session_index - Self::last_era_length_change()) % Self::sessions_per_era()).is_zero()
		{
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
		// TODO: this is not sound. this should be moved to an off-chain solution mechanism.
		let mut intentions = Self::intentions()
			.into_iter()
			.map(|v| (Self::slashable_balance(&v), v))
			.collect::<Vec<_>>();

		// Avoid reevaluate validator set if it would leave us with fewer than the minimum
		// needed validators
		if intentions.len() < Self::minimum_validator_count() {
			return
		}

		intentions.sort_unstable_by(|&(ref b1, _), &(ref b2, _)| b2.cmp(&b1));

		<StakeThreshold<T>>::put(
			if !intentions.is_empty() {
				let i = (<ValidatorCount<T>>::get() as usize).min(intentions.len() - 1);
				intentions[i].0.clone()
			} else { Zero::zero() }
		);
		let vals = &intentions.into_iter()
			.map(|(_, v)| v)
			.take(<ValidatorCount<T>>::get() as usize)
			.collect::<Vec<_>>();
		for v in <session::Module<T>>::validators().iter() {
			<CurrentNominatorsFor<T>>::remove(v);
			let slash_count = <SlashCount<T>>::take(v);
			if slash_count > 1 {
				<SlashCount<T>>::insert(v, slash_count - 1);
			}
		}
		for v in vals.iter() {
			<CurrentNominatorsFor<T>>::insert(v, Self::nominators_for(v));
		}
		<session::Module<T>>::set_validators(vals);
	}

	fn enum_set_size() -> T::AccountIndex {
		T::AccountIndex::sa(ENUM_SET_SIZE)
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
		Self::decrease_total_stake_by(Self::free_balance(who));
		<FreeBalance<T>>::remove(who);
		<Bondage<T>>::remove(who);
		T::OnAccountKill::on_account_kill(who);

		if Self::reserved_balance(who).is_zero() {
			<system::AccountNonce<T>>::remove(who);
		}
	}

	/// Kill an account's reserved portion.
	fn on_reserved_too_low(who: &T::AccountId) {
		Self::decrease_total_stake_by(Self::reserved_balance(who));
		<ReservedBalance<T>>::remove(who);
		if Self::free_balance(who).is_zero() {
			<system::AccountNonce<T>>::remove(who);
		}
	}

	/// Increase TotalStake by Value.
	pub fn increase_total_stake_by(value: T::Balance) {
		if let Some(v) = <Module<T>>::total_stake().checked_add(&value) {
			<TotalStake<T>>::put(v);
		}
	}
	/// Decrease TotalStake by Value.
	pub fn decrease_total_stake_by(value: T::Balance) {
		if let Some(v) = <Module<T>>::total_stake().checked_sub(&value) {
			<TotalStake<T>>::put(v);
		}
	}
}

impl<T: Trait> Executable for Module<T> {
	fn execute() {
	}
}

impl<T: Trait> OnSessionChange<T::Moment> for Module<T> {
	fn on_session_change(elapsed: T::Moment, should_reward: bool) {
		Self::new_session(elapsed, should_reward);
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
		let transaction_fee = Self::transaction_base_fee() + Self::transaction_byte_fee() * <T::Balance as As<u64>>::sa(encoded_len as u64);
		if b < transaction_fee + Self::existential_deposit() {
			return Err("not enough funds for transaction fee");
		}
		Self::set_free_balance(transactor, b - transaction_fee);
		Self::decrease_total_stake_by(transaction_fee);
		Ok(())
	}
}
