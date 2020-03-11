// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! # Multi Account Module
//! A module with multisig functionality with a static AccountId and a dynamic threshold and set of signatories.
//!
//! - [`utility::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//!
//! ## Overview
//!
//! This module contains functionality to create, update and remove multi accounts, identified by a deterministically
//! generated account ID, as well as (potentially) stateful multisig dispatches.
//!
//! This module is closely implemented after the multisig functionality of the utility pallet. The main difference is
//! that this module stores static account ids on chain which are not changing when the threshold or signatories are
//! updated.
//!
//! This module allows multiple signed origins (accounts) to coordinate and dispatch calls from a previously created
//! multi account origin. When dispatching calls, the threshold defined in the multi account defines the number of
//! accounts from the multi account signatory set that must approve it. In the case that the threshold is just one then
//! this is a stateless operation. This is useful for multisig wallets where cryptographic threshold signatures are
//! not available or desired or where a dynamic set of signatories with a static account ID is desired.
//!
//! The motivation for this module is that a deterministically created account ID from threshold and a set of
//! signatories as in the utility pallet has certain downsides:
//!
//!  1. When using multisigs for token holdings and changing signatories or the threshold, the tokens need to be
//! 	transferred to a new account ID, which might be a taxable event, depending on jurisdiction. Even if it's not, it
//! 	complicates communication with accountants/tax advisors.
//!  2. When using multisigs for staking and changing signatories or the threshold, the account needs to unbond,
//! 	transfer tokens and re-stake again. That can lead to months of lost staking rewards, depending on the unbonding
//! 	time.
//!  3. When using multisigs for voting and changing signatories or the threshold, the accounts needs to unvotes,
//! 	transfer tokens and vote again, which is cumbersome.
//!
//! The downside of using this multi account module is that it is slightly more complex than the utility multisigs and
//! that it introduces additional state and the requirement of creating multi accounts before using multisigs.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! #### For multi account management
//! * `create` - Create a new multi account with a threshold and given signatories.
//! * `update` - Update an existing multi account with a new threshold and new signatories.
//! * `remove` - Remove an existing multi account.
//!
//! #### For multisig dispatch
//! * `call` - Approve and if possible dispatch a call from a multi account origin.
//! * `approve` - Approve a call from a multi account origin.
//! * `cancel` - Cancel a call from a multi account origin.
//!
//! [`Call`]: ./enum.Call.html
//! [`Trait`]: ./trait.Trait.html

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use codec::{Encode, Decode};
use sp_core::TypeId;
use sp_io::hashing::blake2_256;
use frame_support::{decl_module, decl_event, decl_error, decl_storage, Parameter, ensure, RuntimeDebug};
use frame_support::{traits::{Get, ReservableCurrency, Currency}, weights::{
	SimpleDispatchInfo, GetDispatchInfo, DispatchClass, FunctionOf,
}};
use frame_system::{self as system, ensure_signed};
use sp_runtime::{DispatchError, DispatchResult, traits::Dispatchable};

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

/// Configuration trait.
pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

	/// The overarching call type.
	type Call: Parameter + Dispatchable<Origin=Self::Origin> + GetDispatchInfo;

	/// The currency mechanism.
	type Currency: ReservableCurrency<Self::AccountId>;

	/// The base amount of currency needed to reserve for creating a multi account.
	///
	/// This is held for an additional storage item whose value size is
	/// `4 + sizeof((BlockNumber, Balance, AccountId))` bytes.
	type MultiAccountDepositBase: Get<BalanceOf<Self>>;

	/// The amount of currency needed per signatory when creating a multi account.
	///
	/// This is held for adding 32 bytes more into a pre-existing storage value.
	type MultiAccountDepositFactor: Get<BalanceOf<Self>>;

	/// The base amount of currency needed to reserve for creating a multisig execution.
	///
	/// This is held for an additional storage item whose value size is
	/// `4 + sizeof((BlockNumber, Balance, AccountId))` bytes.
	type MultisigDepositBase: Get<BalanceOf<Self>>;

	/// The amount of currency needed per unit threshold when creating a multisig execution.
	///
	/// This is held for adding 32 bytes more into a pre-existing storage value.
	type MultisigDepositFactor: Get<BalanceOf<Self>>;

	/// The maximum amount of signatories allowed in the multisig.
	type MaxSignatories: Get<u16>;
}

/// A global extrinsic index, formed as the extrinsic index within a block, together with that
/// block's height. This allows a transaction in which a multisig operation of a particular
/// composite was created to be uniquely identified.
#[derive(Copy, Clone, Eq, PartialEq, Encode, Decode, Default, RuntimeDebug)]
pub struct Timepoint<BlockNumber> {
	/// The hieght of the chain at the point in time.
	height: BlockNumber,
	/// The index of the extrinsic at the point in time.
	index: u32,
}

/// A multisig account.
#[derive(Clone, Eq, PartialEq, Encode, Decode, Default, RuntimeDebug)]
pub struct MultiAccountData<Balance, AccountId> {
	// The total number of approvals for dispatches before they are executed.
	threshold: u16,
	// The accounts who can approve dispatches. May not be empty.
	signatories: Vec<AccountId>,
	/// The amount held in reserve of the `depositor`, to be returned once the operation ends.
	deposit: Balance,
	/// The account who opened it (i.e. the first to approve it).
	depositor: AccountId,
}

/// An open multisig operation.
#[derive(Clone, Eq, PartialEq, Encode, Decode, Default, RuntimeDebug)]
pub struct Multisig<BlockNumber, Balance, AccountId> {
	/// The extrinsic when the multisig operation was opened.
	when: Timepoint<BlockNumber>,
	/// The amount held in reserve of the `depositor`, to be returned once the operation ends.
	deposit: Balance,
	/// The account who opened it (i.e. the first to approve it).
	depositor: AccountId,
	/// The approvals achieved so far, including the depositor. Always sorted.
	approvals: Vec<AccountId>,
}

decl_storage! {
	trait Store for Module<T: Trait> as MultiAccount {
		/// Current multi account index.
		MultiAccountIndex: u64;

		/// The set of multi accounts.
		pub MultiAccounts: map
			hasher(blake2_256) T::AccountId
			=> Option<MultiAccountData<BalanceOf<T>, T::AccountId>>;

		/// The set of open multisig operations.
		pub Multisigs: double_map
			hasher(twox_64_concat) T::AccountId, hasher(blake2_128_concat) [u8; 32]
			=> Option<Multisig<T::BlockNumber, BalanceOf<T>, T::AccountId>>;
	}
	add_extra_genesis {
		config(multi_accounts): Vec<(T::AccountId, u16, Vec<T::AccountId>)>;
		build(|config: &GenesisConfig<T>| {
			for &(ref depositor, threshold, ref other_signatories) in config.multi_accounts.iter() {
				<Module<T>>::create(
					T::Origin::from(Some(depositor.clone()).into()),
					threshold,
					other_signatories.clone(),
				).expect("unable to create multi accounts with the provided genesis");
			}
		});
	}
}

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// Threshold is too low (zero).
		ZeroThreshold,
		/// Call is already approved by this signatory.
		AlreadyApproved,
		/// Call doesn't need any (more) approvals.
		NoApprovalsNeeded,
		/// There are too few signatories in the list.
		TooFewSignatories,
		/// There are too many signatories in the list.
		TooManySignatories,
		/// The signatories were provided out of order; they should be ordered.
		SignatoriesOutOfOrder,
		/// The sender was contained in the other signatories; it shouldn't be.
		SenderInSignatories,
		/// Multi account not found.
		MultiAccountNotFound,
		/// Multisig operation not found when attempting to cancel.
		NotFound,
		/// Only the account that originally created the multisig is able to cancel it.
		NotOwner,
		/// The sender is not a signatory of this multi account
		NotSignatory,
		/// No timepoint was given, yet the multisig operation is already underway.
		NoTimepoint,
		/// A different timepoint was given to the multisig operation that is underway.
		WrongTimepoint,
		/// A timepoint was given, yet no multisig operation is underway.
		UnexpectedTimepoint,
		/// There are active multisigs for this multi account; cancel them first.
		ActiveMultisigs,
	}
}

decl_event! {
	/// Events type.
	pub enum Event<T> where
		AccountId = <T as system::Trait>::AccountId,
		BlockNumber = <T as system::Trait>::BlockNumber
	{
		/// A multi account has been created. First param is the account that created it, second is the multisig
		/// account.
		NewMultiAccount(AccountId, AccountId),
		/// A multi account has been updated. First param is the multisig account.
		MultiAccountUpdated(AccountId),
		/// A multi account has been removed. First param is the multisig account.
		MultiAccountRemoved(AccountId),
		/// A new multisig operation has begun. First param is the account that is approving,
		/// second is the multisig account.
		NewMultisig(AccountId, AccountId),
		/// A multisig operation has been approved by someone. First param is the account that is
		/// approving, third is the multisig account.
		MultisigApproval(AccountId, Timepoint<BlockNumber>, AccountId),
		/// A multisig operation has been executed. First param is the account that is
		/// approving, third is the multisig account.
		MultisigExecuted(AccountId, Timepoint<BlockNumber>, AccountId, DispatchResult),
		/// A multisig operation has been cancelled. First param is the account that is
		/// cancelling, third is the multisig account.
		MultisigCancelled(AccountId, Timepoint<BlockNumber>, AccountId),
	}
}

/// A module identifier. These are per module and should be stored in a registry somewhere.
#[derive(Clone, Copy, Eq, PartialEq, Encode, Decode)]
struct IndexedMultiAccountModuleId(u16);

impl TypeId for IndexedMultiAccountModuleId {
	const TYPE_ID: [u8; 4] = *b"muac";
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		/// Deposit one of this module's events by using the default implementation.
		fn deposit_event() = default;

		/// Create a new multi account with a threshold and given signatories.
		///
		/// This generates a new static account id, that will persist when the threshold or set of signatories are
		/// changed later on.
		///
		/// Payment: `MultiAccountDepositBase` will be reserved, plus the number of signatories times
		/// `MultiAccountDepositFactor`. It is returned when the multi account is updated or removed.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// - `threshold`: The total number of approvals dispatches from this multi account require before they are
		///    executed.
		/// - `other_signatories`: The accounts (other than the sender) who can approve dispatches from this multi
		///    account. May be empty.
		///
		/// # <weight>
		/// - `O(S)`.
		/// - One balance-reserve operation.
		/// - One insert with `O(S)` where `S` is the number of
		///   signatories. `S` is capped by `MaxSignatories`, with weight being proportional.
		/// - One encode & hash, both of complexity `O(S)`.
		/// - I/O: 1 mutate `O(S)`
		/// - One event.
		/// - Storage: inserts one item, value size bounded by `MaxSignatories`, with a
		///   deposit taken for its lifetime of
		///   `MultiAccountDepositBase + other_signatories.len() * MultiAccountDepositFactor`.
		/// # </weight>
		#[weight = FunctionOf(
			|args: (&u16, &Vec<T::AccountId>)| 10_000 * (args.1.len() as u32 + 1),
			DispatchClass::Normal,
			true
		)]
		fn create(origin,
			threshold: u16,
			other_signatories: Vec<T::AccountId>
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			ensure!(threshold >= 1, Error::<T>::ZeroThreshold);
			let max_sigs = T::MaxSignatories::get() as usize;
			ensure!(threshold as usize <= other_signatories.len() + 1, Error::<T>::TooFewSignatories);
			ensure!(other_signatories.len() < max_sigs, Error::<T>::TooManySignatories);
			let signatories = Self::ensure_sorted_and_insert(other_signatories.clone(), who.clone())?;

			let multi_account_index = MultiAccountIndex::get()
				.checked_add(1)
				.expect("multi account indices will never reach 2^64 before the death of the universe; qed");

			let id = Self::multi_account_id(multi_account_index);

			let deposit = T::MultiAccountDepositBase::get()
				+ T::MultiAccountDepositFactor::get() * (other_signatories.len() as u32 + 1).into();

			T::Currency::reserve(&who, deposit)?;

			MultiAccountIndex::put(multi_account_index);

			<MultiAccounts<T>>::insert(&id, MultiAccountData {
				threshold,
				signatories,
				deposit,
				depositor: who.clone(),
			});

			Self::deposit_event(RawEvent::NewMultiAccount(who, id));

			Ok(())
		}

		/// Update an existing multi account with a new threshold and new signatories.
		///
		/// This maintains the multi account's account id.
		///
		/// Payment: `MultiAccountDepositBase` will be reserved, plus the number of signatories times
		/// `MultiAccountDepositFactor`. It is returned when the multi account is updated or removed. This call will
		/// unreserve the previous deposit.
		///
		/// The dispatch origin for this call must be _Signed_ and be equal to the multi account ID. It can be
		/// dispatched by a `call` from this module.
		///
		/// Any active multisig operation needs to be cancelled before a multi account can be updated. See the cancel
		/// extrinsic for details.
		///
		/// - `threshold`: The total number of approvals dispatches from this multi account require before they are
		///    executed.
		/// - `signatories`: The accounts who can approve dispatches from this multi account. May not be empty.
		///
		/// # <weight>
		/// - `O(S)`.
		/// - One balance-reserve and unreserve operation.
		/// - One insert with `O(S)` where `S` is the number of
		///   signatories. `S` is capped by `MaxSignatories`, with weight being proportional.
		/// - One encode & hash, both of complexity `O(S)`.
		/// - I/O: 1 read `O(S)`, 1 mutate `O(S)`.
		/// - One event.
		/// - Storage: inserts one item, value size bounded by `MaxSignatories`, with a
		///   deposit taken for its lifetime of
		///   `MultiAccountDepositBase + signatories.len() * MultiAccountDepositFactor`.
		/// # </weight>
		#[weight = FunctionOf(
			|args: (&u16, &Vec<T::AccountId>)| 10_000 * (args.1.len() as u32 + 1),
			DispatchClass::Normal,
			true
		)]
		fn update(origin,
			threshold: u16,
			signatories: Vec<T::AccountId>
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			ensure!(threshold >= 1, Error::<T>::ZeroThreshold);
			let max_sigs = T::MaxSignatories::get() as usize;
			ensure!(signatories.len() >= 1, Error::<T>::TooFewSignatories);
			ensure!(threshold as usize <= signatories.len(), Error::<T>::TooFewSignatories);
			ensure!(signatories.len() <= max_sigs, Error::<T>::TooManySignatories);
			ensure!(Self::is_sorted_and_unique(&signatories), Error::<T>::SignatoriesOutOfOrder);
			let multi_account = <MultiAccounts<T>>::get(&who).ok_or(Error::<T>::MultiAccountNotFound)?;

			// Check there are no active multisigs
			let mut active_multisigs = <Multisigs<T>>::iter_prefix(&who);
			ensure!(active_multisigs.next().is_none(), Error::<T>::ActiveMultisigs);

			// reserve new deposit for updated multi account
			let updated_deposit = T::MultiAccountDepositBase::get()
				+ T::MultiAccountDepositFactor::get() * (signatories.len() as u32).into();

			T::Currency::reserve(&who, updated_deposit)?;

			// save multi account
			<MultiAccounts<T>>::insert(&who, MultiAccountData {
				threshold,
				signatories,
				deposit: updated_deposit,
				depositor: who.clone(),
			});

			// unreserve previous deposit
			let _ = T::Currency::unreserve(&multi_account.depositor, multi_account.deposit);

			Self::deposit_event(RawEvent::MultiAccountUpdated(who));

			Ok(())
		}

		/// Remove an existing multi account.
		///
		/// Payment: Previous deposits will be unreserved.
		///
		/// The dispatch origin for this call must be _Signed_ and be equal to the multi account ID. It can be
		/// dispatched by a `call` from this module.
		///
		/// Any active multisig operation needs to be cancelled before a multi account can be updated. See the cancel
		/// extrinsic for details.
		///
		/// # <weight>
		/// - `O(1)`.
		/// - One balance-unreserve operation.
		/// - One remove with `O(S)` where `S` is the number of
		///   signatories. `S` is capped by `MaxSignatories`, with weight being proportional.
		/// - I/O: 1 mutate `O(S)`.
		/// - One event.
		/// - Storage: removes one item, value size bounded by `MaxSignatories`.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(1_000_000)]
		fn remove(origin) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let multi_account = <MultiAccounts<T>>::get(&who).ok_or(Error::<T>::MultiAccountNotFound)?;

			// Check there are no active multisigs
			let mut active_multisigs = <Multisigs<T>>::iter_prefix(&who);
			ensure!(active_multisigs.next().is_none(), Error::<T>::ActiveMultisigs);

			let _ = T::Currency::unreserve(&multi_account.depositor, multi_account.deposit);

			<MultiAccounts<T>>::remove(&who);

			Self::deposit_event(RawEvent::MultiAccountRemoved(who));

			Ok(())
		}

		/// Register approval for a dispatch to be made from the given multi account if approved by a total of
		/// `threshold` of `signatories`, as specified in the multi account.
		///
		/// If there are enough approvals, then dispatch the call.
		///
		/// Payment: `MultisigDepositBase` will be reserved if this is the first approval, plus
		/// `threshold` times `MultisigDepositFactor`. It is returned once this dispatch happens or
		/// is cancelled.
		///
		/// The dispatch origin for this call must be _Signed_ and must be one of the signatories.
		///
		/// - `multi_account_id`: The account ID of the multi account that was created before.
		/// - `maybe_timepoint`: If this is the first approval, then this must be `None`. If it is
		/// not the first approval, then it must be `Some`, with the timepoint (block number and
		/// transaction index) of the first approval transaction.
		/// - `call`: The call to be executed.
		///
		/// NOTE: Unless this is the final approval, you will generally want to use
		/// `approve` instead, since it only requires a hash of the call.
		///
		/// Result is equivalent to the dispatched result if `threshold` is exactly `1`. Otherwise
		/// on success, result is `Ok` and the result from the interior call, if it was executed,
		/// may be found in the deposited `MultisigExecuted` event.
		///
		/// # <weight>
		/// - `O(S + Z + Call)`.
		/// - Up to one balance-reserve or unreserve operation.
		/// - One passthrough operation, one insert, both `O(S)` where `S` is the number of
		///   signatories. `S` is capped by `MaxSignatories`, with weight being proportional.
		/// - One call encode & hash, both of complexity `O(Z)` where `Z` is tx-len.
		/// - One encode & hash, both of complexity `O(S)`.
		/// - Up to two binary searches and inserts (`O(logS + S)`).
		/// - I/O: 1 read `O(S)`, up to 1 mutate `O(S)`. Up to one remove.
		/// - One event.
		/// - The weight of the `call`.
		/// - Storage: inserts one item, value size bounded by `MaxSignatories`, with a
		///   deposit taken for its lifetime of
		///   `MultisigDepositBase + threshold * MultisigDepositFactor`.
		/// # </weight>
		#[weight = FunctionOf(
			|args: (&T::AccountId, &Option<Timepoint<T::BlockNumber>>, &Box<<T as Trait>::Call>)| args.2.get_dispatch_info().weight,
			|args: (&T::AccountId, &Option<Timepoint<T::BlockNumber>>, &Box<<T as Trait>::Call>)| args.2.get_dispatch_info().class,
			true
		)]
		fn call(origin,
			multi_account_id: T::AccountId,
			maybe_timepoint: Option<Timepoint<T::BlockNumber>>,
			call: Box<<T as Trait>::Call>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let multi_account = <MultiAccounts<T>>::get(&multi_account_id).ok_or(Error::<T>::MultiAccountNotFound)?;

			// ensure that the origin is a signatory of the multi account
			if let Err(_) = multi_account.signatories.binary_search(&who) {
				Err(Error::<T>::NotSignatory)?
			}

			let call_hash = call.using_encoded(blake2_256);

			if let Some(mut m) = <Multisigs<T>>::get(&multi_account_id, call_hash) {
				let timepoint = maybe_timepoint.ok_or(Error::<T>::NoTimepoint)?;
				ensure!(m.when == timepoint, Error::<T>::WrongTimepoint);

				if let Err(pos) = m.approvals.binary_search(&who) {
					// we know threshold is greater than zero from the above ensure.
					if (m.approvals.len() as u16) < multi_account.threshold - 1 {
						m.approvals.insert(pos, who.clone());
						<Multisigs<T>>::insert(&multi_account_id, call_hash, m);
						Self::deposit_event(RawEvent::MultisigApproval(who, timepoint, multi_account_id));
						return Ok(())
					}
				} else {
					if (m.approvals.len() as u16) < multi_account.threshold {
						Err(Error::<T>::AlreadyApproved)?
					}
				}

				let result = call.dispatch(frame_system::RawOrigin::Signed(multi_account_id.clone()).into());
				let _ = T::Currency::unreserve(&m.depositor, m.deposit);
				<Multisigs<T>>::remove(&multi_account_id, call_hash);
				Self::deposit_event(RawEvent::MultisigExecuted(who, timepoint, multi_account_id, result));
			} else {
				ensure!(maybe_timepoint.is_none(), Error::<T>::UnexpectedTimepoint);
				if multi_account.threshold > 1 {
					let deposit = T::MultisigDepositBase::get()
						+ T::MultisigDepositFactor::get() * multi_account.threshold.into();
					T::Currency::reserve(&who, deposit)?;
					<Multisigs<T>>::insert(&multi_account_id, call_hash, Multisig {
						when: Self::timepoint(),
						deposit,
						depositor: who.clone(),
						approvals: vec![who.clone()],
					});
					Self::deposit_event(RawEvent::NewMultisig(who, multi_account_id));
				} else {
					return call.dispatch(frame_system::RawOrigin::Signed(multi_account_id).into())
				}
			}

			Ok(())
		}

		/// Register approval for a dispatch to be made from the given multi account if approved by a total of
		/// `threshold` of `signatories`, as specified in the multi account.
		///
		/// Payment: `MultisigDepositBase` will be reserved if this is the first approval, plus
		/// `threshold` times `MultisigDepositFactor`. It is returned once this dispatch happens or
		/// is cancelled.
		///
		/// The dispatch origin for this call must be _Signed_ and must be one of the signatories.
		///
		/// - `multi_account_id`: The account ID of the multi account that was created before.
		/// - `maybe_timepoint`: If this is the first approval, then this must be `None`. If it is
		/// not the first approval, then it must be `Some`, with the timepoint (block number and
		/// transaction index) of the first approval transaction.
		/// - `call_hash`: The hash of the call to be executed.
		///
		/// NOTE: If this is the final approval, you will want to use `call` instead.
		///
		/// # <weight>
		/// - `O(S)`.
		/// - Up to one balance-reserve or unreserve operation.
		/// - One passthrough operation, one insert, both `O(S)` where `S` is the number of
		///   signatories. `S` is capped by `MaxSignatories`, with weight being proportional.
		/// - One encode & hash, both of complexity `O(S)`.
		/// - Up to two binary searches and inserts (`O(logS + S)`).
		/// - I/O: 1 read `O(S)`, up to 1 mutate `O(S)`. Up to one remove.
		/// - One event.
		/// - Storage: inserts one item, value size bounded by `MaxSignatories`, with a
		///   deposit taken for its lifetime of
		///   `MultisigDepositBase + threshold * MultisigDepositFactor`.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(1_000_000)]
		fn approve(origin,
			multi_account_id: T::AccountId,
			maybe_timepoint: Option<Timepoint<T::BlockNumber>>,
			call_hash: [u8; 32],
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let multi_account = <MultiAccounts<T>>::get(&multi_account_id).ok_or(Error::<T>::MultiAccountNotFound)?;

			// ensure that the origin is a signatory of the multi account
			if let Err(_) = multi_account.signatories.binary_search(&who) {
				Err(Error::<T>::NotSignatory)?
			}

			if let Some(mut m) = <Multisigs<T>>::get(&multi_account_id, call_hash) {
				let timepoint = maybe_timepoint.ok_or(Error::<T>::NoTimepoint)?;
				ensure!(m.when == timepoint, Error::<T>::WrongTimepoint);

				ensure!(m.approvals.len() < multi_account.threshold as usize, Error::<T>::NoApprovalsNeeded);
				if let Err(pos) = m.approvals.binary_search(&who) {
					m.approvals.insert(pos, who.clone());
					<Multisigs<T>>::insert(&multi_account_id, call_hash, m);
					Self::deposit_event(RawEvent::MultisigApproval(who, timepoint, multi_account_id));
				} else {
					Err(Error::<T>::AlreadyApproved)?
				}
			} else {
				if multi_account.threshold > 1 {
					ensure!(maybe_timepoint.is_none(), Error::<T>::UnexpectedTimepoint);
					let deposit = T::MultisigDepositBase::get()
						+ T::MultisigDepositFactor::get() * multi_account.threshold.into();
					T::Currency::reserve(&who, deposit)?;
					<Multisigs<T>>::insert(&multi_account_id, call_hash, Multisig {
						when: Self::timepoint(),
						deposit,
						depositor: who.clone(),
						approvals: vec![who.clone()],
					});
					Self::deposit_event(RawEvent::NewMultisig(who, multi_account_id));
				} else {
					Err(Error::<T>::NoApprovalsNeeded)?
				}
			}

			Ok(())
		}

		/// Cancel an active (pre-existing/on-going) multisig transaction. Any deposit reserved previously
		/// for the multisig operation will be unreserved on success.
		///
		/// The dispatch origin for this call must be _Signed_ and must be the initiator (owner) of the multisig or
		/// the multi account itself.
		///
		/// Any active multisig must be cancelled before a multi account can be updated or removed. To prevent
		/// an outgoing multi account member to block updates/removals, the multi account itself can cancel
		/// any active multisig. Such a cancellation can be dispatched by a `call` from this module.
		///
		/// - `multi_account_id`: The account ID of the multi account that was created before.
		/// - `timepoint`: The timepoint (block number and transaction index) of the first approval
		/// transaction for this dispatch.
		/// - `call_hash`: The hash of the call to be executed.
		///
		/// # <weight>
		/// - `O(S)`.
		/// - Up to one balance-reserve or unreserve operation.
		/// - One passthrough operation, one insert, both `O(S)` where `S` is the number of
		///   signatories. `S` is capped by `MaxSignatories`, with weight being proportional.
		/// - One encode & hash, both of complexity `O(S)`.
		/// - One event.
		/// - I/O: 1 read `O(S)`, one remove.
		/// - Storage: removes one item.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(1_000_000)]
		fn cancel(origin,
			multi_account_id: T::AccountId,
			timepoint: Timepoint<T::BlockNumber>,
			call_hash: [u8; 32],
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			let m = <Multisigs<T>>::get(&multi_account_id, call_hash)
				.ok_or(Error::<T>::NotFound)?;
			ensure!(m.when == timepoint, Error::<T>::WrongTimepoint);
			ensure!(who == multi_account_id || who == m.depositor, Error::<T>::NotOwner);

			let _ = T::Currency::unreserve(&m.depositor, m.deposit);
			<Multisigs<T>>::remove(&multi_account_id, call_hash);

			Self::deposit_event(RawEvent::MultisigCancelled(m.depositor, timepoint, multi_account_id));

			Ok(())
		}
	}
}

impl<T: Trait> Module<T> {
	/// Derive a multi account ID from the index.
	pub fn multi_account_id(index: u64) -> T::AccountId {
		let entropy = (b"modmua/multiacco", index).using_encoded(blake2_256);
		T::AccountId::decode(&mut &entropy[..]).unwrap_or_default()
	}

	/// The current `Timepoint`.
	pub fn timepoint() -> Timepoint<T::BlockNumber> {
		Timepoint {
			height: <system::Module<T>>::block_number(),
			index: <system::Module<T>>::extrinsic_count(),
		}
	}

	/// Check that signatories are sorted and unique.
	fn is_sorted_and_unique(signatories: &Vec<T::AccountId>) -> bool {
		signatories.windows(2).all(|w| w[0] < w[1])
	}

	/// Check that signatories is sorted and doesn't contain sender, then insert sender.
	fn ensure_sorted_and_insert(other_signatories: Vec<T::AccountId>, who: T::AccountId)
		-> Result<Vec<T::AccountId>, DispatchError>
	{
		let mut signatories = other_signatories;
		let mut maybe_last = None;
		let mut index = 0;
		for item in signatories.iter() {
			if let Some(last) = maybe_last {
				ensure!(last < item, Error::<T>::SignatoriesOutOfOrder);
			}
			if item <= &who {
				ensure!(item != &who, Error::<T>::SenderInSignatories);
				index += 1;
			}
			maybe_last = Some(item);
		}
		signatories.insert(index, who);
		Ok(signatories)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use frame_support::{
		assert_ok, assert_noop, impl_outer_origin, parameter_types, impl_outer_dispatch,
		weights::Weight, impl_outer_event
	};
	use sp_core::H256;
	use sp_runtime::{Perbill, traits::{BlakeTwo256, IdentityLookup}, testing::Header};
	use crate as pallet_multi_account;

	impl_outer_origin! {
		pub enum Origin for Test where system = frame_system {}
	}

	impl_outer_event! {
		pub enum TestEvent for Test {
			system<T>,
			pallet_balances<T>,
			pallet_multi_account<T>,
		}
	}
	impl_outer_dispatch! {
		pub enum Call for Test where origin: Origin {
			pallet_balances::Balances,
			pallet_multi_account::MultiAccount,
		}
	}

	// For testing the module, we construct most of a mock runtime. This means
	// first constructing a configuration type (`Test`) which `impl`s each of the
	// configuration traits of modules we want to use.
	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: Weight = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}
	impl frame_system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Call = Call;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = TestEvent;
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type MaximumBlockLength = MaximumBlockLength;
		type AvailableBlockRatio = AvailableBlockRatio;
		type Version = ();
		type ModuleToIndex = ();
		type AccountData = pallet_balances::AccountData<u64>;
		type OnNewAccount = ();
		type OnKilledAccount = ();
	}
	parameter_types! {
		pub const ExistentialDeposit: u64 = 1;
	}
	impl pallet_balances::Trait for Test {
		type Balance = u64;
		type Event = TestEvent;
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type AccountStore = System;
	}
	parameter_types! {
		pub const MultiAccountDepositBase: u64 = 1;
		pub const MultiAccountDepositFactor: u64 = 1;
		pub const MultisigDepositBase: u64 = 1;
		pub const MultisigDepositFactor: u64 = 1;
		pub const MaxSignatories: u16 = 3;
	}
	impl Trait for Test {
		type Event = TestEvent;
		type Call = Call;
		type Currency = Balances;
		type MultiAccountDepositBase = MultiAccountDepositBase;
		type MultiAccountDepositFactor = MultiAccountDepositFactor;
		type MultisigDepositBase = MultisigDepositBase;
		type MultisigDepositFactor = MultisigDepositFactor;
		type MaxSignatories = MaxSignatories;
	}
	type System = frame_system::Module<Test>;
	type Balances = pallet_balances::Module<Test>;
	type MultiAccount = Module<Test>;

	use pallet_balances::Call as BalancesCall;
	use pallet_balances::Error as BalancesError;

	fn new_test_ext() -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		pallet_balances::GenesisConfig::<Test> {
			balances: vec![(1, 20), (2, 20), (3, 20), (4, 20), (5, 20)],
		}.assimilate_storage(&mut t).unwrap();
		pallet_multi_account::GenesisConfig::<Test> {
			multi_accounts: vec![(3, 2, vec![4, 5])],
		}.assimilate_storage(&mut t).unwrap();
		t.into()
	}

	fn last_event() -> TestEvent {
		system::Module::<Test>::events().pop().map(|e| e.event).expect("Event expected")
	}

	fn expect_event<E: Into<TestEvent>>(e: E) {
		assert_eq!(last_event(), e.into());
	}

	fn now() -> Timepoint<u64> {
		MultiAccount::timepoint()
	}

	#[test]
	fn genesis_multi_accounts_generated() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(1);
			System::set_block_number(1);
			assert_eq!(MultiAccountIndex::get(), 1);
			assert_eq!(<MultiAccounts<Test>>::get(&multi_id), Some(MultiAccountData {
				threshold: 2,
				signatories: vec![3, 4, 5],
				deposit: 4,
				depositor: 3,
			}));
		});
	}

	#[test]
	fn multisig_deposit_is_taken_and_returned() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(2);
			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi_id, 5));

			assert_ok!(MultiAccount::create(Origin::signed(1), 2, vec![2, 3]));
			assert_eq!(Balances::free_balance(1), 11);
			assert_eq!(Balances::reserved_balance(1), 4);
			expect_event(RawEvent::NewMultiAccount(1, multi_id));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			assert_ok!(MultiAccount::call(Origin::signed(1), multi_id.clone(), None, call.clone()));
			assert_eq!(Balances::free_balance(1), 8);
			assert_eq!(Balances::reserved_balance(1), 7);
			expect_event(RawEvent::NewMultisig(1, multi_id));

			assert_ok!(MultiAccount::call(Origin::signed(2), multi_id, Some(now()), call));
			assert_eq!(Balances::free_balance(1), 11);
			assert_eq!(Balances::reserved_balance(1), 4);
			expect_event(RawEvent::MultisigExecuted(2, now(), multi_id, Ok(())));

			assert_ok!(MultiAccount::remove(Origin::signed(multi_id)));
			assert_eq!(Balances::free_balance(1), 15);
			assert_eq!(Balances::reserved_balance(1), 0);
			expect_event(RawEvent::MultiAccountRemoved(multi_id));
		});
	}

	#[test]
	fn multisig_deposit_is_taken_and_returned_when_updated() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(2);
			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi_id, 5));

			assert_ok!(MultiAccount::create(Origin::signed(1), 2, vec![2, 3]));
			assert_eq!(<MultiAccounts<Test>>::get(&multi_id), Some(MultiAccountData {
				threshold: 2,
				signatories: vec![1, 2, 3],
				deposit: 4,
				depositor: 1,
			}));
			assert_eq!(Balances::free_balance(1), 11);
			assert_eq!(Balances::reserved_balance(1), 4);
			assert_eq!(Balances::free_balance(multi_id), 15);
			assert_eq!(Balances::reserved_balance(multi_id), 0);
			expect_event(RawEvent::NewMultiAccount(1, multi_id));

			assert_ok!(MultiAccount::update(Origin::signed(multi_id), 1, vec![1, 3]));
			assert_eq!(<MultiAccounts<Test>>::get(&multi_id), Some(MultiAccountData {
				threshold: 1,
				signatories: vec![1, 3],
				deposit: 3,
				depositor: multi_id,
			}));
			assert_eq!(Balances::free_balance(1), 15);
			assert_eq!(Balances::reserved_balance(1), 0);
			assert_eq!(Balances::free_balance(multi_id), 12);
			assert_eq!(Balances::reserved_balance(multi_id), 3);
			expect_event(RawEvent::MultiAccountUpdated(multi_id));

			assert_ok!(MultiAccount::remove(Origin::signed(multi_id)));
			assert_eq!(<MultiAccounts<Test>>::get(&multi_id), None);
			assert_eq!(Balances::free_balance(multi_id), 15);
			assert_eq!(Balances::reserved_balance(multi_id), 0);
			expect_event(RawEvent::MultiAccountRemoved(multi_id));
		});
	}

	#[test]
	fn cancel_multisig_returns_deposit() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(2);
			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(MultiAccount::create(Origin::signed(1), 3, vec![2, 3]));
			assert_ok!(MultiAccount::approve(Origin::signed(1), multi_id, None, hash.clone()));
			assert_ok!(MultiAccount::approve(Origin::signed(2), multi_id, Some(now()), hash.clone()));
			assert_eq!(Balances::free_balance(1), 12);
			assert_eq!(Balances::reserved_balance(1), 8);
			assert_ok!(
				MultiAccount::cancel(Origin::signed(1), multi_id, now(), hash.clone()),
			);
			assert_eq!(Balances::free_balance(1), 16);
			assert_eq!(Balances::reserved_balance(1), 4);
			expect_event(RawEvent::MultisigCancelled(1, now(), multi_id));
		});
	}

	#[test]
	fn timepoint_checking_works() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(2);

			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi_id, 5));

			assert_ok!(MultiAccount::create(Origin::signed(1), 3, vec![2, 3]));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);

			assert_noop!(
				MultiAccount::approve(Origin::signed(2), multi_id, Some(now()), hash.clone()),
				Error::<Test>::UnexpectedTimepoint,
			);
			assert_noop!(
				MultiAccount::call(Origin::signed(2), multi_id, Some(now()), call.clone()),
				Error::<Test>::UnexpectedTimepoint,
			);

			assert_ok!(MultiAccount::approve(Origin::signed(1), multi_id, None, hash.clone()));
			assert_noop!(
				MultiAccount::approve(Origin::signed(2), multi_id, None, hash.clone()),
				Error::<Test>::NoTimepoint,
			);
			assert_noop!(
				MultiAccount::call(Origin::signed(2), multi_id, None, call.clone()),
				Error::<Test>::NoTimepoint,
			);
			let later = Timepoint { index: 1, .. now() };
			assert_noop!(
				MultiAccount::approve(Origin::signed(2), multi_id, Some(later), hash.clone()),
				Error::<Test>::WrongTimepoint,
			);
			assert_noop!(
				MultiAccount::call(Origin::signed(2), multi_id, Some(later), call),
				Error::<Test>::WrongTimepoint,
			);
			assert_noop!(
				MultiAccount::cancel(Origin::signed(1), multi_id, later, hash),
				Error::<Test>::WrongTimepoint,
			);
		});
	}

	#[test]
	fn multisig_2_of_3_works() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(2);

			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi_id, 5));

			assert_ok!(MultiAccount::create(Origin::signed(1), 2, vec![2, 3]));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(MultiAccount::approve(Origin::signed(1), multi_id, None, hash));
			assert_eq!(Balances::free_balance(6), 0);

			assert_ok!(MultiAccount::call(Origin::signed(2), multi_id, Some(now()), call));
			assert_eq!(Balances::free_balance(6), 15);
		});
	}

	#[test]
	fn multisig_3_of_3_works() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(2);

			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi_id, 5));

			assert_ok!(MultiAccount::create(Origin::signed(1), 3, vec![2, 3]));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(MultiAccount::approve(Origin::signed(1), multi_id, None, hash.clone()));
			assert_ok!(MultiAccount::approve(Origin::signed(2), multi_id, Some(now()), hash.clone()));
			assert_eq!(Balances::free_balance(6), 0);

			assert_ok!(MultiAccount::call(Origin::signed(3), multi_id, Some(now()), call));
			assert_eq!(Balances::free_balance(6), 15);
		});
	}

	#[test]
	fn cancel_multisig_works() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(2);

			assert_ok!(MultiAccount::create(Origin::signed(1), 3, vec![2, 3]));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(MultiAccount::approve(Origin::signed(1), multi_id, None, hash.clone()));
			assert_ok!(MultiAccount::approve(Origin::signed(2), multi_id, Some(now()), hash.clone()));
			assert_noop!(
				MultiAccount::cancel(Origin::signed(2), multi_id, now(), hash.clone()),
				Error::<Test>::NotOwner,
			);
			assert_noop!(
				MultiAccount::cancel(Origin::signed(1), multi_id, now(), [0u8; 32]),
				Error::<Test>::NotFound,
			);
			assert_ok!(
				MultiAccount::cancel(Origin::signed(1), multi_id, now(), hash.clone()),
			);
		});
	}

	#[test]
	fn multisig_2_of_3_call_works() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(2);

			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi_id, 5));

			assert_ok!(MultiAccount::create(Origin::signed(1), 2, vec![2, 3]));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			assert_ok!(MultiAccount::call(Origin::signed(1), multi_id, None, call.clone()));
			assert_eq!(Balances::free_balance(6), 0);

			assert_ok!(MultiAccount::call(Origin::signed(2), multi_id, Some(now()), call));
			assert_eq!(Balances::free_balance(6), 15);
		});
	}

	#[test]
	fn multisig_2_of_3_call_with_many_calls_works() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(2);

			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi_id, 5));

			assert_ok!(MultiAccount::create(Origin::signed(1), 2, vec![2, 3]));

			let call1 = Box::new(Call::Balances(BalancesCall::transfer(6, 10)));
			let call2 = Box::new(Call::Balances(BalancesCall::transfer(7, 5)));

			assert_ok!(MultiAccount::call(Origin::signed(1), multi_id, None, call1.clone()));
			assert_ok!(MultiAccount::call(Origin::signed(2), multi_id, None, call2.clone()));
			assert_ok!(MultiAccount::call(Origin::signed(3), multi_id, Some(now()), call2));
			assert_ok!(MultiAccount::call(Origin::signed(3), multi_id, Some(now()), call1));

			assert_eq!(Balances::free_balance(6), 10);
			assert_eq!(Balances::free_balance(7), 5);
		});
	}

	#[test]
	fn multisig_2_of_3_cannot_reissue_same_call() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(2);

			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi_id, 5));

			assert_ok!(MultiAccount::create(Origin::signed(1), 2, vec![2, 3]));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 10)));
			assert_ok!(MultiAccount::call(Origin::signed(1), multi_id, None, call.clone()));
			assert_ok!(MultiAccount::call(Origin::signed(2), multi_id, Some(now()), call.clone()));
			assert_eq!(Balances::free_balance(multi_id), 5);

			assert_ok!(MultiAccount::call(Origin::signed(1), multi_id, None, call.clone()));
			assert_ok!(MultiAccount::call(Origin::signed(3), multi_id, Some(now()), call));

			let err = DispatchError::from(BalancesError::<Test, _>::InsufficientBalance).stripped();
			expect_event(RawEvent::MultisigExecuted(3, now(), multi_id, Err(err)));
			assert_eq!(Balances::free_balance(multi_id), 5);
		});
	}

	#[test]
	fn multisig_1_of_1_works() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(2);

			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));

			assert_ok!(MultiAccount::create(Origin::signed(1), 1, vec![]));
			assert_eq!(<MultiAccounts<Test>>::get(&multi_id), Some(MultiAccountData {
				threshold: 1,
				signatories: vec![1],
				deposit: 2,
				depositor: 1,
			}));
			expect_event(RawEvent::NewMultiAccount(1, multi_id));

			assert_ok!(MultiAccount::update(Origin::signed(multi_id), 1, vec![2]));
			assert_eq!(<MultiAccounts<Test>>::get(&multi_id), Some(MultiAccountData {
				threshold: 1,
				signatories: vec![2],
				deposit: 2,
				depositor: multi_id,
			}));
			expect_event(RawEvent::MultiAccountUpdated(multi_id));

			assert_ok!(MultiAccount::remove(Origin::signed(multi_id)));
			assert_eq!(<MultiAccounts<Test>>::get(&multi_id), None);
			expect_event(RawEvent::MultiAccountRemoved(multi_id));
		});
	}

	#[test]
	fn zero_threshold_fails() {
		new_test_ext().execute_with(|| {
			assert_noop!(
				MultiAccount::create(Origin::signed(1), 0, vec![2]),
				Error::<Test>::ZeroThreshold,
			);

			let multi_id = MultiAccount::multi_account_id(2);
			assert_ok!(MultiAccount::create(Origin::signed(1), 1, vec![2]));
			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_noop!(
				MultiAccount::update(Origin::signed(multi_id), 0, vec![2, 3]),
				Error::<Test>::ZeroThreshold,
			);
		});
	}

	#[test]
	fn too_many_signatories_fails() {
		new_test_ext().execute_with(|| {
			assert_noop!(
				MultiAccount::create(Origin::signed(1), 2, vec![2, 3, 4]),
				Error::<Test>::TooManySignatories,
			);

			let multi_id = MultiAccount::multi_account_id(2);
			assert_ok!(MultiAccount::create(Origin::signed(1), 1, vec![2]));
			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_noop!(
				MultiAccount::update(Origin::signed(multi_id), 1, vec![2, 3, 4, 5]),
				Error::<Test>::TooManySignatories,
			);
		});
	}

	#[test]
	fn update_non_existing_fails() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(2);
			assert_ok!(MultiAccount::create(Origin::signed(1), 2, vec![2, 3]));
			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_noop!(
				MultiAccount::update(Origin::signed(1), 1, vec![2, 3]),
				Error::<Test>::MultiAccountNotFound,
			);
		});
	}

	#[test]
	fn remove_non_existing_fails() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(2);
			assert_ok!(MultiAccount::create(Origin::signed(1), 2, vec![2, 3]));
			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_noop!(
				MultiAccount::remove(Origin::signed(1)),
				Error::<Test>::MultiAccountNotFound,
			);
		});
	}

	#[test]
	fn duplicate_approvals_are_ignored() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(2);
			assert_ok!(MultiAccount::create(Origin::signed(1), 2, vec![2, 3]));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(MultiAccount::approve(Origin::signed(1), multi_id, None, hash.clone()));
			assert_noop!(
				MultiAccount::approve(Origin::signed(1), multi_id, Some(now()), hash.clone()),
				Error::<Test>::AlreadyApproved,
			);
			assert_noop!(
				MultiAccount::call(Origin::signed(1), multi_id, Some(now()), call.clone()),
				Error::<Test>::AlreadyApproved,
			);
			assert_ok!(MultiAccount::approve(Origin::signed(2), multi_id, Some(now()), hash.clone()));
			assert_noop!(
				MultiAccount::approve(Origin::signed(3), multi_id, Some(now()), hash.clone()),
				Error::<Test>::NoApprovalsNeeded,
			);
		});
	}

	#[test]
	fn multisig_1_of_3_works() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(2);

			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi_id, 5));

			assert_ok!(MultiAccount::create(Origin::signed(1), 1, vec![2, 3]));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);
			assert_noop!(
				MultiAccount::approve(Origin::signed(1), multi_id, None, hash.clone()),
				Error::<Test>::NoApprovalsNeeded,
			);
			assert_ok!(MultiAccount::call(Origin::signed(1), multi_id, None, call));

			assert_eq!(Balances::free_balance(6), 15);
		});
	}

	#[test]
	fn multisig_fails_if_not_existing() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(2);

			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi_id, 5));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);
			assert_noop!(
				MultiAccount::approve(Origin::signed(1), multi_id, None, hash.clone()),
				Error::<Test>::MultiAccountNotFound,
			);
			assert_noop!(
				MultiAccount::call(Origin::signed(1), multi_id, None, call.clone()),
				Error::<Test>::MultiAccountNotFound,
			);
		});
	}

	#[test]
	fn multisig_fails_if_not_signatory() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(2);

			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi_id, 5));

			assert_ok!(MultiAccount::create(Origin::signed(1), 1, vec![2, 3]));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);
			assert_noop!(
				MultiAccount::approve(Origin::signed(4), multi_id, None, hash.clone()),
				Error::<Test>::NotSignatory,
			);
			assert_noop!(
				MultiAccount::call(Origin::signed(4), multi_id, None, call.clone()),
				Error::<Test>::NotSignatory,
			);
			assert_ok!(MultiAccount::call(Origin::signed(1), multi_id, None, call));

			assert_eq!(Balances::free_balance(6), 15);
		});
	}

	#[test]
	fn multiaccount_update_fails_if_has_active_multisigs() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(2);
			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi_id, 5));

			assert_ok!(MultiAccount::create(Origin::signed(1), 2, vec![2, 3]));
			assert_eq!(<MultiAccounts<Test>>::get(&multi_id), Some(MultiAccountData {
				threshold: 2,
				signatories: vec![1, 2, 3],
				deposit: 4,
				depositor: 1,
			}));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 10)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(MultiAccount::call(Origin::signed(1), multi_id, None, call.clone()));

			assert_noop!(MultiAccount::update(Origin::signed(multi_id), 1, vec![1, 3]), Error::<Test>::ActiveMultisigs);

			// multi account still the same
			assert_eq!(<MultiAccounts<Test>>::get(&multi_id), Some(MultiAccountData {
				threshold: 2,
				signatories: vec![1, 2, 3],
				deposit: 4,
				depositor: 1,
			}));

			assert_ok!(MultiAccount::cancel(Origin::signed(multi_id), multi_id, now(), hash));

			assert_ok!(MultiAccount::update(Origin::signed(multi_id), 1, vec![1, 3]));
			assert_eq!(<MultiAccounts<Test>>::get(&multi_id), Some(MultiAccountData {
				threshold: 1,
				signatories: vec![1, 3],
				deposit: 3,
				depositor: multi_id,
			}));
			expect_event(RawEvent::MultiAccountUpdated(multi_id));
		});
	}

	#[test]
	fn multiaccount_remove_fails_if_has_active_multisigs() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(2);
			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi_id, 5));

			assert_ok!(MultiAccount::create(Origin::signed(1), 2, vec![2, 3]));
			assert_eq!(<MultiAccounts<Test>>::get(&multi_id), Some(MultiAccountData {
				threshold: 2,
				signatories: vec![1, 2, 3],
				deposit: 4,
				depositor: 1,
			}));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 10)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(MultiAccount::call(Origin::signed(1), multi_id, None, call.clone()));

			assert_noop!(MultiAccount::remove(Origin::signed(multi_id)), Error::<Test>::ActiveMultisigs);

			// multi account still the same
			assert_eq!(<MultiAccounts<Test>>::get(&multi_id), Some(MultiAccountData {
				threshold: 2,
				signatories: vec![1, 2, 3],
				deposit: 4,
				depositor: 1,
			}));

			assert_ok!(MultiAccount::cancel(Origin::signed(multi_id), multi_id, now(), hash));

			assert_ok!(MultiAccount::remove(Origin::signed(multi_id)));
			assert_eq!(<MultiAccounts<Test>>::get(&multi_id), None);
			expect_event(RawEvent::MultiAccountRemoved(multi_id));
		});
	}
}
