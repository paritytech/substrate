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
	SimpleDispatchInfo, GetDispatchInfo, ClassifyDispatch, WeighData, Weight, DispatchClass, PaysFee
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

/// Simple index-based pass through for the weight functions.
struct MultiPassthrough<Call, AccountId, Timepoint>(
	sp_std::marker::PhantomData<(Call, AccountId, Timepoint)>
);

impl<Call, AccountId, Timepoint> MultiPassthrough<Call, AccountId, Timepoint> {
	fn new() -> Self { Self(Default::default()) }
}
impl<Call: GetDispatchInfo, AccountId, Timepoint> WeighData<(&AccountId, &Timepoint, &Box<Call>)>
for MultiPassthrough<Call, AccountId, Timepoint>
{
	fn weigh_data(&self, (_, _, call): (&AccountId, &Timepoint, &Box<Call>)) -> Weight {
		call.get_dispatch_info().weight
	}
}
impl<Call: GetDispatchInfo, AccountId, Timepoint> ClassifyDispatch<(&AccountId, &Timepoint, &Box<Call>)>
for MultiPassthrough<Call, AccountId, Timepoint>
{
	fn classify_dispatch(&self, (_, _, call): (&AccountId, &Timepoint, &Box<Call>))
		-> DispatchClass
	{
		call.get_dispatch_info().class
	}
}
impl<Call: GetDispatchInfo, AccountId, Timepoint> PaysFee<(&AccountId, &Timepoint, &Box<Call>)>
for MultiPassthrough<Call, AccountId, Timepoint>
{
	fn pays_fee(&self, _: (&AccountId, &Timepoint, &Box<Call>)) -> bool {
		true
	}
}

/// Simple index-based pass through for the weight functions.
struct SigsLen<AccountId>(
	sp_std::marker::PhantomData<AccountId>
);

impl<AccountId> SigsLen<AccountId> {
	fn new() -> Self { Self(Default::default()) }
}
impl<AccountId> WeighData<(&u16, &Vec<AccountId>)>
for SigsLen<AccountId>
{
	fn weigh_data(&self, (_, sigs): (&u16, &Vec<AccountId>)) -> Weight {
		10_000 * (sigs.len() as u32 + 1)
	}
}
impl<AccountId> ClassifyDispatch<(&u16, &Vec<AccountId>)>
for SigsLen<AccountId>
{
	fn classify_dispatch(&self, _: (&u16, &Vec<AccountId>))
		-> DispatchClass
	{
		DispatchClass::Normal
	}
}
impl<AccountId> PaysFee<(&u16, &Vec<AccountId>)>
for SigsLen<AccountId>
{
	fn pays_fee(&self, _: (&u16, &Vec<AccountId>)) -> bool {
		true
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
		///    account. May not be empty.
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
		#[weight = <SigsLen<T::AccountId>>::new()]
		fn create(origin,
			threshold: u16,
			other_signatories: Vec<T::AccountId>
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			ensure!(threshold >= 1, Error::<T>::ZeroThreshold);
			let max_sigs = T::MaxSignatories::get() as usize;
			ensure!(!other_signatories.is_empty(), Error::<T>::TooFewSignatories);
			ensure!(threshold as usize <= other_signatories.len() + 1, Error::<T>::TooFewSignatories);
			ensure!(other_signatories.len() < max_sigs, Error::<T>::TooManySignatories);
			ensure!(other_signatories.len() < u32::max_value() as usize, Error::<T>::TooManySignatories);
			let signatories = Self::ensure_sorted_and_insert(other_signatories.clone(), who.clone())?;

			let multi_account_index = MultiAccountIndex::get()
				.checked_add(1)
				.expect("multi account indices will never reach 2^64 before the death of the universe; qed");

			let id = Self::multi_account_id(multi_account_index);

			let deposit = T::MultiAccountDepositBase::get()
				+ T::MultiAccountDepositFactor::get() * (other_signatories.len() as u32 + 1).into();

			MultiAccountIndex::put(multi_account_index);

			T::Currency::reserve(&who, deposit)?;

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
		/// Any removed signatories that have approved multisig transactions will no longer be counted as valid
		/// approvals. Removing a signatory that has initiated/is the owner of a multisig transaction will not
		/// cancel the multisig transaction, but the owner can always cancel the multisig transaction, even after
		/// leaving the signatories. Such a transaction can still be dispatched, as long as the threshold
		/// is met by the current signatories.
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
		#[weight = <SigsLen<T::AccountId>>::new()]
		fn update(origin,
			threshold: u16,
			signatories: Vec<T::AccountId>
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			ensure!(threshold >= 1, Error::<T>::ZeroThreshold);
			let max_sigs = T::MaxSignatories::get() as usize;
			ensure!(signatories.len() >= 2, Error::<T>::TooFewSignatories);
			ensure!(threshold as usize <= signatories.len(), Error::<T>::TooFewSignatories);
			ensure!(signatories.len() <= max_sigs, Error::<T>::TooManySignatories);
			ensure!(signatories.len() <= u32::max_value() as usize, Error::<T>::TooManySignatories);
			let signatories = Self::ensure_sorted(signatories.clone())?;

			if let Some(multi_account) = <MultiAccounts<T>>::get(&who) {
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
			} else {
				Err(Error::<T>::MultiAccountNotFound)?
			}

			Ok(())
		}

		/// Remove an existing multi account.
		///
		/// Payment: Previous deposits will be unreserved.
		///
		/// The dispatch origin for this call must be _Signed_ and be equal to the multi account ID. It can be
		/// dispatched by a `call` from this module.
		///
		/// Multisig transactions from the removed account will not be automatically cancelled, but they can no
		/// longer be approved or called. The owner can always cancel open multisig transaction, even after
		/// the multi account has been removed.
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

			if let Some(multi_account) = <MultiAccounts<T>>::get(&who) {
				let _ = T::Currency::unreserve(&multi_account.depositor, multi_account.deposit);

				<MultiAccounts<T>>::remove(&who);

				Self::deposit_event(RawEvent::MultiAccountRemoved(who));
			} else {
				Err(Error::<T>::MultiAccountNotFound)?
			}

			Ok(())
		}

		/// Register approval for a dispatch to be made from the given multi account if approved by a total of
		/// `threshold` of `signatories`, as specified in the multi account.
		///
		/// If there are enough approvals, then dispatch the call.
		///
		/// If one approving account is removed from the signatories of the multi account, it does
		/// no longer count as a valid approval for the multisig transaction. Removing the initiator/
		/// owner of a multisig transaction from the signatories will not cancel the multisig transaction.
		/// It can still be dispatched, as long as the threshold is met by the current signatories.
		/// Approvals fail if the multi account was removed.
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
		#[weight = <MultiPassthrough<<T as Trait>::Call, T::AccountId, Option<Timepoint<T::BlockNumber>>>>::new()]
		fn call(origin,
			multi_account_id: T::AccountId,
			maybe_timepoint: Option<Timepoint<T::BlockNumber>>,
			call: Box<<T as Trait>::Call>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			if let Some(multi_account) = <MultiAccounts<T>>::get(&multi_account_id) {
				// ensure that the origin is a signatory of the multi account
				if let Err(_) = multi_account.signatories.binary_search(&who) {
					Err(Error::<T>::NotSignatory)?
				}

				let call_hash = call.using_encoded(blake2_256);

				if let Some(mut m) = <Multisigs<T>>::get(&multi_account_id, call_hash) {
					let timepoint = maybe_timepoint.ok_or(Error::<T>::NoTimepoint)?;
					ensure!(m.when == timepoint, Error::<T>::WrongTimepoint);

					let valid_approvals = Self::filter_approvals(m.approvals.clone(),
						multi_account.signatories.clone());

					if let Err(pos) = m.approvals.binary_search(&who) {
						// we know threshold is greater than zero from the above ensure.
						if (valid_approvals.len() as u16) < multi_account.threshold - 1 {
							m.approvals.insert(pos, who.clone());
							<Multisigs<T>>::insert(&multi_account_id, call_hash, m);
							Self::deposit_event(RawEvent::MultisigApproval(who, timepoint, multi_account_id));
							return Ok(())
						}
					} else {
						if (valid_approvals.len() as u16) < multi_account.threshold {
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
			} else {
				Err(Error::<T>::MultiAccountNotFound)?
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
		/// Removing the initiator/owner of a multisig transaction from the multi account's signatories
		/// will not cancel the multisig transaction. It can still be dispatched, as long as the threshold
		/// is met by the current signatories. Approvals fail if the multi account was removed.
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

			if let Some(multi_account) = <MultiAccounts<T>>::get(&multi_account_id) {
				// ensure that the origin is a signatory of the multi account
				if let Err(_) = multi_account.signatories.binary_search(&who) {
					Err(Error::<T>::NotSignatory)?
				}

				if let Some(mut m) = <Multisigs<T>>::get(&multi_account_id, call_hash) {
					let timepoint = maybe_timepoint.ok_or(Error::<T>::NoTimepoint)?;
					ensure!(m.when == timepoint, Error::<T>::WrongTimepoint);

					let valid_approvals = Self::filter_approvals(m.approvals.clone(),
						multi_account.signatories.clone());

					ensure!(valid_approvals.len() < multi_account.threshold as usize, Error::<T>::NoApprovalsNeeded);
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
			} else {
				Err(Error::<T>::MultiAccountNotFound)?
			}
			Ok(())
		}

		/// Cancel a pre-existing, on-going multisig transaction. Any deposit reserved previously
		/// for this operation will be unreserved on success.
		///
		/// The dispatch origin for this call must be _Signed_ and must be the initiator (owner) of the multisig.
		///
		/// The multisig transaction is not automatically cancelled if the owner is removed from the multi account,
		/// nor is it cancelled if the multi account is removed. The multisig transaction can be cancelled by the
		/// owner even aftre being removed from the multi account, and it can also be cancelled if the multi account
		/// has been removed.
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
			ensure!(m.depositor == who, Error::<T>::NotOwner);

			let _ = T::Currency::unreserve(&m.depositor, m.deposit);
			<Multisigs<T>>::remove(&multi_account_id, call_hash);

			Self::deposit_event(RawEvent::MultisigCancelled(who, timepoint, multi_account_id));

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

	/// Check that signatories is sorted.
	fn ensure_sorted(signatories: Vec<T::AccountId>) -> Result<Vec<T::AccountId>, DispatchError> {
		let mut maybe_last = None;
		for item in signatories.iter() {
			if let Some(last) = maybe_last {
				ensure!(last < item, Error::<T>::SignatoriesOutOfOrder);
			}
			maybe_last = Some(item);
		}
		Ok(signatories)
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

	/// Remove approvals from account IDs that are no longer in the set of signatories
	fn filter_approvals(approvals: Vec<T::AccountId>, signatories: Vec<T::AccountId>) -> Vec<T::AccountId> {
		approvals.into_iter().filter(|approval| signatories.binary_search(&approval).is_ok()).collect()
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
		type OnReapAccount = Balances;
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
	fn multisig_deposit_is_taken_and_returned() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(1);
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
			let multi_id = MultiAccount::multi_account_id(1);
			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi_id, 5));

			assert_ok!(MultiAccount::create(Origin::signed(1), 2, vec![2, 3]));
			assert_eq!(<MultiAccounts<Test>>::get(&multi_id).unwrap(), MultiAccountData {
				threshold: 2,
				signatories: vec![1, 2, 3],
				deposit: 4,
				depositor: 1,
			});
			assert_eq!(Balances::free_balance(1), 11);
			assert_eq!(Balances::reserved_balance(1), 4);
			assert_eq!(Balances::free_balance(multi_id), 15);
			assert_eq!(Balances::reserved_balance(multi_id), 0);
			expect_event(RawEvent::NewMultiAccount(1, multi_id));

			assert_ok!(MultiAccount::update(Origin::signed(multi_id), 1, vec![1, 3]));
			assert_eq!(<MultiAccounts<Test>>::get(&multi_id).unwrap(), MultiAccountData {
				threshold: 1,
				signatories: vec![1, 3],
				deposit: 3,
				depositor: multi_id,
			});
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
			let multi_id = MultiAccount::multi_account_id(1);
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
			let multi_id = MultiAccount::multi_account_id(1);

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
			let multi_id = MultiAccount::multi_account_id(1);

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
			let multi_id = MultiAccount::multi_account_id(1);

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
			let multi_id = MultiAccount::multi_account_id(1);

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
			let multi_id = MultiAccount::multi_account_id(1);

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
			let multi_id = MultiAccount::multi_account_id(1);

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
			let multi_id = MultiAccount::multi_account_id(1);

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
	fn zero_threshold_fails() {
		new_test_ext().execute_with(|| {
			assert_noop!(
				MultiAccount::create(Origin::signed(1), 0, vec![2]),
				Error::<Test>::ZeroThreshold,
			);

			let multi_id = MultiAccount::multi_account_id(1);
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

			let multi_id = MultiAccount::multi_account_id(1);
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
			let multi_id = MultiAccount::multi_account_id(1);
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
			let multi_id = MultiAccount::multi_account_id(1);
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
			let multi_id = MultiAccount::multi_account_id(1);
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
			let multi_id = MultiAccount::multi_account_id(1);

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
			let multi_id = MultiAccount::multi_account_id(1);

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
			let multi_id = MultiAccount::multi_account_id(1);

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
	fn owner_can_still_cancel_after_leaving_signatories() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(1);
			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi_id, 5));

			assert_ok!(MultiAccount::create(Origin::signed(1), 2, vec![2, 3]));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(MultiAccount::approve(Origin::signed(2), multi_id, None, hash.clone()));
			assert_eq!(<Multisigs<Test>>::get(&multi_id, hash).unwrap(), Multisig {
				when: now(),
				deposit: 3,
				depositor: 2,
				approvals: vec![2],
			});
			assert_eq!(Balances::free_balance(2), 12);
			assert_eq!(Balances::reserved_balance(2), 3);

			assert_ok!(MultiAccount::update(Origin::signed(multi_id), 2, vec![1, 3]));
			// multisig has not changed
			assert_eq!(<Multisigs<Test>>::get(&multi_id, hash.clone()).unwrap(), Multisig {
				when: now(),
				deposit: 3,
				depositor: 2,
				approvals: vec![2],
			});

			assert_ok!(MultiAccount::cancel(Origin::signed(2), multi_id, now(), hash.clone()));
			// multisig successfully removed
			assert_eq!(<Multisigs<Test>>::get(&multi_id, hash), None);
			// deposit returned
			assert_eq!(Balances::free_balance(2), 15);
			assert_eq!(Balances::reserved_balance(2), 0);
			// event sent
			expect_event(RawEvent::MultisigCancelled(2, now(), multi_id));
		});
	}

	#[test]
	fn multisig_still_works_after_owner_left_signatories() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(1);
			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi_id, 5));

			assert_ok!(MultiAccount::create(Origin::signed(1), 2, vec![2, 3]));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 10)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(MultiAccount::approve(Origin::signed(2), multi_id, None, hash.clone()));
			assert_eq!(Balances::free_balance(2), 12);
			assert_eq!(Balances::reserved_balance(2), 3);

			assert_ok!(MultiAccount::update(Origin::signed(multi_id), 2, vec![1, 3]));

			assert_ok!(MultiAccount::approve(Origin::signed(1), multi_id, Some(now()), hash.clone()));
			assert_ok!(MultiAccount::call(Origin::signed(3), multi_id, Some(now()), call));
			// multisig successfully removed
			assert_eq!(<Multisigs<Test>>::get(&multi_id, hash), None);
			// deposit returned to owner, who is no longer one of the signatories
			assert_eq!(Balances::free_balance(2), 15);
			assert_eq!(Balances::reserved_balance(2), 0);
			// event sent
			expect_event(RawEvent::MultisigExecuted(3, now(), multi_id, Ok(())));
		});
	}

	#[test]
	fn multisig_only_counts_current_signatories_not_removed_ones() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(1);
			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi_id, 5));

			assert_ok!(MultiAccount::create(Origin::signed(1), 3, vec![2, 3]));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 10)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(MultiAccount::approve(Origin::signed(2), multi_id, None, hash.clone()));
			assert_ok!(MultiAccount::approve(Origin::signed(3), multi_id, Some(now()), hash.clone()));
			// multisig inserted
			assert_eq!(<Multisigs<Test>>::get(&multi_id, hash.clone()).unwrap(), Multisig {
				when: now(),
				deposit: 4,
				depositor: 2,
				approvals: vec![2, 3],
			});

			assert_ok!(MultiAccount::update(Origin::signed(multi_id), 3, vec![1, 2, 4]));
			assert_ok!(MultiAccount::call(Origin::signed(1), multi_id, Some(now()), call.clone()));
			// multisig still not removed, 3 approvals, but not from the right signatories
			assert_eq!(<Multisigs<Test>>::get(&multi_id, hash.clone()).unwrap(), Multisig {
				when: now(),
				deposit: 4,
				depositor: 2,
				approvals: vec![1, 2, 3],
			});
			// deposit not returned
			assert_eq!(Balances::free_balance(2), 11);
			assert_eq!(Balances::reserved_balance(2), 4);
			// event sent
			expect_event(RawEvent::MultisigApproval(1, now(), multi_id));

			assert_ok!(MultiAccount::call(Origin::signed(4), multi_id, Some(now()), call));
			// multisig successfully removed
			assert_eq!(<Multisigs<Test>>::get(&multi_id, hash), None);
			// deposit returned to owner, who is no longer one of the signatories
			assert_eq!(Balances::free_balance(2), 15);
			assert_eq!(Balances::reserved_balance(2), 0);
			// event sent
			expect_event(RawEvent::MultisigExecuted(4, now(), multi_id, Ok(())));
		});
	}

	#[test]
	fn multisig_cannot_be_approved_or_called_after_multiaccount_removed() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(1);
			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi_id, 5));

			assert_ok!(MultiAccount::create(Origin::signed(1), 2, vec![2, 3]));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 10)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(MultiAccount::approve(Origin::signed(2), multi_id, None, hash.clone()));

			assert_ok!(MultiAccount::remove(Origin::signed(multi_id)));

			assert_noop!(MultiAccount::approve(Origin::signed(3), multi_id, Some(now()), hash),
				Error::<Test>::MultiAccountNotFound);
			assert_noop!(MultiAccount::call(Origin::signed(3), multi_id, Some(now()), call),
				Error::<Test>::MultiAccountNotFound);
		});
	}

	#[test]
	fn multisig_can_still_be_cancelled_after_multiaccount_removed() {
		new_test_ext().execute_with(|| {
			let multi_id = MultiAccount::multi_account_id(1);
			assert_ok!(Balances::transfer(Origin::signed(1), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi_id, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi_id, 5));

			assert_ok!(MultiAccount::create(Origin::signed(1), 2, vec![2, 3]));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 10)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(MultiAccount::approve(Origin::signed(2), multi_id, None, hash.clone()));

			assert_ok!(MultiAccount::remove(Origin::signed(multi_id)));

			assert_ok!(MultiAccount::cancel(Origin::signed(2), multi_id, now(), hash));
		});
	}
}
