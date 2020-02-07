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

//! # Utility Module
//! A module with helpers for dispatch management.
//!
//! - [`utility::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//!
//! ## Overview
//!
//! This module contains three basic pieces of functionality, two of which are stateless:
//! - Batch dispatch: A stateless operation, allowing any origin to execute multiple calls in a
//!   single dispatch. This can be useful to amalgamate proposals, combining `set_code` with
//!   corresponding `set_storage`s, for efficient multiple payouts with just a single signature
//!   verify, or in combination with one of the other two dispatch functionality.
//! - Pseudonymal dispatch: A stateless operation, allowing a signed origin to execute a call from
//!   an alternative signed origin. Each account has 2**16 possible "pseudonyms" (alternative
//!   account IDs) and these can be stacked. This can be useful as a key management tool, where you
//!   need multiple distinct accounts (e.g. as controllers for many staking accounts), but where
//!   it's perfectly fine to have each of them controlled by the same underlying keypair.
//! - Multisig dispatch (stateful): A potentially stateful operation, allowing multiple signed
//!   origins (accounts) to coordinate and dispatch a call from a well-known origin, derivable
//!   deterministically from the set of account IDs and the threshold number of accounts from the
//!   set that must approve it. In the case that the threshold is just one then this is a stateless
//!   operation. This is useful for multisig wallets where cryptographic threshold signatures are
//!   not available or desired.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! #### For batch dispatch
//! * `batch` - Dispatch multiple calls from the sender's origin.
//!
//! #### For pseudonymal dispatch
//! * `as_sub` - Dispatch a call from a secondary ("sub") signed origin.
//!
//! #### For multisig dispatch
//! * `as_multi` - Approve and if possible dispatch a call from a composite origin formed from a
//!   number of signed origins.
//! * `approve_as_multi` - Approve a call from a composite origin.
//! * `cancel_as_multi` - Cancel a call from a composite origin.
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
	GetDispatchInfo, ClassifyDispatch, WeighData, Weight, DispatchClass, PaysFee
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
	trait Store for Module<T: Trait> as Utility {
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
		/// Multisig operation not found when attempting to cancel.
		NotFound,
		/// Only the account that originally created the multisig is able to cancel it.
		NotOwner,
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
		/// Batch of dispatches did not complete fully. Index of first failing dispatch given, as
		/// well as the error.
		BatchInterrupted(u32, DispatchError),
		/// Batch of dispatches completed fully with no error.
		BatchCompleted,
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
struct Passthrough<Call>(sp_std::marker::PhantomData<Call>);

impl<Call> Passthrough<Call> {
	fn new() -> Self { Self(Default::default()) }
}
impl<Call: GetDispatchInfo> WeighData<(&u16, &Box<Call>)> for Passthrough<Call> {
	fn weigh_data(&self, (_, call): (&u16, &Box<Call>)) -> Weight {
		call.get_dispatch_info().weight + 10_000
	}
}
impl<Call: GetDispatchInfo> ClassifyDispatch<(&u16, &Box<Call>)> for Passthrough<Call> {
	fn classify_dispatch(&self, (_, call): (&u16, &Box<Call>)) -> DispatchClass {
		call.get_dispatch_info().class
	}
}
impl<Call: GetDispatchInfo> PaysFee<(&u16, &Box<Call>)> for Passthrough<Call> {
	fn pays_fee(&self, (_, call): (&u16, &Box<Call>)) -> bool {
		call.get_dispatch_info().pays_fee
	}
}

/// Sumation pass-through for the weight function of the batch call.
///
/// This just adds all of the weights together of all of the calls.
struct BatchPassthrough<Call>(sp_std::marker::PhantomData<Call>);

impl<Call> BatchPassthrough<Call> {
	fn new() -> Self { Self(Default::default()) }
}
impl<Call: GetDispatchInfo> WeighData<(&Vec<Call>,)> for BatchPassthrough<Call> {
	fn weigh_data(&self, (calls,): (&Vec<Call>,)) -> Weight {
		calls.iter()
			.map(|call| call.get_dispatch_info().weight)
			.fold(10_000, |a, n| a + n)
	}
}
impl<Call: GetDispatchInfo> ClassifyDispatch<(&Vec<Call>,)> for BatchPassthrough<Call> {
	fn classify_dispatch(&self, (calls,): (&Vec<Call>,)) -> DispatchClass {
		let all_operational = calls.iter()
			.map(|call| call.get_dispatch_info().class)
			.all(|class| class == DispatchClass::Operational);
		if all_operational {
			DispatchClass::Operational
		} else {
			DispatchClass::Normal
		}
	}
}
impl<Call: GetDispatchInfo> PaysFee<(&Vec<Call>,)> for BatchPassthrough<Call> {
	fn pays_fee(&self, (calls,): (&Vec<Call>,)) -> bool {
		calls.iter()
			.any(|call| call.get_dispatch_info().pays_fee)
	}
}

/// Simple index-based pass through for the weight functions.
struct MultiPassthrough<Call, AccountId, Timepoint>(
	sp_std::marker::PhantomData<(Call, AccountId, Timepoint)>
);

impl<Call, AccountId, Timepoint> MultiPassthrough<Call, AccountId, Timepoint> {
	fn new() -> Self { Self(Default::default()) }
}
impl<Call: GetDispatchInfo, AccountId, Timepoint> WeighData<(&u16, &Vec<AccountId>, &Timepoint, &Box<Call>)>
for MultiPassthrough<Call, AccountId, Timepoint>
{
	fn weigh_data(&self, (_, sigs, _, call): (&u16, &Vec<AccountId>, &Timepoint, &Box<Call>)) -> Weight {
		call.get_dispatch_info().weight + 10_000 * (sigs.len() as u32 + 1)
	}
}
impl<Call: GetDispatchInfo, AccountId, Timepoint> ClassifyDispatch<(&u16, &Vec<AccountId>, &Timepoint, &Box<Call>)>
for MultiPassthrough<Call, AccountId, Timepoint>
{
	fn classify_dispatch(&self, (_, _, _, call): (&u16, &Vec<AccountId>, &Timepoint, &Box<Call>))
		-> DispatchClass
	{
		call.get_dispatch_info().class
	}
}
impl<Call: GetDispatchInfo, AccountId, Timepoint> PaysFee<(&u16, &Vec<AccountId>, &Timepoint, &Box<Call>)>
for MultiPassthrough<Call, AccountId, Timepoint>
{
	fn pays_fee(&self, _: (&u16, &Vec<AccountId>, &Timepoint, &Box<Call>)) -> bool {
		true
	}
}

/// Simple index-based pass through for the weight functions.
struct SigsLen<AccountId, Timepoint>(
	sp_std::marker::PhantomData<(AccountId, Timepoint)>
);

impl<AccountId, Timepoint> SigsLen<AccountId, Timepoint> {
	fn new() -> Self { Self(Default::default()) }
}
impl<AccountId, Timepoint> WeighData<(&u16, &Vec<AccountId>, &Timepoint, &[u8; 32])>
for SigsLen<AccountId, Timepoint>
{
	fn weigh_data(&self, (_, sigs, _, _): (&u16, &Vec<AccountId>, &Timepoint, &[u8; 32])) -> Weight {
		10_000 * (sigs.len() as u32 + 1)
	}
}
impl<AccountId, Timepoint> ClassifyDispatch<(&u16, &Vec<AccountId>, &Timepoint, &[u8; 32])>
for SigsLen<AccountId, Timepoint>
{
	fn classify_dispatch(&self, _: (&u16, &Vec<AccountId>, &Timepoint, &[u8; 32]))
		-> DispatchClass
	{
		DispatchClass::Normal
	}
}
impl<AccountId, Timepoint> PaysFee<(&u16, &Vec<AccountId>, &Timepoint, &[u8; 32])>
for SigsLen<AccountId, Timepoint>
{
	fn pays_fee(&self, _: (&u16, &Vec<AccountId>, &Timepoint, &[u8; 32])) -> bool {
		true
	}
}

/// A module identifier. These are per module and should be stored in a registry somewhere.
#[derive(Clone, Copy, Eq, PartialEq, Encode, Decode)]
struct IndexedUtilityModuleId(u16);

impl TypeId for IndexedUtilityModuleId {
	const TYPE_ID: [u8; 4] = *b"suba";
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		/// Deposit one of this module's events by using the default implementation.
		fn deposit_event() = default;

		/// Send a batch of dispatch calls.
		///
		/// This will execute until the first one fails and then stop.
		///
		/// May be called from any origin.
		///
		/// - `calls`: The calls to be dispatched from the same origin.
		///
		/// # <weight>
		/// - The sum of the weights of the `calls`.
		/// - One event.
		/// # </weight>
		///
		/// This will return `Ok` in all circumstances. To determine the success of the batch, an
		/// event is deposited. If a call failed and the batch was interrupted, then the
		/// `BatchInterrupted` event is deposited, along with the number of successful calls made
		/// and the error of the failed call. If all were successful, then the `BatchCompleted`
		/// event is deposited.
		#[weight = <BatchPassthrough<<T as Trait>::Call>>::new()]
		fn batch(origin, calls: Vec<<T as Trait>::Call>) {
			for (index, call) in calls.into_iter().enumerate() {
				let result = call.dispatch(origin.clone());
				if let Err(e) = result {
					Self::deposit_event(Event::<T>::BatchInterrupted(index as u32, e));
					return Ok(());
				}
			}
			Self::deposit_event(Event::<T>::BatchCompleted);
		}

		/// Send a call through an indexed pseudonym of the sender.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// # <weight>
		/// - The weight of the `call`.
		/// # </weight>
		#[weight = <Passthrough<<T as Trait>::Call>>::new()]
		fn as_sub(origin, index: u16, call: Box<<T as Trait>::Call>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let pseudonym = Self::sub_account_id(who, index);
			call.dispatch(frame_system::RawOrigin::Signed(pseudonym).into())
		}

		/// Register approval for a dispatch to be made from a deterministic composite account if
		/// approved by a total of `threshold - 1` of `other_signatories`.
		///
		/// If there are enough, then dispatch the call.
		///
		/// Payment: `MultisigDepositBase` will be reserved if this is the first approval, plus
		/// `threshold` times `MultisigDepositFactor`. It is returned once this dispatch happens or
		/// is cancelled.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// - `threshold`: The total number of approvals for this dispatch before it is executed.
		/// - `other_signatories`: The accounts (other than the sender) who can approve this
		/// dispatch. May not be empty.
		/// - `maybe_timepoint`: If this is the first approval, then this must be `None`. If it is
		/// not the first approval, then it must be `Some`, with the timepoint (block number and
		/// transaction index) of the first approval transaction.
		/// - `call`: The call to be executed.
		///
		/// NOTE: Unless this is the final approval, you will generally want to use
		/// `approve_as_multi` instead, since it only requires a hash of the call.
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
		/// - Up to one binary search and insert (`O(logS + S)`).
		/// - I/O: 1 read `O(S)`, up to 1 mutate `O(S)`. Up to one remove.
		/// - One event.
		/// - The weight of the `call`.
		/// - Storage: inserts one item, value size bounded by `MaxSignatories`, with a
		///   deposit taken for its lifetime of
		///   `MultisigDepositBase + threshold * MultisigDepositFactor`.
		/// # </weight>
		#[weight = <MultiPassthrough<<T as Trait>::Call, T::AccountId, Option<Timepoint<T::BlockNumber>>>>::new()]
		fn as_multi(origin,
			threshold: u16,
			other_signatories: Vec<T::AccountId>,
			maybe_timepoint: Option<Timepoint<T::BlockNumber>>,
			call: Box<<T as Trait>::Call>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			ensure!(threshold >= 1, Error::<T>::ZeroThreshold);
			let max_sigs = T::MaxSignatories::get() as usize;
			ensure!(!other_signatories.is_empty(), Error::<T>::TooFewSignatories);
			ensure!(other_signatories.len() < max_sigs, Error::<T>::TooManySignatories);
			let signatories = Self::ensure_sorted_and_insert(other_signatories, who.clone())?;

			let id = Self::multi_account_id(&signatories, threshold);
			let call_hash = call.using_encoded(blake2_256);

			if let Some(mut m) = <Multisigs<T>>::get(&id, call_hash) {
				let timepoint = maybe_timepoint.ok_or(Error::<T>::NoTimepoint)?;
				ensure!(m.when == timepoint, Error::<T>::WrongTimepoint);
				if let Err(pos) = m.approvals.binary_search(&who) {
					// we know threshold is greater than zero from the above ensure.
					if (m.approvals.len() as u16) < threshold - 1 {
						m.approvals.insert(pos, who.clone());
						<Multisigs<T>>::insert(&id, call_hash, m);
						Self::deposit_event(RawEvent::MultisigApproval(who, timepoint, id));
						return Ok(())
					}
				} else {
					if (m.approvals.len() as u16) < threshold {
						Err(Error::<T>::AlreadyApproved)?
					}
				}

				let result = call.dispatch(frame_system::RawOrigin::Signed(id.clone()).into());
				let _ = T::Currency::unreserve(&m.depositor, m.deposit);
				<Multisigs<T>>::remove(&id, call_hash);
				Self::deposit_event(RawEvent::MultisigExecuted(who, timepoint, id, result));
			} else {
				ensure!(maybe_timepoint.is_none(), Error::<T>::UnexpectedTimepoint);
				if threshold > 1 {
					let deposit = T::MultisigDepositBase::get()
						+ T::MultisigDepositFactor::get() * threshold.into();
					T::Currency::reserve(&who, deposit)?;
					<Multisigs<T>>::insert(&id, call_hash, Multisig {
						when: Self::timepoint(),
						deposit,
						depositor: who.clone(),
						approvals: vec![who.clone()],
					});
					Self::deposit_event(RawEvent::NewMultisig(who, id));
				} else {
					return call.dispatch(frame_system::RawOrigin::Signed(id).into())
				}
			}
			Ok(())
		}

		/// Register approval for a dispatch to be made from a deterministic composite account if
		/// approved by a total of `threshold - 1` of `other_signatories`.
		///
		/// Payment: `MultisigDepositBase` will be reserved if this is the first approval, plus
		/// `threshold` times `MultisigDepositFactor`. It is returned once this dispatch happens or
		/// is cancelled.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// - `threshold`: The total number of approvals for this dispatch before it is executed.
		/// - `other_signatories`: The accounts (other than the sender) who can approve this
		/// dispatch. May not be empty.
		/// - `maybe_timepoint`: If this is the first approval, then this must be `None`. If it is
		/// not the first approval, then it must be `Some`, with the timepoint (block number and
		/// transaction index) of the first approval transaction.
		/// - `call_hash`: The hash of the call to be executed.
		///
		/// NOTE: If this is the final approval, you will want to use `as_multi` instead.
		///
		/// # <weight>
		/// - `O(S)`.
		/// - Up to one balance-reserve or unreserve operation.
		/// - One passthrough operation, one insert, both `O(S)` where `S` is the number of
		///   signatories. `S` is capped by `MaxSignatories`, with weight being proportional.
		/// - One encode & hash, both of complexity `O(S)`.
		/// - Up to one binary search and insert (`O(logS + S)`).
		/// - I/O: 1 read `O(S)`, up to 1 mutate `O(S)`. Up to one remove.
		/// - One event.
		/// - Storage: inserts one item, value size bounded by `MaxSignatories`, with a
		///   deposit taken for its lifetime of
		///   `MultisigDepositBase + threshold * MultisigDepositFactor`.
		/// # </weight>
		#[weight = <SigsLen<T::AccountId, Option<Timepoint<T::BlockNumber>>>>::new()]
		fn approve_as_multi(origin,
			threshold: u16,
			other_signatories: Vec<T::AccountId>,
			maybe_timepoint: Option<Timepoint<T::BlockNumber>>,
			call_hash: [u8; 32],
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			ensure!(threshold >= 1, Error::<T>::ZeroThreshold);
			let max_sigs = T::MaxSignatories::get() as usize;
			ensure!(!other_signatories.is_empty(), Error::<T>::TooFewSignatories);
			ensure!(other_signatories.len() < max_sigs, Error::<T>::TooManySignatories);
			let signatories = Self::ensure_sorted_and_insert(other_signatories, who.clone())?;

			let id = Self::multi_account_id(&signatories, threshold);

			if let Some(mut m) = <Multisigs<T>>::get(&id, call_hash) {
				let timepoint = maybe_timepoint.ok_or(Error::<T>::NoTimepoint)?;
				ensure!(m.when == timepoint, Error::<T>::WrongTimepoint);
				ensure!(m.approvals.len() < threshold as usize, Error::<T>::NoApprovalsNeeded);
				if let Err(pos) = m.approvals.binary_search(&who) {
					m.approvals.insert(pos, who.clone());
					<Multisigs<T>>::insert(&id, call_hash, m);
					Self::deposit_event(RawEvent::MultisigApproval(who, timepoint, id));
				} else {
					Err(Error::<T>::AlreadyApproved)?
				}
			} else {
				if threshold > 1 {
					ensure!(maybe_timepoint.is_none(), Error::<T>::UnexpectedTimepoint);
					let deposit = T::MultisigDepositBase::get()
						+ T::MultisigDepositFactor::get() * threshold.into();
					T::Currency::reserve(&who, deposit)?;
					<Multisigs<T>>::insert(&id, call_hash, Multisig {
						when: Self::timepoint(),
						deposit,
						depositor: who.clone(),
						approvals: vec![who.clone()],
					});
					Self::deposit_event(RawEvent::NewMultisig(who, id));
				} else {
					Err(Error::<T>::NoApprovalsNeeded)?
				}
			}
			Ok(())
		}

		/// Cancel a pre-existing, on-going multisig transaction. Any deposit reserved previously
		/// for this operation will be unreserved on success.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// - `threshold`: The total number of approvals for this dispatch before it is executed.
		/// - `other_signatories`: The accounts (other than the sender) who can approve this
		/// dispatch. May not be empty.
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
		#[weight = <SigsLen<T::AccountId, Timepoint<T::BlockNumber>>>::new()]
		fn cancel_as_multi(origin,
			threshold: u16,
			other_signatories: Vec<T::AccountId>,
			timepoint: Timepoint<T::BlockNumber>,
			call_hash: [u8; 32],
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			ensure!(threshold >= 1, Error::<T>::ZeroThreshold);
			let max_sigs = T::MaxSignatories::get() as usize;
			ensure!(!other_signatories.is_empty(), Error::<T>::TooFewSignatories);
			ensure!(other_signatories.len() < max_sigs, Error::<T>::TooManySignatories);
			let signatories = Self::ensure_sorted_and_insert(other_signatories, who.clone())?;

			let id = Self::multi_account_id(&signatories, threshold);

			let m = <Multisigs<T>>::get(&id, call_hash)
				.ok_or(Error::<T>::NotFound)?;
			ensure!(m.when == timepoint, Error::<T>::WrongTimepoint);
			ensure!(m.depositor == who, Error::<T>::NotOwner);

			let _ = T::Currency::unreserve(&m.depositor, m.deposit);
			<Multisigs<T>>::remove(&id, call_hash);

			Self::deposit_event(RawEvent::MultisigCancelled(who, timepoint, id));
			Ok(())
		}
	}
}

impl<T: Trait> Module<T> {
	/// Derive a sub-account ID from the owner account and the sub-account index.
	pub fn sub_account_id(who: T::AccountId, index: u16) -> T::AccountId {
		let entropy = (b"modlpy/utilisuba", who, index).using_encoded(blake2_256);
		T::AccountId::decode(&mut &entropy[..]).unwrap_or_default()
	}

	/// Derive a multi-account ID from the sorted list of accounts and the threshold that are
	/// required.
	///
	/// NOTE: `who` must be sorted. If it is not, then you'll get the wrong answer.
	pub fn multi_account_id(who: &[T::AccountId], threshold: u16) -> T::AccountId {
		let entropy = (b"modlpy/utilisuba", who, threshold).using_encoded(blake2_256);
		T::AccountId::decode(&mut &entropy[..]).unwrap_or_default()
	}

	/// The current `Timepoint`.
	pub fn timepoint() -> Timepoint<T::BlockNumber> {
		Timepoint {
			height: <system::Module<T>>::block_number(),
			index: <system::Module<T>>::extrinsic_count(),
		}
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
	use crate as utility;

	impl_outer_origin! {
		pub enum Origin for Test where system = frame_system {}
	}

	impl_outer_event! {
		pub enum TestEvent for Test {
			pallet_balances<T>,
			utility<T>,
		}
	}
	impl_outer_dispatch! {
		pub enum Call for Test where origin: Origin {
			pallet_balances::Balances,
			utility::Utility,
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
	}
	parameter_types! {
		pub const ExistentialDeposit: u64 = 0;
		pub const CreationFee: u64 = 0;
	}
	impl pallet_balances::Trait for Test {
		type Balance = u64;
		type OnReapAccount = System;
		type OnNewAccount = ();
		type Event = TestEvent;
		type TransferPayment = ();
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type CreationFee = CreationFee;
	}
	parameter_types! {
		pub const MultisigDepositBase: u64 = 1;
		pub const MultisigDepositFactor: u64 = 1;
		pub const MaxSignatories: u16 = 3;
	}
	impl Trait for Test {
		type Event = TestEvent;
		type Call = Call;
		type Currency = Balances;
		type MultisigDepositBase = MultisigDepositBase;
		type MultisigDepositFactor = MultisigDepositFactor;
		type MaxSignatories = MaxSignatories;
	}
	type System = frame_system::Module<Test>;
	type Balances = pallet_balances::Module<Test>;
	type Utility = Module<Test>;

	use pallet_balances::Call as BalancesCall;
	use pallet_balances::Error as BalancesError;

	fn new_test_ext() -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		pallet_balances::GenesisConfig::<Test> {
			balances: vec![(1, 10), (2, 10), (3, 10), (4, 10), (5, 10)],
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
		Utility::timepoint()
	}

	#[test]
	fn multisig_deposit_is_taken_and_returned() {
		new_test_ext().execute_with(|| {
			let multi = Utility::multi_account_id(&[1, 2, 3][..], 2);
			assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			assert_ok!(Utility::as_multi(Origin::signed(1), 2, vec![2, 3], None, call.clone()));
			assert_eq!(Balances::free_balance(1), 2);
			assert_eq!(Balances::reserved_balance(1), 3);

			assert_ok!(Utility::as_multi(Origin::signed(2), 2, vec![1, 3], Some(now()), call));
			assert_eq!(Balances::free_balance(1), 5);
			assert_eq!(Balances::reserved_balance(1), 0);
		});
	}

	#[test]
	fn cancel_multisig_returns_deposit() {
		new_test_ext().execute_with(|| {
			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(Utility::approve_as_multi(Origin::signed(1), 3, vec![2, 3], None, hash.clone()));
			assert_ok!(Utility::approve_as_multi(Origin::signed(2), 3, vec![1, 3], Some(now()), hash.clone()));
			assert_eq!(Balances::free_balance(1), 6);
			assert_eq!(Balances::reserved_balance(1), 4);
			assert_ok!(
				Utility::cancel_as_multi(Origin::signed(1), 3, vec![2, 3], now(), hash.clone()),
			);
			assert_eq!(Balances::free_balance(1), 10);
			assert_eq!(Balances::reserved_balance(1), 0);
		});
	}

	#[test]
	fn timepoint_checking_works() {
		new_test_ext().execute_with(|| {
			let multi = Utility::multi_account_id(&[1, 2, 3][..], 2);
			assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);

			assert_noop!(
				Utility::approve_as_multi(Origin::signed(2), 2, vec![1, 3], Some(now()), hash.clone()),
				Error::<Test>::UnexpectedTimepoint,
			);

			assert_ok!(Utility::approve_as_multi(Origin::signed(1), 2, vec![2, 3], None, hash));

			assert_noop!(
				Utility::as_multi(Origin::signed(2), 2, vec![1, 3], None, call.clone()),
				Error::<Test>::NoTimepoint,
			);
			let later = Timepoint { index: 1, .. now() };
			assert_noop!(
				Utility::as_multi(Origin::signed(2), 2, vec![1, 3], Some(later), call.clone()),
				Error::<Test>::WrongTimepoint,
			);
		});
	}

	#[test]
	fn multisig_2_of_3_works() {
		new_test_ext().execute_with(|| {
			let multi = Utility::multi_account_id(&[1, 2, 3][..], 2);
			assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(Utility::approve_as_multi(Origin::signed(1), 2, vec![2, 3], None, hash));
			assert_eq!(Balances::free_balance(6), 0);

			assert_ok!(Utility::as_multi(Origin::signed(2), 2, vec![1, 3], Some(now()), call));
			assert_eq!(Balances::free_balance(6), 15);
		});
	}

	#[test]
	fn multisig_3_of_3_works() {
		new_test_ext().execute_with(|| {
			let multi = Utility::multi_account_id(&[1, 2, 3][..], 3);
			assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(Utility::approve_as_multi(Origin::signed(1), 3, vec![2, 3], None, hash.clone()));
			assert_ok!(Utility::approve_as_multi(Origin::signed(2), 3, vec![1, 3], Some(now()), hash.clone()));
			assert_eq!(Balances::free_balance(6), 0);

			assert_ok!(Utility::as_multi(Origin::signed(3), 3, vec![1, 2], Some(now()), call));
			assert_eq!(Balances::free_balance(6), 15);
		});
	}

	#[test]
	fn cancel_multisig_works() {
		new_test_ext().execute_with(|| {
			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(Utility::approve_as_multi(Origin::signed(1), 3, vec![2, 3], None, hash.clone()));
			assert_ok!(Utility::approve_as_multi(Origin::signed(2), 3, vec![1, 3], Some(now()), hash.clone()));
			assert_noop!(
				Utility::cancel_as_multi(Origin::signed(2), 3, vec![1, 3], now(), hash.clone()),
				Error::<Test>::NotOwner,
			);
			assert_ok!(
				Utility::cancel_as_multi(Origin::signed(1), 3, vec![2, 3], now(), hash.clone()),
			);
		});
	}

	#[test]
	fn multisig_2_of_3_as_multi_works() {
		new_test_ext().execute_with(|| {
			let multi = Utility::multi_account_id(&[1, 2, 3][..], 2);
			assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			assert_ok!(Utility::as_multi(Origin::signed(1), 2, vec![2, 3], None, call.clone()));
			assert_eq!(Balances::free_balance(6), 0);

			assert_ok!(Utility::as_multi(Origin::signed(2), 2, vec![1, 3], Some(now()), call));
			assert_eq!(Balances::free_balance(6), 15);
		});
	}

	#[test]
	fn multisig_2_of_3_as_multi_with_many_calls_works() {
		new_test_ext().execute_with(|| {
			let multi = Utility::multi_account_id(&[1, 2, 3][..], 2);
			assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

			let call1 = Box::new(Call::Balances(BalancesCall::transfer(6, 10)));
			let call2 = Box::new(Call::Balances(BalancesCall::transfer(7, 5)));

			assert_ok!(Utility::as_multi(Origin::signed(1), 2, vec![2, 3], None, call1.clone()));
			assert_ok!(Utility::as_multi(Origin::signed(2), 2, vec![1, 3], None, call2.clone()));
			assert_ok!(Utility::as_multi(Origin::signed(3), 2, vec![1, 2], Some(now()), call2));
			assert_ok!(Utility::as_multi(Origin::signed(3), 2, vec![1, 2], Some(now()), call1));

			assert_eq!(Balances::free_balance(6), 10);
			assert_eq!(Balances::free_balance(7), 5);
		});
	}

	#[test]
	fn multisig_2_of_3_cannot_reissue_same_call() {
		new_test_ext().execute_with(|| {
			let multi = Utility::multi_account_id(&[1, 2, 3][..], 2);
			assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 10)));
			assert_ok!(Utility::as_multi(Origin::signed(1), 2, vec![2, 3], None, call.clone()));
			assert_ok!(Utility::as_multi(Origin::signed(2), 2, vec![1, 3], Some(now()), call.clone()));
			assert_eq!(Balances::free_balance(multi), 5);

			assert_ok!(Utility::as_multi(Origin::signed(1), 2, vec![2, 3], None, call.clone()));
			assert_ok!(Utility::as_multi(Origin::signed(3), 2, vec![1, 2], Some(now()), call));

			let err = DispatchError::from(BalancesError::<Test, _>::InsufficientBalance).stripped();
			expect_event(RawEvent::MultisigExecuted(3, now(), multi, Err(err)));
		});
	}

	#[test]
	fn zero_threshold_fails() {
		new_test_ext().execute_with(|| {
			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			assert_noop!(
				Utility::as_multi(Origin::signed(1), 0, vec![2], None, call),
				Error::<Test>::ZeroThreshold,
			);
		});
	}

	#[test]
	fn too_many_signatories_fails() {
		new_test_ext().execute_with(|| {
			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			assert_noop!(
				Utility::as_multi(Origin::signed(1), 2, vec![2, 3, 4], None, call.clone()),
				Error::<Test>::TooManySignatories,
			);
		});
	}

	#[test]
	fn duplicate_approvals_are_ignored() {
		new_test_ext().execute_with(|| {
			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(Utility::approve_as_multi(Origin::signed(1), 2, vec![2, 3], None, hash.clone()));
			assert_noop!(
				Utility::approve_as_multi(Origin::signed(1), 2, vec![2, 3], Some(now()), hash.clone()),
				Error::<Test>::AlreadyApproved,
			);
			assert_ok!(Utility::approve_as_multi(Origin::signed(2), 2, vec![1, 3], Some(now()), hash.clone()));
			assert_noop!(
				Utility::approve_as_multi(Origin::signed(3), 2, vec![1, 2], Some(now()), hash.clone()),
				Error::<Test>::NoApprovalsNeeded,
			);
		});
	}

	#[test]
	fn multisig_1_of_3_works() {
		new_test_ext().execute_with(|| {
			let multi = Utility::multi_account_id(&[1, 2, 3][..], 1);
			assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);
			assert_noop!(
				Utility::approve_as_multi(Origin::signed(1), 1, vec![2, 3], None, hash.clone()),
				Error::<Test>::NoApprovalsNeeded,
			);
			assert_noop!(
				Utility::as_multi(Origin::signed(4), 1, vec![2, 3], None, call.clone()),
				BalancesError::<Test, _>::InsufficientBalance,
			);
			assert_ok!(Utility::as_multi(Origin::signed(1), 1, vec![2, 3], None, call));

			assert_eq!(Balances::free_balance(6), 15);
		});
	}

	#[test]
	fn as_sub_works() {
		new_test_ext().execute_with(|| {
			let sub_1_0 = Utility::sub_account_id(1, 0);
			assert_ok!(Balances::transfer(Origin::signed(1), sub_1_0, 5));
			assert_noop!(Utility::as_sub(
				Origin::signed(1),
				1,
				Box::new(Call::Balances(BalancesCall::transfer(6, 3))),
			), BalancesError::<Test, _>::InsufficientBalance);
			assert_ok!(Utility::as_sub(
				Origin::signed(1),
				0,
				Box::new(Call::Balances(BalancesCall::transfer(2, 3))),
			));
			assert_eq!(Balances::free_balance(sub_1_0), 2);
			assert_eq!(Balances::free_balance(2), 13);
		});
	}

	#[test]
	fn batch_with_root_works() {
		new_test_ext().execute_with(|| {
			assert_eq!(Balances::free_balance(1), 10);
			assert_eq!(Balances::free_balance(2), 10);
			assert_ok!(Utility::batch(Origin::ROOT, vec![
				Call::Balances(BalancesCall::force_transfer(1, 2, 5)),
				Call::Balances(BalancesCall::force_transfer(1, 2, 5))
			]));
			assert_eq!(Balances::free_balance(1), 0);
			assert_eq!(Balances::free_balance(2), 20);
		});
	}

	#[test]
	fn batch_with_signed_works() {
		new_test_ext().execute_with(|| {
			assert_eq!(Balances::free_balance(1), 10);
			assert_eq!(Balances::free_balance(2), 10);
			assert_ok!(
				Utility::batch(Origin::signed(1), vec![
					Call::Balances(BalancesCall::transfer(2, 5)),
					Call::Balances(BalancesCall::transfer(2, 5))
				]),
			);
			assert_eq!(Balances::free_balance(1), 0);
			assert_eq!(Balances::free_balance(2), 20);
		});
	}

	#[test]
	fn batch_early_exit_works() {
		new_test_ext().execute_with(|| {
			assert_eq!(Balances::free_balance(1), 10);
			assert_eq!(Balances::free_balance(2), 10);
			assert_ok!(
				Utility::batch(Origin::signed(1), vec![
					Call::Balances(BalancesCall::transfer(2, 5)),
					Call::Balances(BalancesCall::transfer(2, 10)),
					Call::Balances(BalancesCall::transfer(2, 5)),
				]),
			);
			assert_eq!(Balances::free_balance(1), 5);
			assert_eq!(Balances::free_balance(2), 15);
		});
	}
}
