// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! # Multisig Module
//! A module for doing multisig dispatch.
//!
//! - [`multisig::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//!
//! ## Overview
//!
//! This module contains functionality for multi-signature dispatch, a (potentially) stateful
//! operation, allowing multiple signed
//! origins (accounts) to coordinate and dispatch a call from a well-known origin, derivable
//! deterministically from the set of account IDs and the threshold number of accounts from the
//! set that must approve it. In the case that the threshold is just one then this is a stateless
//! operation. This is useful for multisig wallets where cryptographic threshold signatures are
//! not available or desired.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
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
use sp_io::hashing::blake2_256;
use frame_support::{decl_module, decl_event, decl_error, decl_storage, Parameter, ensure, RuntimeDebug};
use frame_support::{traits::{Get, ReservableCurrency, Currency},
	weights::{Weight, GetDispatchInfo, constants::{WEIGHT_PER_NANOS, WEIGHT_PER_MICROS}},
	dispatch::{DispatchResultWithPostInfo, DispatchErrorWithPostInfo, PostDispatchInfo},
};
use frame_system::{self as system, ensure_signed, RawOrigin};
use sp_runtime::{DispatchError, DispatchResult, traits::{Dispatchable, Zero}};

mod tests;
mod benchmarking;

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
/// Just a bunch of bytes, but they should decode to a valid `Call`.
pub type OpaqueCall = Vec<u8>;

pub trait WeightInfo {
	fn as_multi_threshold_1(z: u32, ) -> Weight;
	fn as_multi_create(s: u32, z: u32, ) -> Weight;
	fn as_multi_create_store(s: u32, z: u32, ) -> Weight;
	fn as_multi_approve(s: u32, z: u32, ) -> Weight;
	fn as_multi_complete(s: u32, z: u32, ) -> Weight;
	fn approve_as_multi_create(s: u32, z: u32, ) -> Weight;
	fn approve_as_multi_approve(s: u32, z: u32, ) -> Weight;
	fn approve_as_multi_complete(s: u32, z: u32, ) -> Weight;
	fn cancel_as_multi(s: u32, z: u32, ) -> Weight;
	fn cancel_as_multi_store(s: u32, z: u32, ) -> Weight;
}

impl WeightInfo for () {
	fn as_multi_threshold_1(_z: u32, ) -> Weight { 1_000_000_000 }
	fn as_multi_create(_s: u32, _z: u32, ) -> Weight { 1_000_000_000 }
	fn as_multi_create_store(_s: u32, _z: u32, ) -> Weight { 1_000_000_000 }
	fn as_multi_approve(_s: u32, _z: u32, ) -> Weight { 1_000_000_000 }
	fn as_multi_complete(_s: u32, _z: u32, ) -> Weight { 1_000_000_000 }
	fn approve_as_multi_create(_s: u32, _z: u32, ) -> Weight { 1_000_000_000 }
	fn approve_as_multi_approve(_s: u32, _z: u32, ) -> Weight { 1_000_000_000 }
	fn approve_as_multi_complete(_s: u32, _z: u32, ) -> Weight { 1_000_000_000 }
	fn cancel_as_multi(_s: u32, _z: u32, ) -> Weight { 1_000_000_000 }
	fn cancel_as_multi_store(_s: u32, _z: u32, ) -> Weight { 1_000_000_000 }
}

/// Configuration trait.
pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

	/// The overarching call type.
	type Call: Parameter + Dispatchable<Origin=Self::Origin, PostInfo=PostDispatchInfo>
		+ GetDispatchInfo + From<frame_system::Call<Self>>;

	/// The currency mechanism.
	type Currency: ReservableCurrency<Self::AccountId>;

	/// The base amount of currency needed to reserve for creating a multisig execution or to store
	/// a dispatch call for later.
	///
	/// This is held for an additional storage item whose value size is
	/// `4 + sizeof((BlockNumber, Balance, AccountId))` bytes and whose key size is
	/// `32 + sizeof(AccountId)` bytes.
	type DepositBase: Get<BalanceOf<Self>>;

	/// The amount of currency needed per unit threshold when creating a multisig execution.
	///
	/// This is held for adding 32 bytes more into a pre-existing storage value.
	type DepositFactor: Get<BalanceOf<Self>>;

	/// The maximum amount of signatories allowed in the multisig.
	type MaxSignatories: Get<u16>;

	/// Weight information for extrinsics in this pallet.
	type WeightInfo: WeightInfo;
}

/// A global extrinsic index, formed as the extrinsic index within a block, together with that
/// block's height. This allows a transaction in which a multisig operation of a particular
/// composite was created to be uniquely identified.
#[derive(Copy, Clone, Eq, PartialEq, Encode, Decode, Default, RuntimeDebug)]
pub struct Timepoint<BlockNumber> {
	/// The height of the chain at the point in time.
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
	trait Store for Module<T: Trait> as Multisig {
		/// The set of open multisig operations.
		pub Multisigs: double_map
			hasher(twox_64_concat) T::AccountId, hasher(blake2_128_concat) [u8; 32]
			=> Option<Multisig<T::BlockNumber, BalanceOf<T>, T::AccountId>>;

		pub Calls: map hasher(identity) [u8; 32] => Option<(OpaqueCall, T::AccountId, BalanceOf<T>)>;
	}
}

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// Threshold must be 2 or greater.
		MinimumThreshold,
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
		/// The maximum weight information provided was too low.
		WeightTooLow,
		/// The data to be stored is already stored.
		AlreadyStored,
	}
}

decl_event! {
	/// Events type.
	pub enum Event<T> where
		AccountId = <T as system::Trait>::AccountId,
		BlockNumber = <T as system::Trait>::BlockNumber,
		CallHash = [u8; 32]
	{
		/// A new multisig operation has begun. [approving, multisig, call_hash]
		NewMultisig(AccountId, AccountId, CallHash),
		/// A multisig operation has been approved by someone. [approving, timepoint, multisig, call_hash]
		MultisigApproval(AccountId, Timepoint<BlockNumber>, AccountId, CallHash),
		/// A multisig operation has been executed. [approving, timepoint, multisig, call_hash]
		MultisigExecuted(AccountId, Timepoint<BlockNumber>, AccountId, CallHash, DispatchResult),
		/// A multisig operation has been cancelled. [cancelling, timepoint, multisig, call_hash]
		MultisigCancelled(AccountId, Timepoint<BlockNumber>, AccountId, CallHash),
	}
}

mod weight_of {
	use super::*;

	/// - Base Weight: 33.72 + 0.002 * Z µs
	/// - DB Weight: None
	/// - Plus Call Weight
	pub fn as_multi_threshold_1<T: Trait>(
		call_len: usize,
		call_weight: Weight,
	 ) -> Weight {
		(34 * WEIGHT_PER_MICROS)
			.saturating_add((2 * WEIGHT_PER_NANOS).saturating_mul(call_len as Weight))
			.saturating_add(call_weight)
	}

	/// - Base Weight:
	///     - Create:          38.82 + 0.121 * S + .001 * Z µs
	///     - Create w/ Store: 54.22 + 0.120 * S + .003 * Z µs
	///     - Approve:         29.86 + 0.143 * S + .001 * Z µs
	///     - Complete:        39.55 + 0.267 * S + .002 * Z µs
	/// - DB Weight:
	///     - Reads: Multisig Storage, [Caller Account], Calls, Depositor Account
	///     - Writes: Multisig Storage, [Caller Account], Calls, Depositor Account
	/// - Plus Call Weight
	pub fn as_multi<T: Trait>(
		sig_len: usize,
		call_len: usize,
		call_weight: Weight,
		calls_write: bool,
		refunded: bool,
	 ) -> Weight {
		call_weight
			.saturating_add(55 * WEIGHT_PER_MICROS)
			.saturating_add((250 * WEIGHT_PER_NANOS).saturating_mul(sig_len as Weight))
			.saturating_add((3 * WEIGHT_PER_NANOS).saturating_mul(call_len as Weight))
			.saturating_add(T::DbWeight::get().reads_writes(1, 1)) // Multisig read/write
			.saturating_add(T::DbWeight::get().reads(1)) // Calls read
			.saturating_add(T::DbWeight::get().writes(calls_write.into())) // Calls write
			.saturating_add(T::DbWeight::get().reads_writes(refunded.into(), refunded.into())) // Deposit refunded
	}
}

enum CallOrHash {
	Call(OpaqueCall, bool),
	Hash([u8; 32]),
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		/// Deposit one of this module's events by using the default implementation.
		fn deposit_event() = default;

		/// Immediately dispatch a multi-signature call using a single approval from the caller.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// - `other_signatories`: The accounts (other than the sender) who are part of the
		/// multi-signature, but do not participate in the approval process.
		/// - `call`: The call to be executed.
		///
		/// Result is equivalent to the dispatched result.
		///
		/// # <weight>
		/// O(Z + C) where Z is the length of the call and C its execution weight.
		/// -------------------------------
		/// - Base Weight: 33.72 + 0.002 * Z µs
		/// - DB Weight: None
		/// - Plus Call Weight
		/// # </weight>
		#[weight = (
			weight_of::as_multi_threshold_1::<T>(
				call.using_encoded(|c| c.len()),
				call.get_dispatch_info().weight
			),
			call.get_dispatch_info().class,
		)]
		fn as_multi_threshold_1(origin,
			other_signatories: Vec<T::AccountId>,
			call: Box<<T as Trait>::Call>,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let max_sigs = T::MaxSignatories::get() as usize;
			ensure!(!other_signatories.is_empty(), Error::<T>::TooFewSignatories);
			let other_signatories_len = other_signatories.len();
			ensure!(other_signatories_len < max_sigs, Error::<T>::TooManySignatories);
			let signatories = Self::ensure_sorted_and_insert(other_signatories, who.clone())?;

			let id = Self::multi_account_id(&signatories, 1);

			let call_len = call.using_encoded(|c| c.len());
			let result = call.dispatch(RawOrigin::Signed(id.clone()).into());

			result.map(|post_dispatch_info| post_dispatch_info.actual_weight
				.map(|actual_weight| weight_of::as_multi_threshold_1::<T>(
					call_len,
					actual_weight,
				))
				.into()
			).map_err(|err| match err.post_info.actual_weight {
				Some(actual_weight) => {
					let weight_used = weight_of::as_multi_threshold_1::<T>(
						call_len,
						actual_weight,
					);
					let post_info = Some(weight_used).into();
					let error = err.error.into();
					DispatchErrorWithPostInfo { post_info, error }
				},
				None => err,
			})
		}

		/// Register approval for a dispatch to be made from a deterministic composite account if
		/// approved by a total of `threshold - 1` of `other_signatories`.
		///
		/// If there are enough, then dispatch the call.
		///
		/// Payment: `DepositBase` will be reserved if this is the first approval, plus
		/// `threshold` times `DepositFactor`. It is returned once this dispatch happens or
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
		///   `DepositBase + threshold * DepositFactor`.
		/// -------------------------------
		/// - Base Weight:
		///     - Create:          41.89 + 0.118 * S + .002 * Z µs
		///     - Create w/ Store: 53.57 + 0.119 * S + .003 * Z µs
		///     - Approve:         31.39 + 0.136 * S + .002 * Z µs
		///     - Complete:        39.94 + 0.26  * S + .002 * Z µs
		/// - DB Weight:
		///     - Reads: Multisig Storage, [Caller Account], Calls (if `store_call`)
		///     - Writes: Multisig Storage, [Caller Account], Calls (if `store_call`)
		/// - Plus Call Weight
		/// # </weight>
		#[weight = weight_of::as_multi::<T>(
			other_signatories.len(),
			call.len(),
			*max_weight,
			true, // assume worst case: calls write
			true, // assume worst case: refunded
		)]
		fn as_multi(origin,
			threshold: u16,
			other_signatories: Vec<T::AccountId>,
			maybe_timepoint: Option<Timepoint<T::BlockNumber>>,
			call: OpaqueCall,
			store_call: bool,
			max_weight: Weight,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			Self::operate(who, threshold, other_signatories, maybe_timepoint, CallOrHash::Call(call, store_call), max_weight)
		}

		/// Register approval for a dispatch to be made from a deterministic composite account if
		/// approved by a total of `threshold - 1` of `other_signatories`.
		///
		/// Payment: `DepositBase` will be reserved if this is the first approval, plus
		/// `threshold` times `DepositFactor`. It is returned once this dispatch happens or
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
		///   `DepositBase + threshold * DepositFactor`.
		/// ----------------------------------
		/// - Base Weight:
		///     - Create: 44.71 + 0.088 * S
		///     - Approve: 31.48 + 0.116 * S
		/// - DB Weight:
		///     - Read: Multisig Storage, [Caller Account]
		///     - Write: Multisig Storage, [Caller Account]
		/// # </weight>
		#[weight = weight_of::as_multi::<T>(
			other_signatories.len(),
			0, // call_len is zero in this case
			*max_weight,
			true, // assume worst case: calls write
			true, // assume worst case: refunded
		)]
		fn approve_as_multi(origin,
			threshold: u16,
			other_signatories: Vec<T::AccountId>,
			maybe_timepoint: Option<Timepoint<T::BlockNumber>>,
			call_hash: [u8; 32],
			max_weight: Weight,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			Self::operate(who, threshold, other_signatories, maybe_timepoint, CallOrHash::Hash(call_hash), max_weight)
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
		/// ----------------------------------
		/// - Base Weight: 36.07 + 0.124 * S
		/// - DB Weight:
		///     - Read: Multisig Storage, [Caller Account], Refund Account, Calls
		///     - Write: Multisig Storage, [Caller Account], Refund Account, Calls
		/// # </weight>
		#[weight = T::DbWeight::get().reads_writes(3, 3)
			.saturating_add(36 * WEIGHT_PER_MICROS)
			.saturating_add((other_signatories.len() as Weight).saturating_mul(100 * WEIGHT_PER_NANOS))
		]
		fn cancel_as_multi(origin,
			threshold: u16,
			other_signatories: Vec<T::AccountId>,
			timepoint: Timepoint<T::BlockNumber>,
			call_hash: [u8; 32],
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			ensure!(threshold >= 2, Error::<T>::MinimumThreshold);
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
			<Multisigs<T>>::remove(&id, &call_hash);
			Self::clear_call(&call_hash);

			Self::deposit_event(RawEvent::MultisigCancelled(who, timepoint, id, call_hash));
			Ok(())
		}
	}
}

impl<T: Trait> Module<T> {
	/// Derive a multi-account ID from the sorted list of accounts and the threshold that are
	/// required.
	///
	/// NOTE: `who` must be sorted. If it is not, then you'll get the wrong answer.
	pub fn multi_account_id(who: &[T::AccountId], threshold: u16) -> T::AccountId {
		let entropy = (b"modlpy/utilisuba", who, threshold).using_encoded(blake2_256);
		T::AccountId::decode(&mut &entropy[..]).unwrap_or_default()
	}

	fn operate(
		who: T::AccountId,
		threshold: u16,
		other_signatories: Vec<T::AccountId>,
		maybe_timepoint: Option<Timepoint<T::BlockNumber>>,
		call_or_hash: CallOrHash,
		max_weight: Weight,
	) -> DispatchResultWithPostInfo {
		ensure!(threshold >= 2, Error::<T>::MinimumThreshold);
		let max_sigs = T::MaxSignatories::get() as usize;
		ensure!(!other_signatories.is_empty(), Error::<T>::TooFewSignatories);
		let other_signatories_len = other_signatories.len();
		ensure!(other_signatories_len < max_sigs, Error::<T>::TooManySignatories);
		let signatories = Self::ensure_sorted_and_insert(other_signatories, who.clone())?;

		let id = Self::multi_account_id(&signatories, threshold);

		// Threshold > 1; this means it's a multi-step operation. We extract the `call_hash`.
		let (call_hash, call_len, maybe_call, store) = match call_or_hash {
			CallOrHash::Call(call, should_store) => {
				let call_hash = blake2_256(&call);
				let call_len = call.len();
				(call_hash, call_len, Some(call), should_store)
			}
			CallOrHash::Hash(h) => (h, 0, None, false),
		};

		// Branch on whether the operation has already started or not.
		if let Some(mut m) = <Multisigs<T>>::get(&id, call_hash) {
			// Yes; ensure that the timepoint exists and agrees.
			let timepoint = maybe_timepoint.ok_or(Error::<T>::NoTimepoint)?;
			ensure!(m.when == timepoint, Error::<T>::WrongTimepoint);

			// Ensure that either we have not yet signed or that it is at threshold.
			let mut approvals = m.approvals.len() as u16;
			// We only bother with the approval if we're below threshold.
			let maybe_pos = m.approvals.binary_search(&who).err().filter(|_| approvals < threshold);
			// Bump approvals if not yet voted and the vote is needed.
			if maybe_pos.is_some() { approvals += 1; }

			// We only bother fetching/decoding call if we know that we're ready to execute.
			let maybe_approved_call = if approvals >= threshold {
				Self::get_call(&call_hash, maybe_call.as_ref().map(|c| c.as_ref()))
			} else { None };

			if let Some(call) = maybe_approved_call {
				// verify weight
				ensure!(call.get_dispatch_info().weight <= max_weight, Error::<T>::WeightTooLow);

				// Clean up storage before executing call to avoid an possibility of reentrancy
				// attack.
				<Multisigs<T>>::remove(&id, call_hash);
				Self::clear_call(&call_hash);
				T::Currency::unreserve(&m.depositor, m.deposit);

				let result = call.dispatch(RawOrigin::Signed(id.clone()).into());
				Self::deposit_event(RawEvent::MultisigExecuted(
					who, timepoint, id, call_hash, result.map(|_| ()).map_err(|e| e.error)
				));
				Ok(get_result_weight(result).map(|actual_weight| weight_of::as_multi::<T>(
					other_signatories_len,
					call_len,
					actual_weight,
					true, // Call is removed
					true, // User is refunded
				)).into())
			} else {
				// We cannot dispatch the call now; either it isn't available, or it is, but we
				// don't have threshold approvals even with our signature.

				// Store the call if desired.
				let stored = if let Some(data) = maybe_call.filter(|_| store) {
					Self::store_call_and_reserve(who.clone(), &call_hash, data, BalanceOf::<T>::zero())?;
					true
				} else {
					false
				};

				if let Some(pos) = maybe_pos {
					// Record approval.
					m.approvals.insert(pos, who.clone());
					<Multisigs<T>>::insert(&id, call_hash, m);
					Self::deposit_event(RawEvent::MultisigApproval(who, timepoint, id, call_hash));
				} else {
					// If we already approved and didn't store the Call, then this was useless and
					// we report an error.
					ensure!(stored, Error::<T>::AlreadyApproved);
				}

				// Call is not made, so the actual weight does not include call
				Ok(Some(weight_of::as_multi::<T>(
					other_signatories_len,
					call_len,
					0,
					stored, // Call stored?
					false, // No refund
				)).into())
			}
		} else {
			// Not yet started; there should be no timepoint given.
			ensure!(maybe_timepoint.is_none(), Error::<T>::UnexpectedTimepoint);

			// Just start the operation by recording it in storage.
			let deposit = T::DepositBase::get() + T::DepositFactor::get() * threshold.into();

			// Store the call if desired.
			let stored = if let Some(data) = maybe_call.filter(|_| store) {
				Self::store_call_and_reserve(who.clone(), &call_hash, data, deposit)?;
				true
			} else {
				T::Currency::reserve(&who, deposit)?;
				false
			};

			<Multisigs<T>>::insert(&id, call_hash, Multisig {
				when: Self::timepoint(),
				deposit,
				depositor: who.clone(),
				approvals: vec![who.clone()],
			});
			Self::deposit_event(RawEvent::NewMultisig(who, id, call_hash));
			// Call is not made, so we can return that weight
			return Ok(Some(weight_of::as_multi::<T>(
				other_signatories_len,
				call_len,
				0,
				stored, // Call stored?
				false, // No refund
			)).into())
		}
	}

	/// Place a call's encoded data in storage, reserving funds as appropriate.
	///
	/// We store `data` here because storing `call` would result in needing another `.encode`.
	///
	/// Returns a `bool` indicating whether the data did end up being stored.
	fn store_call_and_reserve(
		who: T::AccountId,
		hash: &[u8; 32],
		data: OpaqueCall,
		other_deposit: BalanceOf<T>,
	) -> DispatchResult {
		ensure!(!Calls::<T>::contains_key(hash), Error::<T>::AlreadyStored);
		let deposit = other_deposit + T::DepositBase::get()
			+ T::DepositFactor::get() * BalanceOf::<T>::from(((data.len() + 31) / 32) as u32);
		T::Currency::reserve(&who, deposit)?;
		Calls::<T>::insert(&hash, (data, who, deposit));
		Ok(())
	}

	/// Attempt to decode and return the call, provided by the user or from storage.
	fn get_call(hash: &[u8; 32], maybe_known: Option<&[u8]>) -> Option<<T as Trait>::Call> {
		maybe_known.map_or_else(|| {
			Calls::<T>::get(hash).and_then(|(data, ..)| {
				Decode::decode(&mut &data[..]).ok()
			})
		}, |data| {
			Decode::decode(&mut &data[..]).ok()
		})
	}

	/// Attempt to remove a call from storage, returning any deposit on it to the owner.
	fn clear_call(hash: &[u8; 32]) {
		if let Some((_, who, deposit)) = Calls::<T>::take(hash) {
			T::Currency::unreserve(&who, deposit);
		}
	}

	/// The current `Timepoint`.
	pub fn timepoint() -> Timepoint<T::BlockNumber> {
		Timepoint {
			height: <system::Module<T>>::block_number(),
			index: <system::Module<T>>::extrinsic_index().unwrap_or_default(),
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

/// Return the weight of a dispatch call result as an `Option`.
///
/// Will return the weight regardless of what the state of the result is.
fn get_result_weight(result: DispatchResultWithPostInfo) -> Option<Weight> {
	match result {
		Ok(post_info) => post_info.actual_weight,
		Err(err) => err.post_info.actual_weight,
	}
}
