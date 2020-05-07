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
use frame_support::{traits::{Get, ReservableCurrency, Currency},
	weights::{Weight, GetDispatchInfo, DispatchClass, FunctionOf, Pays},
	dispatch::{DispatchResultWithPostInfo, DispatchErrorWithPostInfo, PostDispatchInfo},
};
use frame_system::{self as system, ensure_signed};
use sp_runtime::{DispatchError, DispatchResult, traits::Dispatchable};

mod tests;
mod benchmarking;

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

/// Configuration trait.
pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

	/// The overarching call type.
	type Call: Parameter + Dispatchable<Origin=Self::Origin, PostInfo=PostDispatchInfo> + GetDispatchInfo + From<frame_system::Call<Self>>;

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
		BlockNumber = <T as system::Trait>::BlockNumber,
		CallHash = [u8; 32]
	{
		/// Batch of dispatches did not complete fully. Index of first failing dispatch given, as
		/// well as the error.
		BatchInterrupted(u32, DispatchError),
		/// Batch of dispatches completed fully with no error.
		BatchCompleted,
		/// A new multisig operation has begun. First param is the account that is approving,
		/// second is the multisig account, third is hash of the call.
		NewMultisig(AccountId, AccountId, CallHash),
		/// A multisig operation has been approved by someone. First param is the account that is
		/// approving, third is the multisig account, fourth is hash of the call.
		MultisigApproval(AccountId, Timepoint<BlockNumber>, AccountId, CallHash),
		/// A multisig operation has been executed. First param is the account that is
		/// approving, third is the multisig account, fourth is hash of the call to be executed.
		MultisigExecuted(AccountId, Timepoint<BlockNumber>, AccountId, CallHash, DispatchResult),
		/// A multisig operation has been cancelled. First param is the account that is
		/// cancelling, third is the multisig account, fourth is hash of the call.
		MultisigCancelled(AccountId, Timepoint<BlockNumber>, AccountId, CallHash),
	}
}

/// A module identifier. These are per module and should be stored in a registry somewhere.
#[derive(Clone, Copy, Eq, PartialEq, Encode, Decode)]
struct IndexedUtilityModuleId(u16);

impl TypeId for IndexedUtilityModuleId {
	const TYPE_ID: [u8; 4] = *b"suba";
}

mod weight_of {
	use super::*;

	/// - Base Weight:
	///     - Create: 46.55 + 0.089 * S µs
	///     - Approve: 34.03 + .112 * S µs
	///     - Complete: 40.36 + .225 * S µs
	/// - DB Weight:
	///     - Reads: Multisig Storage, [Caller Account]
	///     - Writes: Multisig Storage, [Caller Account]
	/// - Plus Call Weight
	pub fn as_multi<T: Trait>(other_sig_len: usize, call_weight: Weight) -> Weight {
		call_weight
			.saturating_add(45_000_000)
			.saturating_add((other_sig_len as Weight).saturating_mul(250_000))
			.saturating_add(T::DbWeight::get().reads_writes(1, 1))
	}
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
		/// - Base weight: 14.39 + .987 * c µs
		/// - Plus the sum of the weights of the `calls`.
		/// - Plus one additional event. (repeat read/write)
		/// # </weight>
		///
		/// This will return `Ok` in all circumstances. To determine the success of the batch, an
		/// event is deposited. If a call failed and the batch was interrupted, then the
		/// `BatchInterrupted` event is deposited, along with the number of successful calls made
		/// and the error of the failed call. If all were successful, then the `BatchCompleted`
		/// event is deposited.
		#[weight = FunctionOf(
			|args: (&Vec<<T as Trait>::Call>,)| {
				args.0.iter()
					.map(|call| call.get_dispatch_info().weight)
					.fold(15_000_000, |a: Weight, n| a.saturating_add(n).saturating_add(1_000_000))
			},
			|args: (&Vec<<T as Trait>::Call>,)| {
				let all_operational = args.0.iter()
					.map(|call| call.get_dispatch_info().class)
					.all(|class| class == DispatchClass::Operational);
				if all_operational {
					DispatchClass::Operational
				} else {
					DispatchClass::Normal
				}
			},
			Pays::Yes,
		)]
		fn batch(origin, calls: Vec<<T as Trait>::Call>) {
			for (index, call) in calls.into_iter().enumerate() {
				let result = call.dispatch(origin.clone());
				if let Err(e) = result {
					Self::deposit_event(Event::<T>::BatchInterrupted(index as u32, e.error));
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
		/// - Base weight: 2.861 µs
		/// - Plus the weight of the `call`
		/// # </weight>
		#[weight = FunctionOf(
			|args: (&u16, &Box<<T as Trait>::Call>)| {
				args.1.get_dispatch_info().weight.saturating_add(3_000_000)
			},
			|args: (&u16, &Box<<T as Trait>::Call>)| args.1.get_dispatch_info().class,
			Pays::Yes,
		)]
		fn as_sub(origin, index: u16, call: Box<<T as Trait>::Call>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let pseudonym = Self::sub_account_id(who, index);
			call.dispatch(frame_system::RawOrigin::Signed(pseudonym).into())
				.map(|_| ()).map_err(|e| e.error)
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
		/// -------------------------------
		/// - Base Weight:
		///     - Create: 46.55 + 0.089 * S µs
		///     - Approve: 34.03 + .112 * S µs
		///     - Complete: 40.36 + .225 * S µs
		/// - DB Weight:
		///     - Reads: Multisig Storage, [Caller Account]
		///     - Writes: Multisig Storage, [Caller Account]
		/// - Plus Call Weight
		/// # </weight>
		#[weight = FunctionOf(
			|args: (&u16, &Vec<T::AccountId>, &Option<Timepoint<T::BlockNumber>>, &Box<<T as Trait>::Call>)| {
				weight_of::as_multi::<T>(args.1.len(),args.3.get_dispatch_info().weight)
			},
			|args: (&u16, &Vec<T::AccountId>, &Option<Timepoint<T::BlockNumber>>, &Box<<T as Trait>::Call>)| {
				args.3.get_dispatch_info().class
			},
			Pays::Yes,
		)]
		fn as_multi(origin,
			threshold: u16,
			other_signatories: Vec<T::AccountId>,
			maybe_timepoint: Option<Timepoint<T::BlockNumber>>,
			call: Box<<T as Trait>::Call>,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			ensure!(threshold >= 1, Error::<T>::ZeroThreshold);
			let max_sigs = T::MaxSignatories::get() as usize;
			ensure!(!other_signatories.is_empty(), Error::<T>::TooFewSignatories);
			let other_signatories_len = other_signatories.len();
			ensure!(other_signatories_len < max_sigs, Error::<T>::TooManySignatories);
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
						Self::deposit_event(RawEvent::MultisigApproval(who, timepoint, id, call_hash));
						// Call is not made, so the actual weight does not include call
						return Ok(Some(weight_of::as_multi::<T>(other_signatories_len, 0)).into())
					}
				} else {
					if (m.approvals.len() as u16) < threshold {
						Err(Error::<T>::AlreadyApproved)?
					}
				}

				let result = call.dispatch(frame_system::RawOrigin::Signed(id.clone()).into());
				let _ = T::Currency::unreserve(&m.depositor, m.deposit);
				<Multisigs<T>>::remove(&id, call_hash);
				Self::deposit_event(RawEvent::MultisigExecuted(
					who, timepoint, id, call_hash, result.map(|_| ()).map_err(|e| e.error)
				));
				return Ok(None.into())
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
					Self::deposit_event(RawEvent::NewMultisig(who, id, call_hash));
					// Call is not made, so we can return that weight
					return Ok(Some(weight_of::as_multi::<T>(other_signatories_len, 0)).into())
				} else {
					let result = call.dispatch(frame_system::RawOrigin::Signed(id).into());
					match result {
						Ok(post_dispatch_info) => {
							match post_dispatch_info.actual_weight {
								Some(actual_weight) => return Ok(Some(weight_of::as_multi::<T>(other_signatories_len, actual_weight)).into()),
								None => return Ok(None.into()),
							}
						},
						Err(err) => {
							match err.post_info.actual_weight {
								Some(actual_weight) => {
									let weight_used = weight_of::as_multi::<T>(other_signatories_len, actual_weight);
									return Err(DispatchErrorWithPostInfo { post_info: Some(weight_used).into(), error: err.error.into() })
								},
								None => {
									return Err(err)
								}
							}
						}
					}
				}
			}
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
		/// ----------------------------------
		/// - Base Weight:
		///     - Create: 44.71 + 0.088 * S
		///     - Approve: 31.48 + 0.116 * S
		/// - DB Weight:
		///     - Read: Multisig Storage, [Caller Account]
		///     - Write: Multisig Storage, [Caller Account]
		/// # </weight>
		#[weight = FunctionOf(
			|args: (&u16, &Vec<T::AccountId>, &Option<Timepoint<T::BlockNumber>>, &[u8; 32])| {
				T::DbWeight::get().reads_writes(1, 1)
					.saturating_add(45_000_000)
					.saturating_add((args.1.len() as Weight).saturating_mul(120_000))
			},
			DispatchClass::Normal,
			Pays::Yes,
		)]
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
					Self::deposit_event(RawEvent::MultisigApproval(who, timepoint, id, call_hash));
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
					Self::deposit_event(RawEvent::NewMultisig(who, id, call_hash));
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
		/// ----------------------------------
		/// - Base Weight: 37.6 + 0.084 * S
		/// - DB Weight:
		///     - Read: Multisig Storage, [Caller Account]
		///     - Write: Multisig Storage, [Caller Account]
		/// # </weight>
		#[weight = FunctionOf(
			|args: (&u16, &Vec<T::AccountId>, &Timepoint<T::BlockNumber>, &[u8; 32])| {
				T::DbWeight::get().reads_writes(1, 1)
					.saturating_add(40_000_000)
					.saturating_add((args.1.len() as Weight).saturating_mul(100_000))
			},
			DispatchClass::Normal,
			Pays::Yes,
		)]
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

			Self::deposit_event(RawEvent::MultisigCancelled(who, timepoint, id, call_hash));
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
