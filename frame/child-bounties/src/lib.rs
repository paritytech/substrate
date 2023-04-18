// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! # Child Bounties Pallet ( `pallet-child-bounties` )
//!
//! ## Child Bounty
//!
//! > NOTE: This pallet is tightly coupled with `pallet-treasury` and `pallet-bounties`.
//!
//! With child bounties, a large bounty proposal can be divided into smaller chunks,
//! for parallel execution, and for efficient governance and tracking of spent funds.
//! A child bounty is a smaller piece of work, extracted from a parent bounty.
//! A curator is assigned after the child bounty is created by the parent bounty curator,
//! to be delegated with the responsibility of assigning a payout address once the specified
//! set of tasks is completed.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! Child Bounty protocol:
//! - `add_child_bounty` - Add a child bounty for a parent bounty to for dividing the work in
//!   smaller tasks.
//! - `propose_curator` - Assign an account to a child bounty as candidate curator.
//! - `accept_curator` - Accept a child bounty assignment from the parent bounty curator, setting a
//!   curator deposit.
//! - `award_child_bounty` - Close and pay out the specified amount for the completed work.
//! - `claim_child_bounty` - Claim a specific child bounty amount from the payout address.
//! - `unassign_curator` - Unassign an accepted curator from a specific child bounty.
//! - `close_child_bounty` - Cancel the child bounty for a specific treasury amount and close the
//!   bounty.

// Most of the business logic in this pallet has been
// originally contributed by "https://github.com/shamb0",
// as part of the PR - https://github.com/paritytech/substrate/pull/7965.
// The code has been moved here and then refactored in order to
// extract child bounties as a separate pallet.

#![cfg_attr(not(feature = "std"), no_std)]

mod benchmarking;
mod tests;
pub mod weights;

use sp_std::prelude::*;

use frame_support::traits::{
	Currency,
	ExistenceRequirement::{AllowDeath, KeepAlive},
	Get, OnUnbalanced, ReservableCurrency, WithdrawReasons,
};

use sp_runtime::{
	traits::{AccountIdConversion, BadOrigin, CheckedSub, Saturating, StaticLookup, Zero},
	DispatchResult, RuntimeDebug,
};

use frame_support::pallet_prelude::*;
use frame_system::pallet_prelude::*;
use pallet_bounties::BountyStatus;
use scale_info::TypeInfo;
pub use weights::WeightInfo;

pub use pallet::*;

type BalanceOf<T> = pallet_treasury::BalanceOf<T>;
type BountiesError<T> = pallet_bounties::Error<T>;
type BountyIndex = pallet_bounties::BountyIndex;
type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;

/// A child bounty proposal.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub struct ChildBounty<AccountId, Balance, BlockNumber> {
	/// The parent of this child-bounty.
	parent_bounty: BountyIndex,
	/// The (total) amount that should be paid if this child-bounty is rewarded.
	value: Balance,
	/// The child bounty curator fee.
	fee: Balance,
	/// The deposit of child-bounty curator.
	curator_deposit: Balance,
	/// The status of this child-bounty.
	status: ChildBountyStatus<AccountId, BlockNumber>,
}

/// The status of a child-bounty.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub enum ChildBountyStatus<AccountId, BlockNumber> {
	/// The child-bounty is added and waiting for curator assignment.
	Added,
	/// A curator has been proposed by the parent bounty curator. Waiting for
	/// acceptance from the child-bounty curator.
	CuratorProposed {
		/// The assigned child-bounty curator of this bounty.
		curator: AccountId,
	},
	/// The child-bounty is active and waiting to be awarded.
	Active {
		/// The curator of this child-bounty.
		curator: AccountId,
	},
	/// The child-bounty is awarded and waiting to released after a delay.
	PendingPayout {
		/// The curator of this child-bounty.
		curator: AccountId,
		/// The beneficiary of the child-bounty.
		beneficiary: AccountId,
		/// When the child-bounty can be claimed.
		unlock_at: BlockNumber,
	},
}

#[frame_support::pallet]
pub mod pallet {

	use super::*;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config:
		frame_system::Config + pallet_treasury::Config + pallet_bounties::Config
	{
		/// Maximum number of child bounties that can be added to a parent bounty.
		#[pallet::constant]
		type MaxActiveChildBountyCount: Get<u32>;

		/// Minimum value for a child-bounty.
		#[pallet::constant]
		type ChildBountyValueMinimum: Get<BalanceOf<Self>>;

		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::error]
	pub enum Error<T> {
		/// The parent bounty is not in active state.
		ParentBountyNotActive,
		/// The bounty balance is not enough to add new child-bounty.
		InsufficientBountyBalance,
		/// Number of child bounties exceeds limit `MaxActiveChildBountyCount`.
		TooManyChildBounties,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A child-bounty is added.
		Added { index: BountyIndex, child_index: BountyIndex },
		/// A child-bounty is awarded to a beneficiary.
		Awarded { index: BountyIndex, child_index: BountyIndex, beneficiary: T::AccountId },
		/// A child-bounty is claimed by beneficiary.
		Claimed {
			index: BountyIndex,
			child_index: BountyIndex,
			payout: BalanceOf<T>,
			beneficiary: T::AccountId,
		},
		/// A child-bounty is cancelled.
		Canceled { index: BountyIndex, child_index: BountyIndex },
	}

	/// Number of total child bounties.
	#[pallet::storage]
	#[pallet::getter(fn child_bounty_count)]
	pub type ChildBountyCount<T: Config> = StorageValue<_, BountyIndex, ValueQuery>;

	/// Number of child bounties per parent bounty.
	/// Map of parent bounty index to number of child bounties.
	#[pallet::storage]
	#[pallet::getter(fn parent_child_bounties)]
	pub type ParentChildBounties<T: Config> =
		StorageMap<_, Twox64Concat, BountyIndex, u32, ValueQuery>;

	/// Child bounties that have been added.
	#[pallet::storage]
	#[pallet::getter(fn child_bounties)]
	pub type ChildBounties<T: Config> = StorageDoubleMap<
		_,
		Twox64Concat,
		BountyIndex,
		Twox64Concat,
		BountyIndex,
		ChildBounty<T::AccountId, BalanceOf<T>, T::BlockNumber>,
	>;

	/// The description of each child-bounty.
	#[pallet::storage]
	#[pallet::getter(fn child_bounty_descriptions)]
	pub type ChildBountyDescriptions<T: Config> =
		StorageMap<_, Twox64Concat, BountyIndex, BoundedVec<u8, T::MaximumReasonLength>>;

	/// The cumulative child-bounty curator fee for each parent bounty.
	#[pallet::storage]
	#[pallet::getter(fn children_curator_fees)]
	pub type ChildrenCuratorFees<T: Config> =
		StorageMap<_, Twox64Concat, BountyIndex, BalanceOf<T>, ValueQuery>;

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Add a new child-bounty.
		///
		/// The dispatch origin for this call must be the curator of parent
		/// bounty and the parent bounty must be in "active" state.
		///
		/// Child-bounty gets added successfully & fund gets transferred from
		/// parent bounty to child-bounty account, if parent bounty has enough
		/// funds, else the call fails.
		///
		/// Upper bound to maximum number of active  child bounties that can be
		/// added are managed via runtime trait config
		/// [`Config::MaxActiveChildBountyCount`].
		///
		/// If the call is success, the status of child-bounty is updated to
		/// "Added".
		///
		/// - `parent_bounty_id`: Index of parent bounty for which child-bounty is being added.
		/// - `value`: Value for executing the proposal.
		/// - `description`: Text description for the child-bounty.
		#[pallet::call_index(0)]
		#[pallet::weight(<T as Config>::WeightInfo::add_child_bounty(description.len() as u32))]
		pub fn add_child_bounty(
			origin: OriginFor<T>,
			#[pallet::compact] parent_bounty_id: BountyIndex,
			#[pallet::compact] value: BalanceOf<T>,
			description: Vec<u8>,
		) -> DispatchResult {
			let signer = ensure_signed(origin)?;

			// Verify the arguments.
			let bounded_description =
				description.try_into().map_err(|_| BountiesError::<T>::ReasonTooBig)?;
			ensure!(value >= T::ChildBountyValueMinimum::get(), BountiesError::<T>::InvalidValue);
			ensure!(
				Self::parent_child_bounties(parent_bounty_id) <=
					T::MaxActiveChildBountyCount::get() as u32,
				Error::<T>::TooManyChildBounties,
			);

			let (curator, _) = Self::ensure_bounty_active(parent_bounty_id)?;
			ensure!(signer == curator, BountiesError::<T>::RequireCurator);

			// Read parent bounty account info.
			let parent_bounty_account =
				pallet_bounties::Pallet::<T>::bounty_account_id(parent_bounty_id);

			// Ensure parent bounty has enough balance after adding child-bounty.
			let bounty_balance = T::Currency::free_balance(&parent_bounty_account);
			let new_bounty_balance = bounty_balance
				.checked_sub(&value)
				.ok_or(Error::<T>::InsufficientBountyBalance)?;
			T::Currency::ensure_can_withdraw(
				&parent_bounty_account,
				value,
				WithdrawReasons::TRANSFER,
				new_bounty_balance,
			)?;

			// Get child-bounty ID.
			let child_bounty_id = Self::child_bounty_count();
			let child_bounty_account = Self::child_bounty_account_id(child_bounty_id);

			// Transfer funds from parent bounty to child-bounty.
			T::Currency::transfer(&parent_bounty_account, &child_bounty_account, value, KeepAlive)?;

			// Increment the active child-bounty count.
			<ParentChildBounties<T>>::mutate(parent_bounty_id, |count| count.saturating_inc());
			<ChildBountyCount<T>>::put(child_bounty_id.saturating_add(1));

			// Create child-bounty instance.
			Self::create_child_bounty(
				parent_bounty_id,
				child_bounty_id,
				value,
				bounded_description,
			);
			Ok(())
		}

		/// Propose curator for funded child-bounty.
		///
		/// The dispatch origin for this call must be curator of parent bounty.
		///
		/// Parent bounty must be in active state, for this child-bounty call to
		/// work.
		///
		/// Child-bounty must be in "Added" state, for processing the call. And
		/// state of child-bounty is moved to "CuratorProposed" on successful
		/// call completion.
		///
		/// - `parent_bounty_id`: Index of parent bounty.
		/// - `child_bounty_id`: Index of child bounty.
		/// - `curator`: Address of child-bounty curator.
		/// - `fee`: payment fee to child-bounty curator for execution.
		#[pallet::call_index(1)]
		#[pallet::weight(<T as Config>::WeightInfo::propose_curator())]
		pub fn propose_curator(
			origin: OriginFor<T>,
			#[pallet::compact] parent_bounty_id: BountyIndex,
			#[pallet::compact] child_bounty_id: BountyIndex,
			curator: AccountIdLookupOf<T>,
			#[pallet::compact] fee: BalanceOf<T>,
		) -> DispatchResult {
			let signer = ensure_signed(origin)?;
			let child_bounty_curator = T::Lookup::lookup(curator)?;

			let (curator, _) = Self::ensure_bounty_active(parent_bounty_id)?;
			ensure!(signer == curator, BountiesError::<T>::RequireCurator);

			// Mutate the child-bounty instance.
			ChildBounties::<T>::try_mutate_exists(
				parent_bounty_id,
				child_bounty_id,
				|maybe_child_bounty| -> DispatchResult {
					let mut child_bounty =
						maybe_child_bounty.as_mut().ok_or(BountiesError::<T>::InvalidIndex)?;

					// Ensure child-bounty is in expected state.
					ensure!(
						child_bounty.status == ChildBountyStatus::Added,
						BountiesError::<T>::UnexpectedStatus,
					);

					// Ensure child-bounty curator fee is less than child-bounty value.
					ensure!(fee < child_bounty.value, BountiesError::<T>::InvalidFee);

					// Add child-bounty curator fee to the cumulative sum. To be
					// subtracted from the parent bounty curator when claiming
					// bounty.
					ChildrenCuratorFees::<T>::mutate(parent_bounty_id, |value| {
						*value = value.saturating_add(fee)
					});

					// Update the child-bounty curator fee.
					child_bounty.fee = fee;

					// Update the child-bounty state.
					child_bounty.status =
						ChildBountyStatus::CuratorProposed { curator: child_bounty_curator };

					Ok(())
				},
			)
		}

		/// Accept the curator role for the child-bounty.
		///
		/// The dispatch origin for this call must be the curator of this
		/// child-bounty.
		///
		/// A deposit will be reserved from the curator and refund upon
		/// successful payout or cancellation.
		///
		/// Fee for curator is deducted from curator fee of parent bounty.
		///
		/// Parent bounty must be in active state, for this child-bounty call to
		/// work.
		///
		/// Child-bounty must be in "CuratorProposed" state, for processing the
		/// call. And state of child-bounty is moved to "Active" on successful
		/// call completion.
		///
		/// - `parent_bounty_id`: Index of parent bounty.
		/// - `child_bounty_id`: Index of child bounty.
		#[pallet::call_index(2)]
		#[pallet::weight(<T as Config>::WeightInfo::accept_curator())]
		pub fn accept_curator(
			origin: OriginFor<T>,
			#[pallet::compact] parent_bounty_id: BountyIndex,
			#[pallet::compact] child_bounty_id: BountyIndex,
		) -> DispatchResult {
			let signer = ensure_signed(origin)?;

			let (parent_curator, _) = Self::ensure_bounty_active(parent_bounty_id)?;
			// Mutate child-bounty.
			ChildBounties::<T>::try_mutate_exists(
				parent_bounty_id,
				child_bounty_id,
				|maybe_child_bounty| -> DispatchResult {
					let mut child_bounty =
						maybe_child_bounty.as_mut().ok_or(BountiesError::<T>::InvalidIndex)?;

					// Ensure child-bounty is in expected state.
					if let ChildBountyStatus::CuratorProposed { ref curator } = child_bounty.status
					{
						ensure!(signer == *curator, BountiesError::<T>::RequireCurator);

						// Reserve child-bounty curator deposit.
						let deposit = Self::calculate_curator_deposit(
							&parent_curator,
							curator,
							&child_bounty.fee,
						);

						T::Currency::reserve(curator, deposit)?;
						child_bounty.curator_deposit = deposit;

						child_bounty.status =
							ChildBountyStatus::Active { curator: curator.clone() };
						Ok(())
					} else {
						Err(BountiesError::<T>::UnexpectedStatus.into())
					}
				},
			)
		}

		/// Unassign curator from a child-bounty.
		///
		/// The dispatch origin for this call can be either `RejectOrigin`, or
		/// the curator of the parent bounty, or any signed origin.
		///
		/// For the origin other than T::RejectOrigin and the child-bounty
		/// curator, parent bounty must be in active state, for this call to
		/// work. We allow child-bounty curator and T::RejectOrigin to execute
		/// this call irrespective of the parent bounty state.
		///
		/// If this function is called by the `RejectOrigin` or the
		/// parent bounty curator, we assume that the child-bounty curator is
		/// malicious or inactive. As a result, child-bounty curator deposit is
		/// slashed.
		///
		/// If the origin is the child-bounty curator, we take this as a sign
		/// that they are unable to do their job, and are willingly giving up.
		/// We could slash the deposit, but for now we allow them to unreserve
		/// their deposit and exit without issue. (We may want to change this if
		/// it is abused.)
		///
		/// Finally, the origin can be anyone iff the child-bounty curator is
		/// "inactive". Expiry update due of parent bounty is used to estimate
		/// inactive state of child-bounty curator.
		///
		/// This allows anyone in the community to call out that a child-bounty
		/// curator is not doing their due diligence, and we should pick a new
		/// one. In this case the child-bounty curator deposit is slashed.
		///
		/// State of child-bounty is moved to Added state on successful call
		/// completion.
		///
		/// - `parent_bounty_id`: Index of parent bounty.
		/// - `child_bounty_id`: Index of child bounty.
		#[pallet::call_index(3)]
		#[pallet::weight(<T as Config>::WeightInfo::unassign_curator())]
		pub fn unassign_curator(
			origin: OriginFor<T>,
			#[pallet::compact] parent_bounty_id: BountyIndex,
			#[pallet::compact] child_bounty_id: BountyIndex,
		) -> DispatchResult {
			let maybe_sender = ensure_signed(origin.clone())
				.map(Some)
				.or_else(|_| T::RejectOrigin::ensure_origin(origin).map(|_| None))?;

			ChildBounties::<T>::try_mutate_exists(
				parent_bounty_id,
				child_bounty_id,
				|maybe_child_bounty| -> DispatchResult {
					let mut child_bounty =
						maybe_child_bounty.as_mut().ok_or(BountiesError::<T>::InvalidIndex)?;

					let slash_curator = |curator: &T::AccountId,
					                     curator_deposit: &mut BalanceOf<T>| {
						let imbalance = T::Currency::slash_reserved(curator, *curator_deposit).0;
						T::OnSlash::on_unbalanced(imbalance);
						*curator_deposit = Zero::zero();
					};

					match child_bounty.status {
						ChildBountyStatus::Added => {
							// No curator to unassign at this point.
							return Err(BountiesError::<T>::UnexpectedStatus.into())
						},
						ChildBountyStatus::CuratorProposed { ref curator } => {
							// A child-bounty curator has been proposed, but not accepted yet.
							// Either `RejectOrigin`, parent bounty curator or the proposed
							// child-bounty curator can unassign the child-bounty curator.
							ensure!(
								maybe_sender.map_or(true, |sender| {
									sender == *curator ||
										Self::ensure_bounty_active(parent_bounty_id)
											.map_or(false, |(parent_curator, _)| {
												sender == parent_curator
											})
								}),
								BadOrigin
							);
							// Continue to change bounty status below.
						},
						ChildBountyStatus::Active { ref curator } => {
							// The child-bounty is active.
							match maybe_sender {
								// If the `RejectOrigin` is calling this function, slash the curator
								// deposit.
								None => {
									slash_curator(curator, &mut child_bounty.curator_deposit);
									// Continue to change child-bounty status below.
								},
								Some(sender) if sender == *curator => {
									// This is the child-bounty curator, willingly giving up their
									// role. Give back their deposit.
									T::Currency::unreserve(curator, child_bounty.curator_deposit);
									// Reset curator deposit.
									child_bounty.curator_deposit = Zero::zero();
									// Continue to change bounty status below.
								},
								Some(sender) => {
									let (parent_curator, update_due) =
										Self::ensure_bounty_active(parent_bounty_id)?;
									if sender == parent_curator ||
										update_due < frame_system::Pallet::<T>::block_number()
									{
										// Slash the child-bounty curator if
										// + the call is made by the parent bounty curator.
										// + or the curator is inactive.
										slash_curator(curator, &mut child_bounty.curator_deposit);
									// Continue to change bounty status below.
									} else {
										// Curator has more time to give an update.
										return Err(BountiesError::<T>::Premature.into())
									}
								},
							}
						},
						ChildBountyStatus::PendingPayout { ref curator, .. } => {
							let (parent_curator, _) = Self::ensure_bounty_active(parent_bounty_id)?;
							ensure!(
								maybe_sender.map_or(true, |sender| parent_curator == sender),
								BadOrigin,
							);
							slash_curator(curator, &mut child_bounty.curator_deposit);
							// Continue to change child-bounty status below.
						},
					};
					// Move the child-bounty state to Added.
					child_bounty.status = ChildBountyStatus::Added;
					Ok(())
				},
			)
		}

		/// Award child-bounty to a beneficiary.
		///
		/// The beneficiary will be able to claim the funds after a delay.
		///
		/// The dispatch origin for this call must be the parent curator or
		/// curator of this child-bounty.
		///
		/// Parent bounty must be in active state, for this child-bounty call to
		/// work.
		///
		/// Child-bounty must be in active state, for processing the call. And
		/// state of child-bounty is moved to "PendingPayout" on successful call
		/// completion.
		///
		/// - `parent_bounty_id`: Index of parent bounty.
		/// - `child_bounty_id`: Index of child bounty.
		/// - `beneficiary`: Beneficiary account.
		#[pallet::call_index(4)]
		#[pallet::weight(<T as Config>::WeightInfo::award_child_bounty())]
		pub fn award_child_bounty(
			origin: OriginFor<T>,
			#[pallet::compact] parent_bounty_id: BountyIndex,
			#[pallet::compact] child_bounty_id: BountyIndex,
			beneficiary: AccountIdLookupOf<T>,
		) -> DispatchResult {
			let signer = ensure_signed(origin)?;
			let beneficiary = T::Lookup::lookup(beneficiary)?;

			// Ensure parent bounty exists, and is active.
			let (parent_curator, _) = Self::ensure_bounty_active(parent_bounty_id)?;

			ChildBounties::<T>::try_mutate_exists(
				parent_bounty_id,
				child_bounty_id,
				|maybe_child_bounty| -> DispatchResult {
					let mut child_bounty =
						maybe_child_bounty.as_mut().ok_or(BountiesError::<T>::InvalidIndex)?;

					// Ensure child-bounty is in active state.
					if let ChildBountyStatus::Active { ref curator } = child_bounty.status {
						ensure!(
							signer == *curator || signer == parent_curator,
							BountiesError::<T>::RequireCurator,
						);
						// Move the child-bounty state to pending payout.
						child_bounty.status = ChildBountyStatus::PendingPayout {
							curator: signer,
							beneficiary: beneficiary.clone(),
							unlock_at: frame_system::Pallet::<T>::block_number() +
								T::BountyDepositPayoutDelay::get(),
						};
						Ok(())
					} else {
						Err(BountiesError::<T>::UnexpectedStatus.into())
					}
				},
			)?;

			// Trigger the event Awarded.
			Self::deposit_event(Event::<T>::Awarded {
				index: parent_bounty_id,
				child_index: child_bounty_id,
				beneficiary,
			});

			Ok(())
		}

		/// Claim the payout from an awarded child-bounty after payout delay.
		///
		/// The dispatch origin for this call may be any signed origin.
		///
		/// Call works independent of parent bounty state, No need for parent
		/// bounty to be in active state.
		///
		/// The Beneficiary is paid out with agreed bounty value. Curator fee is
		/// paid & curator deposit is unreserved.
		///
		/// Child-bounty must be in "PendingPayout" state, for processing the
		/// call. And instance of child-bounty is removed from the state on
		/// successful call completion.
		///
		/// - `parent_bounty_id`: Index of parent bounty.
		/// - `child_bounty_id`: Index of child bounty.
		#[pallet::call_index(5)]
		#[pallet::weight(<T as Config>::WeightInfo::claim_child_bounty())]
		pub fn claim_child_bounty(
			origin: OriginFor<T>,
			#[pallet::compact] parent_bounty_id: BountyIndex,
			#[pallet::compact] child_bounty_id: BountyIndex,
		) -> DispatchResult {
			let _ = ensure_signed(origin)?;

			// Ensure child-bounty is in expected state.
			ChildBounties::<T>::try_mutate_exists(
				parent_bounty_id,
				child_bounty_id,
				|maybe_child_bounty| -> DispatchResult {
					let child_bounty =
						maybe_child_bounty.as_mut().ok_or(BountiesError::<T>::InvalidIndex)?;

					if let ChildBountyStatus::PendingPayout {
						ref curator,
						ref beneficiary,
						ref unlock_at,
					} = child_bounty.status
					{
						// Ensure block number is elapsed for processing the
						// claim.
						ensure!(
							frame_system::Pallet::<T>::block_number() >= *unlock_at,
							BountiesError::<T>::Premature,
						);

						// Make curator fee payment.
						let child_bounty_account = Self::child_bounty_account_id(child_bounty_id);
						let balance = T::Currency::free_balance(&child_bounty_account);
						let curator_fee = child_bounty.fee.min(balance);
						let payout = balance.saturating_sub(curator_fee);

						// Unreserve the curator deposit. Should not fail
						// because the deposit is always reserved when curator is
						// assigned.
						let _ = T::Currency::unreserve(curator, child_bounty.curator_deposit);

						// Make payout to child-bounty curator.
						// Should not fail because curator fee is always less than bounty value.
						let fee_transfer_result = T::Currency::transfer(
							&child_bounty_account,
							curator,
							curator_fee,
							AllowDeath,
						);
						debug_assert!(fee_transfer_result.is_ok());

						// Make payout to beneficiary.
						// Should not fail.
						let payout_transfer_result = T::Currency::transfer(
							&child_bounty_account,
							beneficiary,
							payout,
							AllowDeath,
						);
						debug_assert!(payout_transfer_result.is_ok());

						// Trigger the Claimed event.
						Self::deposit_event(Event::<T>::Claimed {
							index: parent_bounty_id,
							child_index: child_bounty_id,
							payout,
							beneficiary: beneficiary.clone(),
						});

						// Update the active child-bounty tracking count.
						<ParentChildBounties<T>>::mutate(parent_bounty_id, |count| {
							count.saturating_dec()
						});

						// Remove the child-bounty description.
						<ChildBountyDescriptions<T>>::remove(child_bounty_id);

						// Remove the child-bounty instance from the state.
						*maybe_child_bounty = None;

						Ok(())
					} else {
						Err(BountiesError::<T>::UnexpectedStatus.into())
					}
				},
			)
		}

		/// Cancel a proposed or active child-bounty. Child-bounty account funds
		/// are transferred to parent bounty account. The child-bounty curator
		/// deposit may be unreserved if possible.
		///
		/// The dispatch origin for this call must be either parent curator or
		/// `T::RejectOrigin`.
		///
		/// If the state of child-bounty is `Active`, curator deposit is
		/// unreserved.
		///
		/// If the state of child-bounty is `PendingPayout`, call fails &
		/// returns `PendingPayout` error.
		///
		/// For the origin other than T::RejectOrigin, parent bounty must be in
		/// active state, for this child-bounty call to work. For origin
		/// T::RejectOrigin execution is forced.
		///
		/// Instance of child-bounty is removed from the state on successful
		/// call completion.
		///
		/// - `parent_bounty_id`: Index of parent bounty.
		/// - `child_bounty_id`: Index of child bounty.
		#[pallet::call_index(6)]
		#[pallet::weight(<T as Config>::WeightInfo::close_child_bounty_added()
			.max(<T as Config>::WeightInfo::close_child_bounty_active()))]
		pub fn close_child_bounty(
			origin: OriginFor<T>,
			#[pallet::compact] parent_bounty_id: BountyIndex,
			#[pallet::compact] child_bounty_id: BountyIndex,
		) -> DispatchResult {
			let maybe_sender = ensure_signed(origin.clone())
				.map(Some)
				.or_else(|_| T::RejectOrigin::ensure_origin(origin).map(|_| None))?;

			// Ensure parent bounty exist, get parent curator.
			let (parent_curator, _) = Self::ensure_bounty_active(parent_bounty_id)?;

			ensure!(maybe_sender.map_or(true, |sender| parent_curator == sender), BadOrigin);

			Self::impl_close_child_bounty(parent_bounty_id, child_bounty_id)?;
			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	// This function will calculate the deposit of a curator.
	fn calculate_curator_deposit(
		parent_curator: &T::AccountId,
		child_curator: &T::AccountId,
		bounty_fee: &BalanceOf<T>,
	) -> BalanceOf<T> {
		if parent_curator == child_curator {
			return Zero::zero()
		}

		// We just use the same logic from the parent bounties pallet.
		pallet_bounties::Pallet::<T>::calculate_curator_deposit(bounty_fee)
	}

	/// The account ID of a child-bounty account.
	pub fn child_bounty_account_id(id: BountyIndex) -> T::AccountId {
		// This function is taken from the parent (bounties) pallet, but the
		// prefix is changed to have different AccountId when the index of
		// parent and child is same.
		T::PalletId::get().into_sub_account_truncating(("cb", id))
	}

	fn create_child_bounty(
		parent_bounty_id: BountyIndex,
		child_bounty_id: BountyIndex,
		child_bounty_value: BalanceOf<T>,
		description: BoundedVec<u8, T::MaximumReasonLength>,
	) {
		let child_bounty = ChildBounty {
			parent_bounty: parent_bounty_id,
			value: child_bounty_value,
			fee: 0u32.into(),
			curator_deposit: 0u32.into(),
			status: ChildBountyStatus::Added,
		};
		ChildBounties::<T>::insert(parent_bounty_id, child_bounty_id, &child_bounty);
		ChildBountyDescriptions::<T>::insert(child_bounty_id, description);
		Self::deposit_event(Event::Added { index: parent_bounty_id, child_index: child_bounty_id });
	}

	fn ensure_bounty_active(
		bounty_id: BountyIndex,
	) -> Result<(T::AccountId, T::BlockNumber), DispatchError> {
		let parent_bounty = pallet_bounties::Pallet::<T>::bounties(bounty_id)
			.ok_or(BountiesError::<T>::InvalidIndex)?;
		if let BountyStatus::Active { curator, update_due } = parent_bounty.get_status() {
			Ok((curator, update_due))
		} else {
			Err(Error::<T>::ParentBountyNotActive.into())
		}
	}

	fn impl_close_child_bounty(
		parent_bounty_id: BountyIndex,
		child_bounty_id: BountyIndex,
	) -> DispatchResult {
		ChildBounties::<T>::try_mutate_exists(
			parent_bounty_id,
			child_bounty_id,
			|maybe_child_bounty| -> DispatchResult {
				let child_bounty =
					maybe_child_bounty.as_mut().ok_or(BountiesError::<T>::InvalidIndex)?;

				match &child_bounty.status {
					ChildBountyStatus::Added | ChildBountyStatus::CuratorProposed { .. } => {
						// Nothing extra to do besides the removal of the child-bounty below.
					},
					ChildBountyStatus::Active { curator } => {
						// Cancelled by parent curator or RejectOrigin,
						// refund deposit of the working child-bounty curator.
						let _ = T::Currency::unreserve(curator, child_bounty.curator_deposit);
						// Then execute removal of the child-bounty below.
					},
					ChildBountyStatus::PendingPayout { .. } => {
						// Child-bounty is already in pending payout. If parent
						// curator or RejectOrigin wants to close this
						// child-bounty, it should mean the child-bounty curator
						// was acting maliciously. So first unassign the
						// child-bounty curator, slashing their deposit.
						return Err(BountiesError::<T>::PendingPayout.into())
					},
				}

				// Revert the curator fee back to parent bounty curator &
				// reduce the active child-bounty count.
				ChildrenCuratorFees::<T>::mutate(parent_bounty_id, |value| {
					*value = value.saturating_sub(child_bounty.fee)
				});
				<ParentChildBounties<T>>::mutate(parent_bounty_id, |count| {
					*count = count.saturating_sub(1)
				});

				// Transfer fund from child-bounty to parent bounty.
				let parent_bounty_account =
					pallet_bounties::Pallet::<T>::bounty_account_id(parent_bounty_id);
				let child_bounty_account = Self::child_bounty_account_id(child_bounty_id);
				let balance = T::Currency::free_balance(&child_bounty_account);
				let transfer_result = T::Currency::transfer(
					&child_bounty_account,
					&parent_bounty_account,
					balance,
					AllowDeath,
				); // Should not fail; child bounty account gets this balance during creation.
				debug_assert!(transfer_result.is_ok());

				// Remove the child-bounty description.
				<ChildBountyDescriptions<T>>::remove(child_bounty_id);

				*maybe_child_bounty = None;

				Self::deposit_event(Event::<T>::Canceled {
					index: parent_bounty_id,
					child_index: child_bounty_id,
				});
				Ok(())
			},
		)
	}
}

// Implement ChildBountyManager to connect with the bounties pallet. This is
// where we pass the active child bounties and child curator fees to the parent
// bounty.
impl<T: Config> pallet_bounties::ChildBountyManager<BalanceOf<T>> for Pallet<T> {
	fn child_bounties_count(
		bounty_id: pallet_bounties::BountyIndex,
	) -> pallet_bounties::BountyIndex {
		Self::parent_child_bounties(bounty_id)
	}

	fn children_curator_fees(bounty_id: pallet_bounties::BountyIndex) -> BalanceOf<T> {
		// This is asked for when the parent bounty is being claimed. No use of
		// keeping it in state after that. Hence removing.
		let children_fee_total = Self::children_curator_fees(bounty_id);
		<ChildrenCuratorFees<T>>::remove(bounty_id);
		children_fee_total
	}
}
