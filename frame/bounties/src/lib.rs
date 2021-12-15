// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! # Bounties Module ( pallet-bounties )
//!
//! ## Bounty
//!
//! > NOTE: This pallet is tightly coupled with pallet-treasury.
//!
//! A Bounty Spending is a reward for a specified body of work - or specified set of objectives -
//! that needs to be executed for a predefined Treasury amount to be paid out. A curator is assigned
//! after the bounty is approved and funded by Council, to be delegated with the responsibility of
//! assigning a payout address once the specified set of objectives is completed.
//!
//! After the Council has activated a bounty, it delegates the work that requires expertise to a
//! curator in exchange of a deposit. Once the curator accepts the bounty, they get to close the
//! active bounty. Closing the active bounty enacts a delayed payout to the payout address, the
//! curator fee and the return of the curator deposit. The delay allows for intervention through
//! regular democracy. The Council gets to unassign the curator, resulting in a new curator
//! election. The Council also gets to cancel the bounty if deemed necessary before assigning a
//! curator or once the bounty is active or payout is pending, resulting in the slash of the
//! curator's deposit.
//!
//!
//! ### Terminology
//!
//! Bounty:
//! - **Bounty spending proposal:** A proposal to reward a predefined body of work upon completion
//!   by the Treasury.
//! - **Proposer:** An account proposing a bounty spending.
//! - **Curator:** An account managing the bounty and assigning a payout address receiving the
//!   reward for the completion of work.
//! - **Deposit:** The amount held on deposit for placing a bounty proposal plus the amount held on
//!   deposit per byte within the bounty description.
//! - **Curator deposit:** The payment from a candidate willing to curate an approved bounty. The
//!   deposit is returned when/if the bounty is completed.
//! - **Bounty value:** The total amount that should be paid to the Payout Address if the bounty is
//!   rewarded.
//! - **Payout address:** The account to which the total or part of the bounty is assigned to.
//! - **Payout Delay:** The delay period for which a bounty beneficiary needs to wait before
//!   claiming.
//! - **Curator fee:** The reserved upfront payment for a curator for work related to the bounty.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! Bounty protocol:
//! - `propose_bounty` - Propose a specific treasury amount to be earmarked for a predefined set of
//!   tasks and stake the required deposit.
//! - `approve_bounty` - Accept a specific treasury amount to be earmarked for a predefined body of
//!   work.
//! - `propose_curator` - Assign an account to a bounty as candidate curator.
//! - `accept_curator` - Accept a bounty assignment from the Council, setting a curator deposit.
//! - `extend_bounty_expiry` - Extend the expiry block number of the bounty and stay active.
//! - `award_bounty` - Close and pay out the specified amount for the completed work.
//! - `claim_bounty` - Claim a specific bounty amount from the Payout Address.
//! - `unassign_curator` - Unassign an accepted curator from a specific earmark.
//! - `close_bounty` - Cancel the earmark for a specific treasury amount and close the bounty.

#![cfg_attr(not(feature = "std"), no_std)]

mod benchmarking;
pub mod migrations;
mod tests;
pub mod weights;

use sp_std::prelude::*;

use frame_support::traits::{
	Currency, ExistenceRequirement::AllowDeath, Get, Imbalance, OnUnbalanced, ReservableCurrency,
};

use sp_runtime::{
	traits::{AccountIdConversion, BadOrigin, Saturating, StaticLookup, Zero},
	DispatchResult, Permill, RuntimeDebug,
};

use frame_support::{dispatch::DispatchResultWithPostInfo, traits::EnsureOrigin};

use frame_support::pallet_prelude::*;
use frame_system::pallet_prelude::*;
use scale_info::TypeInfo;
pub use weights::WeightInfo;

pub use pallet::*;

type BalanceOf<T> = pallet_treasury::BalanceOf<T>;

type PositiveImbalanceOf<T> = pallet_treasury::PositiveImbalanceOf<T>;

/// An index of a bounty. Just a `u32`.
pub type BountyIndex = u32;

/// A bounty proposal.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub struct Bounty<AccountId, Balance, BlockNumber> {
	/// The account proposing it.
	proposer: AccountId,
	/// The (total) amount that should be paid if the bounty is rewarded.
	value: Balance,
	/// The curator fee. Included in value.
	fee: Balance,
	/// The deposit of curator.
	curator_deposit: Balance,
	/// The amount held on deposit (reserved) for making this proposal.
	bond: Balance,
	/// The status of this bounty.
	status: BountyStatus<AccountId, BlockNumber>,
}

impl<AccountId: PartialEq + Clone + Ord, Balance, BlockNumber: Clone>
	Bounty<AccountId, Balance, BlockNumber>
{
	/// Getter for bounty status, to be used for child bounties.
	pub fn get_status(&self) -> BountyStatus<AccountId, BlockNumber> {
		self.status.clone()
	}
}

/// The status of a bounty proposal.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub enum BountyStatus<AccountId, BlockNumber> {
	/// The bounty is proposed and waiting for approval.
	Proposed,
	/// The bounty is approved and waiting to become active at next spend period.
	Approved,
	/// The bounty is funded and waiting for curator assignment.
	Funded,
	/// A curator has been proposed by the `ApproveOrigin`. Waiting for acceptance from the
	/// curator.
	CuratorProposed {
		/// The assigned curator of this bounty.
		curator: AccountId,
	},
	/// The bounty is active and waiting to be awarded.
	Active {
		/// The curator of this bounty.
		curator: AccountId,
		/// An update from the curator is due by this block, else they are considered inactive.
		update_due: BlockNumber,
	},
	/// The bounty is awarded and waiting to released after a delay.
	PendingPayout {
		/// The curator of this bounty.
		curator: AccountId,
		/// The beneficiary of the bounty.
		beneficiary: AccountId,
		/// When the bounty can be claimed.
		unlock_at: BlockNumber,
	},
}

/// The child-bounty manager.
pub trait ChildBountyManager<Balance> {
	/// Get the active child-bounties for a parent bounty.
	fn child_bounties_count(bounty_id: BountyIndex) -> BountyIndex;

	/// Get total curator fees of children-bounty curators.
	fn children_curator_fees(bounty_id: BountyIndex) -> Balance;
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config + pallet_treasury::Config {
		/// The amount held on deposit for placing a bounty proposal.
		#[pallet::constant]
		type BountyDepositBase: Get<BalanceOf<Self>>;

		/// The delay period for which a bounty beneficiary need to wait before claim the payout.
		#[pallet::constant]
		type BountyDepositPayoutDelay: Get<Self::BlockNumber>;

		/// Bounty duration in blocks.
		#[pallet::constant]
		type BountyUpdatePeriod: Get<Self::BlockNumber>;

		/// Percentage of the curator fee that will be reserved upfront as deposit for bounty
		/// curator.
		#[pallet::constant]
		type BountyCuratorDeposit: Get<Permill>;

		/// Minimum value for a bounty.
		#[pallet::constant]
		type BountyValueMinimum: Get<BalanceOf<Self>>;

		/// The amount held on deposit per byte within the tip report reason or bounty description.
		#[pallet::constant]
		type DataDepositPerByte: Get<BalanceOf<Self>>;

		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// Maximum acceptable reason length.
		///
		/// Benchmarks depend on this value, be sure to update weights file when changing this value
		#[pallet::constant]
		type MaximumReasonLength: Get<u32>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;

		/// The child-bounty manager.
		type ChildBountyManager: ChildBountyManager<BalanceOf<Self>>;
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Proposer's balance is too low.
		InsufficientProposersBalance,
		/// No proposal or bounty at that index.
		InvalidIndex,
		/// The reason given is just too big.
		ReasonTooBig,
		/// The bounty status is unexpected.
		UnexpectedStatus,
		/// Require bounty curator.
		RequireCurator,
		/// Invalid bounty value.
		InvalidValue,
		/// Invalid bounty fee.
		InvalidFee,
		/// A bounty payout is pending.
		/// To cancel the bounty, you must unassign and slash the curator.
		PendingPayout,
		/// The bounties cannot be claimed/closed because it's still in the countdown period.
		Premature,
		/// The bounty cannot be closed because it has active child-bounties.
		HasActiveChildBounty,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// New bounty proposal.
		BountyProposed { index: BountyIndex },
		/// A bounty proposal was rejected; funds were slashed.
		BountyRejected { index: BountyIndex, bond: BalanceOf<T> },
		/// A bounty proposal is funded and became active.
		BountyBecameActive { index: BountyIndex },
		/// A bounty is awarded to a beneficiary.
		BountyAwarded { index: BountyIndex, beneficiary: T::AccountId },
		/// A bounty is claimed by beneficiary.
		BountyClaimed { index: BountyIndex, payout: BalanceOf<T>, beneficiary: T::AccountId },
		/// A bounty is cancelled.
		BountyCanceled { index: BountyIndex },
		/// A bounty expiry is extended.
		BountyExtended { index: BountyIndex },
	}

	/// Number of bounty proposals that have been made.
	#[pallet::storage]
	#[pallet::getter(fn bounty_count)]
	pub type BountyCount<T: Config> = StorageValue<_, BountyIndex, ValueQuery>;

	/// Bounties that have been made.
	#[pallet::storage]
	#[pallet::getter(fn bounties)]
	pub type Bounties<T: Config> = StorageMap<
		_,
		Twox64Concat,
		BountyIndex,
		Bounty<T::AccountId, BalanceOf<T>, T::BlockNumber>,
	>;

	/// The description of each bounty.
	#[pallet::storage]
	#[pallet::getter(fn bounty_descriptions)]
	pub type BountyDescriptions<T: Config> = StorageMap<_, Twox64Concat, BountyIndex, Vec<u8>>;

	/// Bounty indices that have been approved but not yet funded.
	#[pallet::storage]
	#[pallet::getter(fn bounty_approvals)]
	pub type BountyApprovals<T: Config> = StorageValue<_, Vec<BountyIndex>, ValueQuery>;

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Propose a new bounty.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// Payment: `TipReportDepositBase` will be reserved from the origin account, as well as
		/// `DataDepositPerByte` for each byte in `reason`. It will be unreserved upon approval,
		/// or slashed when rejected.
		///
		/// - `curator`: The curator account whom will manage this bounty.
		/// - `fee`: The curator fee.
		/// - `value`: The total payment amount of this bounty, curator fee included.
		/// - `description`: The description of this bounty.
		#[pallet::weight(<T as Config>::WeightInfo::propose_bounty(description.len() as u32))]
		pub fn propose_bounty(
			origin: OriginFor<T>,
			#[pallet::compact] value: BalanceOf<T>,
			description: Vec<u8>,
		) -> DispatchResult {
			let proposer = ensure_signed(origin)?;
			Self::create_bounty(proposer, description, value)?;
			Ok(())
		}

		/// Approve a bounty proposal. At a later time, the bounty will be funded and become active
		/// and the original deposit will be returned.
		///
		/// May only be called from `T::ApproveOrigin`.
		///
		/// # <weight>
		/// - O(1).
		/// # </weight>
		#[pallet::weight(<T as Config>::WeightInfo::approve_bounty())]
		pub fn approve_bounty(
			origin: OriginFor<T>,
			#[pallet::compact] bounty_id: BountyIndex,
		) -> DispatchResult {
			T::ApproveOrigin::ensure_origin(origin)?;

			Bounties::<T>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let mut bounty = maybe_bounty.as_mut().ok_or(Error::<T>::InvalidIndex)?;
				ensure!(bounty.status == BountyStatus::Proposed, Error::<T>::UnexpectedStatus);

				bounty.status = BountyStatus::Approved;

				BountyApprovals::<T>::append(bounty_id);

				Ok(())
			})?;
			Ok(())
		}

		/// Assign a curator to a funded bounty.
		///
		/// May only be called from `T::ApproveOrigin`.
		///
		/// # <weight>
		/// - O(1).
		/// # </weight>
		#[pallet::weight(<T as Config>::WeightInfo::propose_curator())]
		pub fn propose_curator(
			origin: OriginFor<T>,
			#[pallet::compact] bounty_id: BountyIndex,
			curator: <T::Lookup as StaticLookup>::Source,
			#[pallet::compact] fee: BalanceOf<T>,
		) -> DispatchResult {
			T::ApproveOrigin::ensure_origin(origin)?;

			let curator = T::Lookup::lookup(curator)?;
			Bounties::<T>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let mut bounty = maybe_bounty.as_mut().ok_or(Error::<T>::InvalidIndex)?;
				match bounty.status {
					BountyStatus::Proposed | BountyStatus::Approved | BountyStatus::Funded => {},
					_ => return Err(Error::<T>::UnexpectedStatus.into()),
				};

				ensure!(fee < bounty.value, Error::<T>::InvalidFee);

				bounty.status = BountyStatus::CuratorProposed { curator };
				bounty.fee = fee;

				Ok(())
			})?;
			Ok(())
		}

		/// Unassign curator from a bounty.
		///
		/// This function can only be called by the `RejectOrigin` a signed origin.
		///
		/// If this function is called by the `RejectOrigin`, we assume that the curator is
		/// malicious or inactive. As a result, we will slash the curator when possible.
		///
		/// If the origin is the curator, we take this as a sign they are unable to do their job and
		/// they willingly give up. We could slash them, but for now we allow them to recover their
		/// deposit and exit without issue. (We may want to change this if it is abused.)
		///
		/// Finally, the origin can be anyone if and only if the curator is "inactive". This allows
		/// anyone in the community to call out that a curator is not doing their due diligence, and
		/// we should pick a new curator. In this case the curator should also be slashed.
		///
		/// # <weight>
		/// - O(1).
		/// # </weight>
		#[pallet::weight(<T as Config>::WeightInfo::unassign_curator())]
		pub fn unassign_curator(
			origin: OriginFor<T>,
			#[pallet::compact] bounty_id: BountyIndex,
		) -> DispatchResult {
			let maybe_sender = ensure_signed(origin.clone())
				.map(Some)
				.or_else(|_| T::RejectOrigin::ensure_origin(origin).map(|_| None))?;

			Bounties::<T>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let mut bounty = maybe_bounty.as_mut().ok_or(Error::<T>::InvalidIndex)?;

				let slash_curator = |curator: &T::AccountId, curator_deposit: &mut BalanceOf<T>| {
					let imbalance = T::Currency::slash_reserved(curator, *curator_deposit).0;
					T::OnSlash::on_unbalanced(imbalance);
					*curator_deposit = Zero::zero();
				};

				match bounty.status {
					BountyStatus::Proposed | BountyStatus::Approved | BountyStatus::Funded => {
						// No curator to unassign at this point.
						return Err(Error::<T>::UnexpectedStatus.into())
					},
					BountyStatus::CuratorProposed { ref curator } => {
						// A curator has been proposed, but not accepted yet.
						// Either `RejectOrigin` or the proposed curator can unassign the curator.
						ensure!(maybe_sender.map_or(true, |sender| sender == *curator), BadOrigin);
					},
					BountyStatus::Active { ref curator, ref update_due } => {
						// The bounty is active.
						match maybe_sender {
							// If the `RejectOrigin` is calling this function, slash the curator.
							None => {
								slash_curator(curator, &mut bounty.curator_deposit);
								// Continue to change bounty status below...
							},
							Some(sender) => {
								// If the sender is not the curator, and the curator is inactive,
								// slash the curator.
								if sender != *curator {
									let block_number = frame_system::Pallet::<T>::block_number();
									if *update_due < block_number {
										slash_curator(curator, &mut bounty.curator_deposit);
									// Continue to change bounty status below...
									} else {
										// Curator has more time to give an update.
										return Err(Error::<T>::Premature.into())
									}
								} else {
									// Else this is the curator, willingly giving up their role.
									// Give back their deposit.
									let err_amount =
										T::Currency::unreserve(&curator, bounty.curator_deposit);
									debug_assert!(err_amount.is_zero());
									bounty.curator_deposit = Zero::zero();
									// Continue to change bounty status below...
								}
							},
						}
					},
					BountyStatus::PendingPayout { ref curator, .. } => {
						// The bounty is pending payout, so only council can unassign a curator.
						// By doing so, they are claiming the curator is acting maliciously, so
						// we slash the curator.
						ensure!(maybe_sender.is_none(), BadOrigin);
						slash_curator(curator, &mut bounty.curator_deposit);
						// Continue to change bounty status below...
					},
				};

				bounty.status = BountyStatus::Funded;
				Ok(())
			})?;
			Ok(())
		}

		/// Accept the curator role for a bounty.
		/// A deposit will be reserved from curator and refund upon successful payout.
		///
		/// May only be called from the curator.
		///
		/// # <weight>
		/// - O(1).
		/// # </weight>
		#[pallet::weight(<T as Config>::WeightInfo::accept_curator())]
		pub fn accept_curator(
			origin: OriginFor<T>,
			#[pallet::compact] bounty_id: BountyIndex,
		) -> DispatchResult {
			let signer = ensure_signed(origin)?;

			Bounties::<T>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let mut bounty = maybe_bounty.as_mut().ok_or(Error::<T>::InvalidIndex)?;

				match bounty.status {
					BountyStatus::CuratorProposed { ref curator } => {
						ensure!(signer == *curator, Error::<T>::RequireCurator);

						let deposit = T::BountyCuratorDeposit::get() * bounty.fee;
						T::Currency::reserve(curator, deposit)?;
						bounty.curator_deposit = deposit;

						let update_due = frame_system::Pallet::<T>::block_number() +
							T::BountyUpdatePeriod::get();
						bounty.status =
							BountyStatus::Active { curator: curator.clone(), update_due };

						Ok(())
					},
					_ => Err(Error::<T>::UnexpectedStatus.into()),
				}
			})?;
			Ok(())
		}

		/// Award bounty to a beneficiary account. The beneficiary will be able to claim the funds
		/// after a delay.
		///
		/// The dispatch origin for this call must be the curator of this bounty.
		///
		/// - `bounty_id`: Bounty ID to award.
		/// - `beneficiary`: The beneficiary account whom will receive the payout.
		///
		/// # <weight>
		/// - O(1).
		/// # </weight>
		#[pallet::weight(<T as Config>::WeightInfo::award_bounty())]
		pub fn award_bounty(
			origin: OriginFor<T>,
			#[pallet::compact] bounty_id: BountyIndex,
			beneficiary: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			let signer = ensure_signed(origin)?;
			let beneficiary = T::Lookup::lookup(beneficiary)?;

			Bounties::<T>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let mut bounty = maybe_bounty.as_mut().ok_or(Error::<T>::InvalidIndex)?;

				// Ensure no active child-bounties before processing the call.
				ensure!(
					T::ChildBountyManager::child_bounties_count(bounty_id) == 0,
					Error::<T>::HasActiveChildBounty
				);

				match &bounty.status {
					BountyStatus::Active { curator, .. } => {
						ensure!(signer == *curator, Error::<T>::RequireCurator);
					},
					_ => return Err(Error::<T>::UnexpectedStatus.into()),
				}
				bounty.status = BountyStatus::PendingPayout {
					curator: signer,
					beneficiary: beneficiary.clone(),
					unlock_at: frame_system::Pallet::<T>::block_number() +
						T::BountyDepositPayoutDelay::get(),
				};

				Ok(())
			})?;

			Self::deposit_event(Event::<T>::BountyAwarded { index: bounty_id, beneficiary });
			Ok(())
		}

		/// Claim the payout from an awarded bounty after payout delay.
		///
		/// The dispatch origin for this call must be the beneficiary of this bounty.
		///
		/// - `bounty_id`: Bounty ID to claim.
		///
		/// # <weight>
		/// - O(1).
		/// # </weight>
		#[pallet::weight(<T as Config>::WeightInfo::claim_bounty())]
		pub fn claim_bounty(
			origin: OriginFor<T>,
			#[pallet::compact] bounty_id: BountyIndex,
		) -> DispatchResult {
			let _ = ensure_signed(origin)?; // anyone can trigger claim

			Bounties::<T>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let bounty = maybe_bounty.take().ok_or(Error::<T>::InvalidIndex)?;
				if let BountyStatus::PendingPayout { curator, beneficiary, unlock_at } =
					bounty.status
				{
					ensure!(
						frame_system::Pallet::<T>::block_number() >= unlock_at,
						Error::<T>::Premature
					);
					let bounty_account = Self::bounty_account_id(bounty_id);
					let balance = T::Currency::free_balance(&bounty_account);
					let fee = bounty.fee.min(balance); // just to be safe
					let payout = balance.saturating_sub(fee);
					let err_amount = T::Currency::unreserve(&curator, bounty.curator_deposit);
					debug_assert!(err_amount.is_zero());

					// Get total child-bounties curator fees, and subtract it from master curator
					// fee.
					let children_fee = T::ChildBountyManager::children_curator_fees(bounty_id);
					debug_assert!(children_fee <= fee);

					let final_fee = fee.saturating_sub(children_fee);
					let res =
						T::Currency::transfer(&bounty_account, &curator, final_fee, AllowDeath); // should not fail
					debug_assert!(res.is_ok());
					let res =
						T::Currency::transfer(&bounty_account, &beneficiary, payout, AllowDeath); // should not fail
					debug_assert!(res.is_ok());

					*maybe_bounty = None;

					BountyDescriptions::<T>::remove(bounty_id);

					Self::deposit_event(Event::<T>::BountyClaimed {
						index: bounty_id,
						payout,
						beneficiary,
					});
					Ok(())
				} else {
					Err(Error::<T>::UnexpectedStatus.into())
				}
			})?;
			Ok(())
		}

		/// Cancel a proposed or active bounty. All the funds will be sent to treasury and
		/// the curator deposit will be unreserved if possible.
		///
		/// Only `T::RejectOrigin` is able to cancel a bounty.
		///
		/// - `bounty_id`: Bounty ID to cancel.
		///
		/// # <weight>
		/// - O(1).
		/// # </weight>
		#[pallet::weight(<T as Config>::WeightInfo::close_bounty_proposed()
			.max(<T as Config>::WeightInfo::close_bounty_active()))]
		pub fn close_bounty(
			origin: OriginFor<T>,
			#[pallet::compact] bounty_id: BountyIndex,
		) -> DispatchResultWithPostInfo {
			T::RejectOrigin::ensure_origin(origin)?;

			Bounties::<T>::try_mutate_exists(
				bounty_id,
				|maybe_bounty| -> DispatchResultWithPostInfo {
					let bounty = maybe_bounty.as_ref().ok_or(Error::<T>::InvalidIndex)?;

					// Ensure no active child-bounties before processing the call.
					ensure!(
						T::ChildBountyManager::child_bounties_count(bounty_id) == 0,
						Error::<T>::HasActiveChildBounty
					);

					match &bounty.status {
						BountyStatus::Proposed => {
							// The reject origin would like to cancel a proposed bounty.
							BountyDescriptions::<T>::remove(bounty_id);
							let value = bounty.bond;
							let imbalance = T::Currency::slash_reserved(&bounty.proposer, value).0;
							T::OnSlash::on_unbalanced(imbalance);
							*maybe_bounty = None;

							Self::deposit_event(Event::<T>::BountyRejected {
								index: bounty_id,
								bond: value,
							});
							// Return early, nothing else to do.
							return Ok(
								Some(<T as Config>::WeightInfo::close_bounty_proposed()).into()
							)
						},
						BountyStatus::Approved => {
							// For weight reasons, we don't allow a council to cancel in this phase.
							// We ask for them to wait until it is funded before they can cancel.
							return Err(Error::<T>::UnexpectedStatus.into())
						},
						BountyStatus::Funded | BountyStatus::CuratorProposed { .. } => {
							// Nothing extra to do besides the removal of the bounty below.
						},
						BountyStatus::Active { curator, .. } => {
							// Cancelled by council, refund deposit of the working curator.
							let err_amount =
								T::Currency::unreserve(&curator, bounty.curator_deposit);
							debug_assert!(err_amount.is_zero());
							// Then execute removal of the bounty below.
						},
						BountyStatus::PendingPayout { .. } => {
							// Bounty is already pending payout. If council wants to cancel
							// this bounty, it should mean the curator was acting maliciously.
							// So the council should first unassign the curator, slashing their
							// deposit.
							return Err(Error::<T>::PendingPayout.into())
						},
					}

					let bounty_account = Self::bounty_account_id(bounty_id);

					BountyDescriptions::<T>::remove(bounty_id);

					let balance = T::Currency::free_balance(&bounty_account);
					let res = T::Currency::transfer(
						&bounty_account,
						&Self::account_id(),
						balance,
						AllowDeath,
					); // should not fail
					debug_assert!(res.is_ok());
					*maybe_bounty = None;

					Self::deposit_event(Event::<T>::BountyCanceled { index: bounty_id });
					Ok(Some(<T as Config>::WeightInfo::close_bounty_active()).into())
				},
			)
		}

		/// Extend the expiry time of an active bounty.
		///
		/// The dispatch origin for this call must be the curator of this bounty.
		///
		/// - `bounty_id`: Bounty ID to extend.
		/// - `remark`: additional information.
		///
		/// # <weight>
		/// - O(1).
		/// # </weight>
		#[pallet::weight(<T as Config>::WeightInfo::extend_bounty_expiry())]
		pub fn extend_bounty_expiry(
			origin: OriginFor<T>,
			#[pallet::compact] bounty_id: BountyIndex,
			_remark: Vec<u8>,
		) -> DispatchResult {
			let signer = ensure_signed(origin)?;

			Bounties::<T>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let bounty = maybe_bounty.as_mut().ok_or(Error::<T>::InvalidIndex)?;

				match bounty.status {
					BountyStatus::Active { ref curator, ref mut update_due } => {
						ensure!(*curator == signer, Error::<T>::RequireCurator);
						*update_due = (frame_system::Pallet::<T>::block_number() +
							T::BountyUpdatePeriod::get())
						.max(*update_due);
					},
					_ => return Err(Error::<T>::UnexpectedStatus.into()),
				}

				Ok(())
			})?;

			Self::deposit_event(Event::<T>::BountyExtended { index: bounty_id });
			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	// Add public immutables and private mutables.

	/// The account ID of the treasury pot.
	///
	/// This actually does computation. If you need to keep using it, then make sure you cache the
	/// value and only call this once.
	pub fn account_id() -> T::AccountId {
		T::PalletId::get().into_account()
	}

	/// The account ID of a bounty account
	pub fn bounty_account_id(id: BountyIndex) -> T::AccountId {
		// only use two byte prefix to support 16 byte account id (used by test)
		// "modl" ++ "py/trsry" ++ "bt" is 14 bytes, and two bytes remaining for bounty index
		T::PalletId::get().into_sub_account(("bt", id))
	}

	fn create_bounty(
		proposer: T::AccountId,
		description: Vec<u8>,
		value: BalanceOf<T>,
	) -> DispatchResult {
		ensure!(
			description.len() <= T::MaximumReasonLength::get() as usize,
			Error::<T>::ReasonTooBig
		);
		ensure!(value >= T::BountyValueMinimum::get(), Error::<T>::InvalidValue);

		let index = Self::bounty_count();

		// reserve deposit for new bounty
		let bond = T::BountyDepositBase::get() +
			T::DataDepositPerByte::get() * (description.len() as u32).into();
		T::Currency::reserve(&proposer, bond)
			.map_err(|_| Error::<T>::InsufficientProposersBalance)?;

		BountyCount::<T>::put(index + 1);

		let bounty = Bounty {
			proposer,
			value,
			fee: 0u32.into(),
			curator_deposit: 0u32.into(),
			bond,
			status: BountyStatus::Proposed,
		};

		Bounties::<T>::insert(index, &bounty);
		BountyDescriptions::<T>::insert(index, description);

		Self::deposit_event(Event::<T>::BountyProposed { index });

		Ok(())
	}
}

impl<T: Config> pallet_treasury::SpendFunds<T> for Pallet<T> {
	fn spend_funds(
		budget_remaining: &mut BalanceOf<T>,
		imbalance: &mut PositiveImbalanceOf<T>,
		total_weight: &mut Weight,
		missed_any: &mut bool,
	) {
		let bounties_len = BountyApprovals::<T>::mutate(|v| {
			let bounties_approval_len = v.len() as u32;
			v.retain(|&index| {
				Bounties::<T>::mutate(index, |bounty| {
					// Should always be true, but shouldn't panic if false or we're screwed.
					if let Some(bounty) = bounty {
						if bounty.value <= *budget_remaining {
							*budget_remaining -= bounty.value;

							bounty.status = BountyStatus::Funded;

							// return their deposit.
							let err_amount = T::Currency::unreserve(&bounty.proposer, bounty.bond);
							debug_assert!(err_amount.is_zero());

							// fund the bounty account
							imbalance.subsume(T::Currency::deposit_creating(
								&Self::bounty_account_id(index),
								bounty.value,
							));

							Self::deposit_event(Event::<T>::BountyBecameActive { index });
							false
						} else {
							*missed_any = true;
							true
						}
					} else {
						false
					}
				})
			});
			bounties_approval_len
		});

		*total_weight += <T as Config>::WeightInfo::spend_funds(bounties_len);
	}
}

// Default impl for when ChildBounties is not being used in the runtime.
impl<Balance: Zero> ChildBountyManager<Balance> for () {
	fn child_bounties_count(_bounty_id: BountyIndex) -> BountyIndex {
		Default::default()
	}

	fn children_curator_fees(_bounty_id: BountyIndex) -> Balance {
		Zero::zero()
	}
}
