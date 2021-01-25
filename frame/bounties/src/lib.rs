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

mod tests;
mod benchmarking;
pub mod weights;

use sp_std::{
	prelude::*,
};

use frame_support::{decl_module, decl_storage, decl_event, ensure, decl_error};

use frame_support::traits::{
	Currency, Get, Imbalance, OnUnbalanced, ExistenceRequirement::{AllowDeath},
	ReservableCurrency, BalanceStatus};

use sp_runtime::{Permill, RuntimeDebug, DispatchResult, traits::{
	Zero, StaticLookup, AccountIdConversion, Saturating, BadOrigin
}};

use frame_support::dispatch::DispatchResultWithPostInfo;
use frame_support::traits::{EnsureOrigin};

use frame_support::weights::{Weight};

use codec::{Encode, Decode};
use frame_system::{self as system, ensure_signed};
pub use weights::WeightInfo;

type BalanceOf<T> = pallet_treasury::BalanceOf<T>;

type PositiveImbalanceOf<T> = pallet_treasury::PositiveImbalanceOf<T>;

pub trait Config: frame_system::Config + pallet_treasury::Config {

	/// The amount held on deposit for placing a bounty proposal.
	type BountyDepositBase: Get<BalanceOf<Self>>;

	/// The delay period for which a bounty beneficiary need to wait before claim the payout.
	type BountyDepositPayoutDelay: Get<Self::BlockNumber>;

	/// Bounty duration in blocks.
	type BountyUpdatePeriod: Get<Self::BlockNumber>;

	/// Percentage of the curator fee that will be reserved upfront as deposit for bounty curator.
	type BountyCuratorDeposit: Get<Permill>;

	/// Minimum value for a bounty.
	type BountyValueMinimum: Get<BalanceOf<Self>>;

	/// The amount held on deposit per byte within the tip report reason or bounty description.
	type DataDepositPerByte: Get<BalanceOf<Self>>;

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Config>::Event>;

	/// Maximum acceptable reason length.
	type MaximumReasonLength: Get<u32>;

	/// Weight information for extrinsics in this pallet.
	type WeightInfo: WeightInfo;

	/// Maximum number of subbounty that can be added to active bounty.
	type MaxSubBountyCount: Get<u32>;
}

/// An index of a bounty. Just a `u32`.
pub type BountyIndex = u32;

/// A Subbounty proposal.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
pub struct SubBounty<AccountId, Balance, BlockNumber> {
	/// The account proposing it.
	proposer: AccountId,
	/// The (total) amount that should be paid if the bounty is rewarded.
	value: Balance,
	/// Parent bounty curator or master_curator
	curator: AccountId,
	/// The curator fee. Included in value.
	fee: Balance,
	/// The deposit of curator.
	curator_deposit: Balance,
	/// The amount held on deposit (reserved) for making this proposal.
	bond: Balance,
	/// The status of this bounty.
	status: BountyStatus<AccountId, BlockNumber>,
}

/// A bounty proposal.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
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
	/// Subbounties counter
	subbountycount: BountyIndex,
	/// Sorted list of active Subbounties
	activesubbounty: Vec<BountyIndex>,
}

/// The status of a bounty proposal.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
pub enum BountyStatus<AccountId, BlockNumber> {
	/// The bounty is proposed and waiting for approval.
	Proposed,
	/// The bounty is approved and waiting to become active at next spend period.
	Approved,
	/// The bounty is funded and waiting for curator assignment.
	Funded,
	/// A curator has been proposed by the `ApproveOrigin`. Waiting for acceptance from the curator.
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

// Note :: For backward compatibility reasons,
// pallet-bounties uses Treasury for storage.
// This is temporary solution, soon will get replaced with
// Own storage identifier.
decl_storage! {
	trait Store for Module<T: Config> as Treasury {

		/// Number of bounty proposals that have been made.
		pub BountyCount get(fn bounty_count): BountyIndex;

		/// Bounties that have been made.
		pub Bounties get(fn bounties):
		map hasher(twox_64_concat) BountyIndex
		=> Option<Bounty<T::AccountId, BalanceOf<T>, T::BlockNumber>>;

		/// The description of each bounty.
		pub BountyDescriptions get(fn bounty_descriptions): map hasher(twox_64_concat) BountyIndex => Option<Vec<u8>>;

		/// Bounty indices that have been approved but not yet funded.
		pub BountyApprovals get(fn bounty_approvals): Vec<BountyIndex>;

		/// SubBounties that have been made.
		pub SubBounties get(fn subbounties):
		double_map hasher(twox_64_concat) BountyIndex,
		hasher(twox_64_concat) BountyIndex =>
		Option<SubBounty<T::AccountId, BalanceOf<T>, T::BlockNumber>>;

		/// The SubBounties description of each subbounty.
		pub SubBountyDescriptions get(fn subbounty_descriptions):
		double_map hasher(twox_64_concat) BountyIndex,
		hasher(twox_64_concat) BountyIndex => Option<Vec<u8>>;

		/// SubBounty indices that have been approved but not yet funded.
		pub SubBountyApprovals get(fn subbounty_approvals): Vec<(BountyIndex, BountyIndex)>;
	}
}

decl_event!(
	pub enum Event<T>
	where
		Balance = BalanceOf<T>,
		<T as frame_system::Config>::AccountId,
	{
		/// New bounty proposal. \[index\]
		BountyProposed(BountyIndex),
		/// A bounty proposal was rejected; funds were slashed. \[index, bond\]
		BountyRejected(BountyIndex, Balance),
		/// A bounty proposal is funded and became active. \[index\]
		BountyBecameActive(BountyIndex),
		/// A bounty is awarded to a beneficiary. \[index, beneficiary\]
		BountyAwarded(BountyIndex, AccountId),
		/// A bounty is claimed by beneficiary. \[index, payout, beneficiary\]
		BountyClaimed(BountyIndex, Balance, AccountId),
		/// A bounty is cancelled. \[index\]
		BountyCanceled(BountyIndex),
		/// A bounty expiry is extended. \[index\]
		BountyExtended(BountyIndex),
		/// A subbounty is approved. \[index, subbounty index\]
		SubBountyApproved(BountyIndex, BountyIndex),
		/// A subbounty is awarded to a beneficiary. \[index, subbounty index, beneficiary\]
		SubBountyAwarded(BountyIndex, BountyIndex, AccountId),
		/// A Subbounty is claimed by beneficiary. \[index, subbounty index, payout, beneficiary\]
		SubBountyClaimed(BountyIndex, BountyIndex, Balance, AccountId),
		/// A Subbounty proposal was rejected; funds were slashed. \[index, subbounty index, bond\]
		SubBountyRejected(BountyIndex, BountyIndex, Balance),
		/// A Subbounty is cancelled. \[index, subbounty index,\]
		SubBountyCanceled(BountyIndex, BountyIndex),
		/// A subbounty proposal is funded and became active. \[index, subbounty index\]
		SubBountyBecameActive(BountyIndex, BountyIndex),
		/// A Subbounty expiry is extended. \[index, subbounty index,\]
		SubBountyExtended(BountyIndex, BountyIndex),
	}
);

decl_error! {
	/// Error for the treasury module.
	pub enum Error for Module<T: Config> {
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
		/// The bounty balance is not enough to add new subbounty.
		InsufficientBountyBalance,
		/// Subbounty active
		SubBountyActive,
		/// Number of subbounty recached MaxSubBountyCount
		SubBountyMaxReached,
	}
}

decl_module! {
	pub struct Module<T: Config>
		for enum Call
		where origin: T::Origin
	{
		/// The amount held on deposit per byte within bounty description.
		const DataDepositPerByte: BalanceOf<T> = T::DataDepositPerByte::get();

		/// The amount held on deposit for placing a bounty proposal.
		const BountyDepositBase: BalanceOf<T> = T::BountyDepositBase::get();

		/// The delay period for which a bounty beneficiary need to wait before claim the payout.
		const BountyDepositPayoutDelay: T::BlockNumber = T::BountyDepositPayoutDelay::get();

		/// Bounty duration in blocks.
		const BountyUpdatePeriod: T::BlockNumber = T::BountyUpdatePeriod::get();

		/// Percentage of the curator fee that will be reserved upfront as deposit for bounty curator.
		const BountyCuratorDeposit: Permill = T::BountyCuratorDeposit::get();

		/// Minimum value for a bounty.
		const BountyValueMinimum: BalanceOf<T> = T::BountyValueMinimum::get();

		/// Maximum acceptable reason length.
		const MaximumReasonLength: u32 = T::MaximumReasonLength::get();

		type Error = Error<T>;

		fn deposit_event() = default;

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
		#[weight = <T as Config>::WeightInfo::propose_bounty(description.len() as u32)]
		fn propose_bounty(
			origin,
			#[compact] value: BalanceOf<T>,
			description: Vec<u8>,
		) {
			let proposer = ensure_signed(origin)?;
			Self::create_bounty(proposer, description, value)?;
		}

		/// Approve a bounty proposal. At a later time, the bounty will be funded and become active
		/// and the original deposit will be returned.
		///
		/// May only be called from `T::ApproveOrigin`.
		///
		/// # <weight>
		/// - O(1).
		/// # </weight>
		#[weight = <T as Config>::WeightInfo::approve_bounty()]
		fn approve_bounty(origin, #[compact] bounty_id: BountyIndex) {
			T::ApproveOrigin::ensure_origin(origin)?;

			Bounties::<T>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let mut bounty = maybe_bounty.as_mut().ok_or(Error::<T>::InvalidIndex)?;
				ensure!(bounty.status == BountyStatus::Proposed, Error::<T>::UnexpectedStatus);

				bounty.status = BountyStatus::Approved;

				BountyApprovals::append(bounty_id);

				Ok(())
			})?;
		}

		/// Assign a curator to a funded bounty.
		///
		/// May only be called from `T::ApproveOrigin`.
		///
		/// # <weight>
		/// - O(1).
		/// # </weight>
		#[weight = <T as Config>::WeightInfo::propose_curator()]
		fn propose_curator(
			origin,
			#[compact] bounty_id: BountyIndex,
			curator: <T::Lookup as StaticLookup>::Source,
			#[compact] fee: BalanceOf<T>,
		) {
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

				// Reserve the fee for Curator
				let bounty_account = Self::bounty_account_id(bounty_id);
				let balance = T::Currency::free_balance(&bounty_account);
				let fee = bounty.fee.min(balance); // just to be safe
				T::Currency::reserve(&bounty_account, fee)?;

				Ok(())
			})?;
		}

		/// Unassign curator from a bounty.
		///
		/// This function can only be called by the `RejectOrigin` a signed origin.
		///
		/// If this function is called by the `RejectOrigin`, we assume that the curator is malicious
		/// or inactive. As a result, we will slash the curator when possible.
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
		#[weight = <T as Config>::WeightInfo::unassign_curator()]
		fn unassign_curator(
			origin,
			#[compact] bounty_id: BountyIndex,
		) {
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
					}
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
									let block_number = system::Module::<T>::block_number();
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
									let _ = T::Currency::unreserve(&curator, bounty.curator_deposit);
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
				// Unreserve the fee for Curator which got reserved during "propose_curator()"
				let bounty_account = Self::bounty_account_id(bounty_id);
				T::Currency::unreserve(&bounty_account, bounty.fee);
				bounty.status = BountyStatus::Funded;
				Ok(())
			})?;
		}
		/// Accept the curator role for a bounty.
		/// A deposit will be reserved from curator and refund upon successful payout.
		///
		/// May only be called from the curator.
		///
		/// # <weight>
		/// - O(1).
		/// # </weight>
		#[weight = <T as Config>::WeightInfo::accept_curator()]
		fn accept_curator(origin, #[compact] bounty_id: BountyIndex) {
			let signer = ensure_signed(origin)?;

			Bounties::<T>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let mut bounty = maybe_bounty.as_mut().ok_or(Error::<T>::InvalidIndex)?;

				match bounty.status {
					BountyStatus::CuratorProposed { ref curator } => {
						ensure!(signer == *curator, Error::<T>::RequireCurator);

						// Reserve the Curator deposit
						let deposit = T::BountyCuratorDeposit::get() * bounty.fee;
						T::Currency::reserve(curator, deposit)?;
						bounty.curator_deposit = deposit;

						// Update the Curator info to Subbounties list
						if bounty.activesubbounty.len() > 0 {
							bounty.activesubbounty
							.iter()
							.for_each(|subbounty_id| {
								let _ = SubBounties::<T>::try_mutate_exists(bounty_id,
									subbounty_id,
									|maybe_subbounty| -> DispatchResult {
									let mut subbounty = maybe_subbounty.as_mut().unwrap();
									subbounty.curator = curator.clone();
									Ok(())
								});
							});
						}

						let update_due = system::Module::<T>::block_number() + T::BountyUpdatePeriod::get();
						bounty.status = BountyStatus::Active { curator: curator.clone(), update_due };

						Ok(())
					},
					_ => Err(Error::<T>::UnexpectedStatus.into()),
				}
			})?;
		}

		/// Award bounty to a beneficiary account. The beneficiary will be able to claim the funds after a delay.
		///
		/// The dispatch origin for this call must be the curator of this bounty.
		///
		/// - `bounty_id`: Bounty ID to award.
		/// - `beneficiary`: The beneficiary account whom will receive the payout.
		///
		/// # <weight>
		/// - O(1).
		/// # </weight>
		#[weight = <T as Config>::WeightInfo::award_bounty()]
		fn award_bounty(origin, #[compact] bounty_id: BountyIndex, beneficiary: <T::Lookup as StaticLookup>::Source) {
			let signer = ensure_signed(origin)?;
			let beneficiary = T::Lookup::lookup(beneficiary)?;

			Bounties::<T>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let mut bounty = maybe_bounty.as_mut().ok_or(Error::<T>::InvalidIndex)?;

				ensure!(bounty.activesubbounty.len() == 0, Error::<T>::SubBountyActive);

				match &bounty.status {
					BountyStatus::Active {
						curator,
						..
					} => {
						ensure!(signer == *curator, Error::<T>::RequireCurator);
					},
					_ => return Err(Error::<T>::UnexpectedStatus.into()),
				}
				bounty.status = BountyStatus::PendingPayout {
					curator: signer,
					beneficiary: beneficiary.clone(),
					unlock_at: system::Module::<T>::block_number() + T::BountyDepositPayoutDelay::get(),
				};

				Ok(())
			})?;

			Self::deposit_event(Event::<T>::BountyAwarded(bounty_id, beneficiary));
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
		#[weight = <T as Config>::WeightInfo::claim_bounty()]
		fn claim_bounty(origin, #[compact] bounty_id: BountyIndex) {
			let _ = ensure_signed(origin)?; // anyone can trigger claim

			Bounties::<T>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let bounty = maybe_bounty.take().ok_or(Error::<T>::InvalidIndex)?;
				if let BountyStatus::PendingPayout { curator, beneficiary, unlock_at } = bounty.status {
					ensure!(system::Module::<T>::block_number() >= unlock_at, Error::<T>::Premature);
					// Get bounty account id
					let bounty_account = Self::bounty_account_id(bounty_id);
					// Make curator fee payment & unreserve the deposit
					let _ = T::Currency::unreserve(&curator, bounty.curator_deposit);
					let _ = T::Currency::repatriate_reserved(
						&bounty_account,
						&curator,
						bounty.fee,
						Status::Free,
					);
					// Make beneficiary payment
					let balance = T::Currency::free_balance(&bounty_account);

					// TODO :: Have to recheck this condition
					// Incase of curator managing subbounties
					// curator may have to close the bounty and transfer the
					// balance back to treasury, in that case api is executed
					// with beneficiary as curator.
					if curator != beneficiary {
						let _ = T::Currency::transfer(&bounty_account, &beneficiary, balance, AllowDeath); // should not fail
					} else {
						let _ = T::Currency::transfer(&bounty_account, &Self::account_id(), balance, AllowDeath); // should not fail
					}
					// State Clean-up
					BountyDescriptions::remove(bounty_id);
					*maybe_bounty = None;
					// Trigger Event
					Self::deposit_event(Event::<T>::BountyClaimed(bounty_id, balance, beneficiary));
					Ok(())
				} else {
					Err(Error::<T>::UnexpectedStatus.into())
				}
			})?;
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
		#[weight = <T as Config>::WeightInfo::close_bounty_proposed().max(<T as Config>::WeightInfo::close_bounty_active())]
		fn close_bounty(origin, #[compact] bounty_id: BountyIndex) -> DispatchResultWithPostInfo {
			T::RejectOrigin::ensure_origin(origin)?;

			Bounties::<T>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResultWithPostInfo {
				let bounty = maybe_bounty.as_ref().ok_or(Error::<T>::InvalidIndex)?;

				match &bounty.status {
					BountyStatus::Proposed => {
						// The reject origin would like to cancel a proposed bounty.
						BountyDescriptions::remove(bounty_id);
						let value = bounty.bond;
						let imbalance = T::Currency::slash_reserved(&bounty.proposer, value).0;
						T::OnSlash::on_unbalanced(imbalance);
						*maybe_bounty = None;

						Self::deposit_event(Event::<T>::BountyRejected(bounty_id, value));
						// Return early, nothing else to do.
						return Ok(Some(<T as Config>::WeightInfo::close_bounty_proposed()).into())
					},
					BountyStatus::Approved => {
						// For weight reasons, we don't allow a council to cancel in this phase.
						// We ask for them to wait until it is funded before they can cancel.
						return Err(Error::<T>::UnexpectedStatus.into())
					},
					BountyStatus::Funded => {
						// Nothing extra to do besides the removal of the bounty below.
					},
					BountyStatus::CuratorProposed { .. } => {
						// Unreserve the fee for Curator which got reserved during "propose_curator()"
						let bounty_account = Self::bounty_account_id(bounty_id);
						T::Currency::unreserve(&bounty_account, bounty.fee);
						// Then execute removal of the bounty below.
					},
					BountyStatus::Active { curator, .. } => {
						// Cancelled by council, refund deposit of the working curator.
						let _ = T::Currency::unreserve(&curator, bounty.curator_deposit);
						// TODO :: Have to check on curator fee
						// if any subbounties are successfully completed
						// Unreserve the fee for Curator which got reserved during "propose_curator()"
						let bounty_account = Self::bounty_account_id(bounty_id);
						T::Currency::unreserve(&bounty_account, bounty.fee);
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

				// close if there are any active subbounty
				if bounty.activesubbounty.len() > 0 {
					bounty.activesubbounty
					.iter()
					.for_each(|subbounty_id| {
						let _ = Self::impl_close_subbounty(bounty_id, *subbounty_id);
					});
				}

				let bounty_account = Self::bounty_account_id(bounty_id);
				BountyDescriptions::remove(bounty_id);

				let balance = T::Currency::free_balance(&bounty_account);
				let _ = T::Currency::transfer(&bounty_account, &Self::account_id(), balance, AllowDeath); // should not fail
				*maybe_bounty = None;

				Self::deposit_event(Event::<T>::BountyCanceled(bounty_id));
				Ok(Some(<T as Config>::WeightInfo::close_bounty_active()).into())
			})
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
		#[weight = <T as Config>::WeightInfo::extend_bounty_expiry()]
		fn extend_bounty_expiry(origin, #[compact] bounty_id: BountyIndex, remark: Vec<u8>) {
			let signer = ensure_signed(origin)?;

			Bounties::<T>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let bounty = maybe_bounty.as_mut().ok_or(Error::<T>::InvalidIndex)?;

				match bounty.status {
					BountyStatus::Active { ref curator, ref mut update_due } => {
						ensure!(*curator == signer, Error::<T>::RequireCurator);
						*update_due = (system::Module::<T>::block_number() + T::BountyUpdatePeriod::get()).max(*update_due);
					},
					_ => return Err(Error::<T>::UnexpectedStatus.into()),
				}
				// TODO :: Have to recheck this requirement
				// extend expiry if there are any active subbounty
				if bounty.activesubbounty.len() > 0 {
					bounty.activesubbounty
					.iter()
					.for_each(|subbounty_id| {
						let _ = Self::impl_extend_subbounty_expiry(&signer, bounty_id, *subbounty_id, remark.clone());
					});
				}
				Ok(())
			})?;

			Self::deposit_event(Event::<T>::BountyExtended(bounty_id));
		}

		/// Add a new subbounty.
		///
		/// The dispatch origin for this call must be curator.
		/// Bounty must me in "active" state.
		///
		/// Subbouty gets added successfully & fund gets reserved, if bounty has enough fund.
		/// else call get failed.
		///
		/// Upperbount to maximum number of subbounties that can be added is
		/// managed via runtime trait config 'MaxSubBountyCount'.
		///
		/// Payment: `TipReportDepositBase` will be reserved from the origin account, as well as
		/// `DataDepositPerByte` for each byte in `reason`. It will be unreserved upon approval,
		/// or slashed when rejected.
		///
		/// if call is success, state of subbounty is moved to "Approved" state.
		/// And later moved to "Funded" state as part of "spend_fund()" callback.
		///
		/// - `bounty_id`: Bounty ID for which subbounty to be added.
		/// - `value`: Value for executing the proposal.
		/// - `description`: Text description for the subbounty.
		#[weight = 10_000]
		fn add_subbounty(origin,
			#[compact] bounty_id: BountyIndex,
			value: BalanceOf<T>,
			description: Vec<u8>,
		)
		{
			let signer = ensure_signed(origin)?;

			Bounties::<T>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let mut bounty = maybe_bounty.as_mut().ok_or(Error::<T>::InvalidIndex)?;
				match bounty.status {
					BountyStatus::Active {
						ref curator,
						..
					} => {
						ensure!(signer == *curator, Error::<T>::RequireCurator);

						// Verify the arguments
						ensure!(description.len() <= T::MaximumReasonLength::get() as usize,
							Error::<T>::ReasonTooBig,
						);
						ensure!(value >= T::BountyValueMinimum::get(),
							Error::<T>::InvalidValue,
						);
						ensure!(bounty.subbountycount <= T::MaxSubBountyCount::get() as u32,
							Error::<T>::SubBountyMaxReached,
						);

						// reserve deposit for new bounty
						let bond = T::BountyDepositBase::get()
							+ T::DataDepositPerByte::get() * (description.len() as u32).into();
						T::Currency::reserve(&signer, bond)
							.map_err(|_| Error::<T>::InsufficientProposersBalance)?;

						// Makesure Parent bounty have enough balance to fund Subbounty
						let bounty_account = Self::bounty_account_id(bounty_id);
						let balance = T::Currency::free_balance(&bounty_account);
						ensure!(value < balance, Error::<T>::InsufficientBountyBalance);
						let _ = T::Currency::reserve(&bounty_account, value);

						bounty.subbountycount += 1;
						match bounty.activesubbounty.binary_search_by_key(&bounty.subbountycount, |x| *x) {
							Ok(_) => {
								//This should not occur
							},
							Err(i) => bounty.activesubbounty.insert(i, bounty.subbountycount),
						}
						Self::create_subbounty(&signer,
							bounty_id,
							bounty.subbountycount,
							description,
							value
						)?;
					},
					_ => return Err(Error::<T>::UnexpectedStatus.into()),
				}
				Ok(())
			})?;
		}

		/// Assign subcurator for funded subbounty.
		///
		/// The dispatch origin for this call must be curator.
		/// Bounty must me in "active" state.
		///
		/// Proposed subcurator may be "curator", in this case
		/// payment fee is considered as Zero.
		///
		/// Bounty must be active, for this subbounty call to work.
		///
		/// - `bounty_id`: ID pair Bounty ID.
		/// - `subbounty_id`: ID pair SubBounty ID to cancel.
		/// - `subcurator`: Address of subcurator.
		/// - `fee`: payment fee to subcurator for execution.
		#[weight = 10_000]
		fn propose_subcurator(
			origin,
			#[compact] bounty_id: BountyIndex,
			#[compact] subbounty_id: BountyIndex,
			subcurator: <T::Lookup as StaticLookup>::Source,
			#[compact] fee: BalanceOf<T>,
		) {
			let signer = ensure_signed(origin)?;
			let subcurator = T::Lookup::lookup(subcurator)?;

			// Ensure parent bounty is Active
			Self::ensure_bounty_active(bounty_id)?;

			// Mutate the Subbounty instance
			SubBounties::<T>::try_mutate_exists(bounty_id,
				subbounty_id,
				|maybe_subbounty| -> DispatchResult {

				let mut subbounty = maybe_subbounty
					.as_mut()
					.ok_or(Error::<T>::InvalidIndex)?;

				// Ensure sure caller is curator
				let master_curator = &subbounty.curator;
				ensure!( signer == *master_curator, Error::<T>::RequireCurator);

				// Ensure subbounty is in expected state
				match subbounty.status {
					BountyStatus::Proposed | BountyStatus::Approved | BountyStatus::Funded => {},
					_ => return Err(Error::<T>::UnexpectedStatus.into()),
				};

				// if curator self assign as subcurator, fee is 0
				if *master_curator != subcurator {
					ensure!(fee < subbounty.value, Error::<T>::InvalidFee);
					subbounty.fee = fee;
				} else {
					subbounty.fee = Zero::zero();
				}
				// update the subbounty state
				subbounty.status = BountyStatus::CuratorProposed {
					curator: subcurator
				};
				Ok(())
			})?;
		}

		/// Accept the subcurator role for subbounty.
		///
		/// A deposit will be reserved from curator and refund upon
		/// successful payout. In case if "curator" is "subcurator",
		/// deposit is not reserved.
		///
		/// Bounty must be active, for this subbounty call to work.
		///
		/// May only be called from the curator/proposed subcurator.
		///
		/// - `bounty_id`: ID pair Bounty ID.
		/// - `subbounty_id`: ID pair SubBounty ID to cancel.
		#[weight = 10_000]
		fn accept_subcurator(origin,
			#[compact] bounty_id: BountyIndex,
			#[compact] subbounty_id: BountyIndex,
		) {
			let signer = ensure_signed(origin)?;

			// Ensure parent bounty is Active
			Self::ensure_bounty_active(bounty_id)?;

			// Mutate Subbounty
			SubBounties::<T>::try_mutate_exists(bounty_id, subbounty_id,
				|maybe_subbounty| -> DispatchResult {

				let mut subbounty = maybe_subbounty
					.as_mut()
					.ok_or(Error::<T>::InvalidIndex)?;

				let master_curator = &subbounty.curator;

				// Ensure subbounty is in expected state
				match subbounty.status {
					BountyStatus::CuratorProposed { ref curator } => {
						let subcurator = curator;
						ensure!(signer == *subcurator, Error::<T>::RequireCurator);
						// TODO :: Have to recheck this condition
						// Deposit the bond if subcurator is not equal to curator
						if *master_curator != *subcurator {
							let deposit = T::BountyCuratorDeposit::get() * subbounty.fee;
							T::Currency::reserve(subcurator, deposit)?;
							subbounty.curator_deposit = deposit;
						} else {
							subbounty.curator_deposit = Zero::zero();
						}
						// TODO :: Have to recheck this config, do we need trait cfg like SubBountyUpdatePeriod ?
						let update_due = system::Module::<T>::block_number() +
							T::BountyUpdatePeriod::get();
						subbounty.status = BountyStatus::Active {
							curator: subcurator.clone(),
							update_due,
						};
					},
					_ => return Err(Error::<T>::UnexpectedStatus.into()),
				};
				Ok(())
			})?;
		}

		/// Unassign subcurator from a subbounty.
		///
		/// This function can only be called by the
		/// `RejectOrigin` a signed origin.
		///
		/// Bounty must be active, for this subbounty call to work.
		///
		/// If this function is called by the `RejectOrigin`, we assume that
		/// the curator is malicious or inactive. As a result,
		/// we will slash the curator when possible.
		///
		/// If the origin is the curator, we take this as a sign they are
		/// unable to do their job and they willingly give up.
		/// We could slash them, but for now we allow them to recover their
		/// deposit and exit without issue. (We may want to change this
		/// if it is abused.)
		///
		/// Finally, the origin can be anyone if and only if the curator
		/// is "inactive". This allows anyone in the community to call out
		/// that a curator is not doing their due diligence, and
		/// we should pick a new curator. In this case the curator
		/// should also be slashed.
		///
		/// - `bounty_id`: ID pair Bounty ID.
		/// - `subbounty_id`: ID pair SubBounty ID to cancel.
		#[weight = 10_000]
		fn unassign_subcurator(
			origin,
			#[compact] bounty_id: BountyIndex,
			#[compact] subbounty_id: BountyIndex,
		) {
			let maybe_sender = ensure_signed(origin.clone())
				.map(Some)
				.or_else(|_| T::RejectOrigin::ensure_origin(origin).map(|_| None))?;

			// Ensure parent bounty is Active
			Self::ensure_bounty_active(bounty_id)?;

			// Ensure subbounty is in expected state
			SubBounties::<T>::try_mutate_exists(bounty_id,
				subbounty_id,
				|maybe_subbounty| -> DispatchResult {

				let mut subbounty = maybe_subbounty
					.as_mut()
					.ok_or(Error::<T>::InvalidIndex)?;

				let master_curator = &subbounty.curator;

				let slash_curator = |arg_curator: &T::AccountId, curator_deposit: &mut BalanceOf<T>| {
					let imbalance = T::Currency::slash_reserved(arg_curator, *curator_deposit).0;
					T::OnSlash::on_unbalanced(imbalance);
					*curator_deposit = Zero::zero();
				};

				match subbounty.status {
					BountyStatus::Proposed | BountyStatus::Approved | BountyStatus::Funded => {
						// No curator to unassign at this point.
						return Err(Error::<T>::UnexpectedStatus.into())
					}
					BountyStatus::CuratorProposed { ref curator } => {
						let subcurator = curator;
						// A curator has been proposed, but not accepted yet.
						// Either `RejectOrigin`, curator or the proposed subcurator can unassign the subcurator.
						ensure!(maybe_sender
							.map_or(true, |sender| sender == *subcurator || sender == *master_curator),
							BadOrigin
						);
					},
					BountyStatus::Active { ref curator, ref update_due } => {
						let subcurator = curator;
						// The bounty is active.
						match maybe_sender {
							// If the `RejectOrigin` is calling this function, slash the curator.
							None => {
								slash_curator(subcurator, &mut subbounty.curator_deposit);
								// Continue to change bounty status below...
							},
							Some(sender) => {
								// If the sender is curator, and the subcurator is inactive,
								// slash the subcurator.
								if sender == *master_curator {
									let block_number = system::Module::<T>::block_number();
									if *update_due < block_number {
										slash_curator(subcurator, &mut subbounty.curator_deposit);
										// Continue to change bounty status below...
									} else {
										// Curator has more time to give an update.
										return Err(Error::<T>::Premature.into())
									}
								} else {
									// Else this is the subcurator, willingly giving up their role.
									// Give back their deposit.
									let _ = T::Currency::unreserve(&subcurator, subbounty.curator_deposit);
									// Continue to change bounty status below...
								}
							},
						}
					},
					BountyStatus::PendingPayout { ref curator, .. } => {
						let ref subcurator = curator;
						// TODO :: Have to review the condition again
						// The bounty is pending payout, so only council can unassign a subcurator.
						// By doing so, they are claiming the subcurator is acting maliciously, so
						// we slash the subcurator.
						ensure!(maybe_sender.is_none(), BadOrigin);
						slash_curator(subcurator, &mut subbounty.curator_deposit);
						// Continue to change bounty status below...
					},
				};
				// Move the subbounty state to Funded.
				subbounty.status = BountyStatus::Funded;
				Ok(())
			})?;
		}

		/// Award subbounty to a beneficiary account.
		/// The beneficiary will be able to claim the
		/// funds after a delay.
		///
		/// The dispatch origin for this call must be
		/// the curator or subcurator of this subbounty.
		///
		/// Bounty must be active, for this subbounty call to work.
		///
		/// - `bounty_id`: ID pair Bounty ID.
		/// - `subbounty_id`: ID pair SubBounty ID to cancel.
		/// - `beneficiary`: Beneficiary account.
		#[weight = 10_000]
		fn award_subbounty(origin,
			#[compact] bounty_id: BountyIndex,
			#[compact] subbounty_id: BountyIndex,
			beneficiary: <T::Lookup as StaticLookup>::Source
		) {
			let signer = ensure_signed(origin)?;
			let beneficiary = T::Lookup::lookup(beneficiary)?;

			// Ensure parent bounty is Active
			Self::ensure_bounty_active(bounty_id)?;

			// Ensure subbounty is in expected state
			SubBounties::<T>::try_mutate_exists(bounty_id,
				subbounty_id,
				|maybe_subbounty| -> DispatchResult {

				let mut subbounty = maybe_subbounty
					.as_mut()
					.ok_or(Error::<T>::InvalidIndex)?;

				// Ensure Subbounty is in active state
				match &subbounty.status {
					BountyStatus::Active {
						curator,
						..
					} => {
						ensure!(signer == *curator, Error::<T>::RequireCurator);
					},
					_ => return Err(Error::<T>::UnexpectedStatus.into()),
				}

				// Move the subbounty state to Pending payout.
				subbounty.status = BountyStatus::PendingPayout {
					curator: signer,
					beneficiary: beneficiary.clone(),
					unlock_at: system::Module::<T>::block_number() + T::BountyDepositPayoutDelay::get(),
				};

				Ok(())
			})?;

			Self::deposit_event(Event::<T>::SubBountyAwarded(bounty_id, subbounty_id, beneficiary));
		}

		/// Claim the payout from an awarded subbounty after payout delay.
		///
		/// The dispatch origin for this call must be the beneficiary
		/// of this subbounty.
		///
		/// Bounty must be active, for this subbounty call to work.
		///
		/// - `bounty_id`: ID pair Bounty ID.
		/// - `subbounty_id`: ID pair SubBounty ID to cancel.
		#[weight = 10_000]
		fn claim_subbounty(origin,
			#[compact] bounty_id: BountyIndex,
			#[compact] subbounty_id: BountyIndex,
		) {
			let _ = ensure_signed(origin)?;

			// Ensure parent bounty is Active
			Self::ensure_bounty_active(bounty_id)?;

			// Ensure subbounty is in expected state
			SubBounties::<T>::try_mutate_exists(bounty_id,
				subbounty_id,
				|maybe_subbounty| -> DispatchResult {

				let subbounty = maybe_subbounty
					.as_mut()
					.ok_or(Error::<T>::InvalidIndex)?;

				let master_curator = &subbounty.curator;

				if let BountyStatus::PendingPayout { ref curator, ref beneficiary, ref unlock_at } = subbounty.status {
					let subcurator = curator;

					ensure!(system::Module::<T>::block_number() >= *unlock_at, Error::<T>::Premature);

					let bounty_account = Self::bounty_account_id(bounty_id);

					// Make curator fee payment & unreserve the deposit
					// if subcurator != curator
					if *subcurator != *master_curator {
						let _ = T::Currency::unreserve(&subcurator, subbounty.curator_deposit);
						let _ = T::Currency::repatriate_reserved(
							&bounty_account,
							&subcurator,
							subbounty.fee,
							Status::Free,
						);
					}
					// Make payout to beneficiary
					let payout = subbounty.value.saturating_sub(subbounty.fee);
					let _ = T::Currency::repatriate_reserved(
						&bounty_account,
						beneficiary,
						payout,
						Status::Free,
					);
					Self::deposit_event(Event::<T>::SubBountyClaimed(bounty_id,
						subbounty_id,
						payout,
						beneficiary.clone(),
					));

					// Remove the subbounty description
					SubBountyDescriptions::remove(bounty_id, subbounty_id);
					// Remove the subbounty from bounty active subbouty list
					Bounties::<T>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
						let bounty = maybe_bounty.as_mut().ok_or(Error::<T>::InvalidIndex)?;
						bounty.activesubbounty.retain(|h| h != &subbounty_id);
						Ok(())
					})?;
					*maybe_subbounty = None;
					Ok(())
				} else {
					Err(Error::<T>::UnexpectedStatus.into())
				}
			})?;
		}

		/// Cancel a proposed or active subbounty. All the funds gets
		/// unreserved to bounty account. the curator deposit will
		/// be unreserved if possible.
		///
		/// Only `T::RejectOrigin` or `curator` is able to cancel a bounty.
		///
		/// Bounty must be active, for this subbounty call to work.
		///
		/// - `bounty_id`: ID pair Bounty ID.
		/// - `subbounty_id`: ID pair SubBounty ID to cancel.
		#[weight = 10_000]
		fn close_subbounty(origin,
			#[compact] bounty_id: BountyIndex,
			#[compact] subbounty_id: BountyIndex,
		) -> DispatchResultWithPostInfo {
			// TODO :: Have to recheck this requirement
			let _signer = ensure_signed(origin)?;

			// Ensure parent bounty is Active
			Self::ensure_bounty_active(bounty_id)?;

			Self::impl_close_subbounty(bounty_id, subbounty_id)?;

			Ok(Some(<T as Config>::WeightInfo::close_bounty_active()).into())
		}

		/// Extend the expiry time of an active subbounty.
		///
		/// The dispatch origin for this call must be the curator or
		/// subcurator of this subbounty.
		///
		/// Bounty must be active, for this subbounty call to work.
		///
		/// - `bounty_id`: ID pair Bounty ID.
		/// - `subbounty_id`: ID pair SubBounty ID to cancel.
		/// - `remark`: reason for extending( reserved & not used),
		#[weight = 10_000]
		fn extend_subbounty_expiry(origin,
			#[compact] bounty_id: BountyIndex,
			#[compact] subbounty_id: BountyIndex,
			remark: Vec<u8>
		) {
			let signer = ensure_signed(origin)?;

			// Ensure parent bounty is Active
			Self::ensure_bounty_active(bounty_id)?;

			Self::impl_extend_subbounty_expiry(&signer, bounty_id, subbounty_id, remark)?;
		}
	}
}

impl<T: Config> Module<T> {
	// Add public immutables and private mutables.

	/// The account ID of the treasury pot.
	///
	/// This actually does computation. If you need to keep using it, then make sure you cache the
	/// value and only call this once.
	pub fn account_id() -> T::AccountId {
		T::ModuleId::get().into_account()
	}

	/// The account ID of a bounty account
	pub fn bounty_account_id(id: BountyIndex) -> T::AccountId {
		// only use two byte prefix to support 16 byte account id (used by test)
		// "modl" ++ "py/trsry" ++ "bt" is 14 bytes, and two bytes remaining for bounty index
		T::ModuleId::get().into_sub_account(("bt", id))
	}

	fn create_bounty(
		proposer: T::AccountId,
		description: Vec<u8>,
		value: BalanceOf<T>,
	) -> DispatchResult {
		ensure!(description.len() <= T::MaximumReasonLength::get() as usize, Error::<T>::ReasonTooBig);
		ensure!(value >= T::BountyValueMinimum::get(), Error::<T>::InvalidValue);

		let index = Self::bounty_count();

		// reserve deposit for new bounty
		let bond = T::BountyDepositBase::get()
			+ T::DataDepositPerByte::get() * (description.len() as u32).into();
		T::Currency::reserve(&proposer, bond)
			.map_err(|_| Error::<T>::InsufficientProposersBalance)?;

		BountyCount::put(index + 1);

		let bounty = Bounty {
			proposer,
			value,
			fee: 0u32.into(),
			curator_deposit: 0u32.into(),
			bond,
			status: BountyStatus::Proposed,
			subbountycount: 0u32.into(),
			activesubbounty: Default::default(),
		};

		Bounties::<T>::insert(index, &bounty);
		BountyDescriptions::insert(index, description);

		Self::deposit_event(RawEvent::BountyProposed(index));

		Ok(())
	}

	fn ensure_bounty_active(
		bounty_id: BountyIndex,
	) -> DispatchResult {
		let bounty = Self::bounties(&bounty_id).ok_or(Error::<T>::InvalidIndex)?;
		if let BountyStatus::Active { curator: _ , .. } = bounty.status {
			Ok(())
		} else {
			Err(Error::<T>::UnexpectedStatus.into())
		}
	}

	fn create_subbounty(
		proposer: &T::AccountId,
		bounty_id: BountyIndex,
		subbounty_id: BountyIndex,
		description: Vec<u8>,
		value: BalanceOf<T>,
	) -> DispatchResult {

		let bond = T::BountyDepositBase::get()
			+ T::DataDepositPerByte::get() * (description.len() as u32).into();

		let subbounty = SubBounty {
			proposer: proposer.clone(),
			value,
			fee: 0u32.into(),
			curator: proposer.clone(),
			curator_deposit: 0u32.into(),
			bond,
			status: BountyStatus::Approved,
		};

		SubBounties::<T>::insert(bounty_id, subbounty_id, &subbounty);
		SubBountyDescriptions::insert(bounty_id, subbounty_id, description);
		Self::deposit_event(RawEvent::SubBountyApproved(bounty_id, subbounty_id));
		Ok(())
	}

	fn impl_close_subbounty(
		bounty_id: BountyIndex,
		subbounty_id: BountyIndex,
	) -> DispatchResult {
		SubBounties::<T>::try_mutate_exists(bounty_id, subbounty_id,
			|maybe_subbounty| -> DispatchResult {

			let subbounty = maybe_subbounty
				.as_mut()
				.ok_or(Error::<T>::InvalidIndex)?;

			match &subbounty.status {
				BountyStatus::Proposed |
				BountyStatus::Approved => {
					// Slash the proposer.
					let value = subbounty.bond;
					let imbalance = T::Currency::slash_reserved(&subbounty.proposer, value).0;
					T::OnSlash::on_unbalanced(imbalance);
				},
				BountyStatus::Funded |
				BountyStatus::CuratorProposed { .. } => {
					// Nothing extra to do besides the removal of the bounty below.
				},
				BountyStatus::Active { curator, .. } => {
					// Cancelled by council, refund deposit of the working curator.
					let _ = T::Currency::unreserve(&curator, subbounty.curator_deposit);
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
			// Unlock the fund reserved for subbounty
			let bounty_account = Self::bounty_account_id(bounty_id);
			let _ = T::Currency::unreserve(&bounty_account, subbounty.value);

			*maybe_subbounty = None;
			Self::deposit_event(Event::<T>::SubBountyCanceled(bounty_id, subbounty_id));
			Ok(())
		})
	}

	fn impl_extend_subbounty_expiry(
		signer: &T::AccountId,
		bounty_id: BountyIndex,
		subbounty_id: BountyIndex,
		_remark: Vec<u8>
	) -> DispatchResult {

		SubBounties::<T>::try_mutate_exists(bounty_id, subbounty_id,
			|maybe_subbounty| -> DispatchResult {

			let subbounty = maybe_subbounty
				.as_mut()
				.ok_or(Error::<T>::InvalidIndex)?;

			match subbounty.status {
				BountyStatus::Active { ref curator, ref mut update_due } => {
					ensure!(*curator == *signer || subbounty.curator == *signer, Error::<T>::RequireCurator);
					*update_due = (system::Module::<T>::block_number() + T::BountyUpdatePeriod::get()).max(*update_due);
				},
				_ => return Err(Error::<T>::UnexpectedStatus.into()),
			}
			Self::deposit_event(Event::<T>::SubBountyExtended(bounty_id, subbounty_id));
			Ok(())
		})
	}
}

impl<T: Config> pallet_treasury::SpendFunds<T> for Module<T> {
	fn spend_funds(
		budget_remaining: &mut BalanceOf<T>,
		imbalance: &mut PositiveImbalanceOf<T>,
		total_weight: &mut Weight,
		missed_any: &mut bool
	) {
		let bounties_len = BountyApprovals::mutate(|v| {
			let bounties_approval_len = v.len() as u32;
			v.retain(|&index| {
				Bounties::<T>::mutate(index, |bounty| {
					// Should always be true, but shouldn't panic if false or we're screwed.
					if let Some(bounty) = bounty {
						if bounty.value <= *budget_remaining {
							*budget_remaining -= bounty.value;

							bounty.status = BountyStatus::Funded;

							// return their deposit.
							let _ = T::Currency::unreserve(&bounty.proposer, bounty.bond);

							// fund the bounty account
							imbalance.subsume(T::Currency::deposit_creating(&Self::bounty_account_id(index), bounty.value));

							Self::deposit_event(RawEvent::BountyBecameActive(index));
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

		// Process the Subbounties approval.
		let subbounties_len = SubBountyApprovals::mutate(|v| {
			let subbounties_approval_len = v.len() as u32;
			v.iter().for_each(|(bounty_id, subbounty_id)| {
				let _ = SubBounties::<T>::try_mutate_exists(bounty_id, subbounty_id,
					|maybe_subbounty| -> DispatchResult {
						let mut subbounty = maybe_subbounty.as_mut().unwrap();
						subbounty.status = BountyStatus::Funded;
						// return the proposer deposit.
						let _ = T::Currency::unreserve(&subbounty.proposer, subbounty.bond);
						Self::deposit_event(RawEvent::SubBountyBecameActive(*bounty_id,*subbounty_id));
						Ok(())
					}
				);
			});
			subbounties_approval_len
		});
		*total_weight += <T as Config>::WeightInfo::spend_funds(bounties_len + subbounties_len);
	}
}
