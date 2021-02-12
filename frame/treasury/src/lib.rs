// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! # Treasury Module
//!
//! The Treasury module provides a "pot" of funds that can be managed by stakeholders in the
//! system and a structure for making spending proposals from this pot.
//!
//! - [`treasury::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//!
//! ## Overview
//!
//! The Treasury Module itself provides the pot to store funds, and a means for stakeholders to
//! propose, approve, and deny expenditures. The chain will need to provide a method (e.g.
//! inflation, fees) for collecting funds.
//!
//! By way of example, the Council could vote to fund the Treasury with a portion of the block
//! reward and use the funds to pay developers.
//!
//! ### Tipping
//!
//! A separate subsystem exists to allow for an agile "tipping" process, whereby a reward may be
//! given without first having a pre-determined stakeholder group come to consensus on how much
//! should be paid.
//!
//! A group of `Tippers` is determined through the config `Trait`. After half of these have declared
//! some amount that they believe a particular reported reason deserves, then a countdown period is
//! entered where any remaining members can declare their tip amounts also. After the close of the
//! countdown period, the median of all declared tips is paid to the reported beneficiary, along
//! with any finders fee, in case of a public (and bonded) original report.
//!
//! ### Bounty
//!
//! A Bounty Spending is a reward for a specified body of work - or specified set of objectives - that
//! needs to be executed for a predefined Treasury amount to be paid out. A curator is assigned after
//! the bounty is approved and funded by Council, to be delegated
//! with the responsibility of assigning a payout address once the specified set of objectives is completed.
//!
//! After the Council has activated a bounty, it delegates the work that requires expertise to a curator
//! in exchange of a deposit. Once the curator accepts the bounty, they
//! get to close the Active bounty. Closing the Active bounty enacts a delayed payout to the payout
//! address, the curator fee and the return of the curator deposit. The
//! delay allows for intervention through regular democracy. The Council gets to unassign the curator,
//! resulting in a new curator election. The Council also gets to cancel
//! the bounty if deemed necessary before assigning a curator or once the bounty is active or payout
//! is pending, resulting in the slash of the curator's deposit.
//!
//!
//! ### Terminology
//!
//! - **Proposal:** A suggestion to allocate funds from the pot to a beneficiary.
//! - **Beneficiary:** An account who will receive the funds from a proposal iff
//! the proposal is approved.
//! - **Deposit:** Funds that a proposer must lock when making a proposal. The
//! deposit will be returned or slashed if the proposal is approved or rejected
//! respectively.
//! - **Pot:** Unspent funds accumulated by the treasury module.
//!
//! Tipping protocol:
//! - **Tipping:** The process of gathering declarations of amounts to tip and taking the median
//!   amount to be transferred from the treasury to a beneficiary account.
//! - **Tip Reason:** The reason for a tip; generally a URL which embodies or explains why a
//!   particular individual (identified by an account ID) is worthy of a recognition by the
//!   treasury.
//! - **Finder:** The original public reporter of some reason for tipping.
//! - **Finders Fee:** Some proportion of the tip amount that is paid to the reporter of the tip,
//!   rather than the main beneficiary.
//!
//! Bounty:
//! - **Bounty spending proposal:** A proposal to reward a predefined body of work upon completion by
//! the Treasury.
//! - **Proposer:** An account proposing a bounty spending.
//! - **Curator:** An account managing the bounty and assigning a payout address receiving the reward
//! for the completion of work.
//! - **Deposit:** The amount held on deposit for placing a bounty proposal plus the amount held on
//! deposit per byte within the bounty description.
//! - **Curator deposit:** The payment from a candidate willing to curate an approved bounty. The deposit
//! is returned when/if the bounty is completed.
//! - **Bounty value:** The total amount that should be paid to the Payout Address if the bounty is
//! rewarded.
//! - **Payout address:** The account to which the total or part of the bounty is assigned to.
//! - **Payout Delay:** The delay period for which a bounty beneficiary needs to wait before claiming.
//! - **Curator fee:** The reserved upfront payment for a curator for work related to the bounty.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! General spending/proposal protocol:
//! - `propose_spend` - Make a spending proposal and stake the required deposit.
//! - `set_pot` - Set the spendable balance of funds.
//! - `configure` - Configure the module's proposal requirements.
//! - `reject_proposal` - Reject a proposal, slashing the deposit.
//! - `approve_proposal` - Accept the proposal, returning the deposit.
//!
//! Tipping protocol:
//! - `report_awesome` - Report something worthy of a tip and register for a finders fee.
//! - `retract_tip` - Retract a previous (finders fee registered) report.
//! - `tip_new` - Report an item worthy of a tip and declare a specific amount to tip.
//! - `tip` - Declare or redeclare an amount to tip for a particular reason.
//! - `close_tip` - Close and pay out a tip.
//!
//! Bounty protocol:
//! - `propose_bounty` - Propose a specific treasury amount to be earmarked for a predefined set of
//! tasks and stake the required deposit.
//! - `approve_bounty` - Accept a specific treasury amount to be earmarked for a predefined body of work.
//! - `propose_curator` - Assign an account to a bounty as candidate curator.
//! - `accept_curator` - Accept a bounty assignment from the Council, setting a curator deposit.
//! - `extend_bounty_expiry` - Extend the expiry block number of the bounty and stay active.
//! - `award_bounty` - Close and pay out the specified amount for the completed work.
//! - `claim_bounty` - Claim a specific bounty amount from the Payout Address.
//! - `unassign_curator` - Unassign an accepted curator from a specific earmark.
//! - `close_bounty` - Cancel the earmark for a specific treasury amount and close the bounty.
//!
//!
//! ## GenesisConfig
//!
//! The Treasury module depends on the [`GenesisConfig`](./struct.GenesisConfig.html).

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
use sp_std::prelude::*;
use frame_support::{decl_module, decl_storage, decl_event, ensure, print, decl_error, Parameter};
use frame_support::traits::{
	Currency, Get, Imbalance, OnUnbalanced, ExistenceRequirement::{KeepAlive, AllowDeath},
	ReservableCurrency, WithdrawReason
};
use sp_runtime::{Permill, ModuleId, Percent, RuntimeDebug, DispatchResult, traits::{
	Zero, StaticLookup, AccountIdConversion, Saturating, Hash, BadOrigin
}};
use frame_support::dispatch::DispatchResultWithPostInfo;
use frame_support::weights::{Weight, DispatchClass};
use frame_support::traits::{Contains, ContainsLengthBound, EnsureOrigin};
use codec::{Encode, Decode};
use frame_system::{self as system, ensure_signed};

mod tests;
mod benchmarking;
mod default_weights;

type BalanceOf<T, I> =
	<<T as Trait<I>>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
type PositiveImbalanceOf<T, I> =
	<<T as Trait<I>>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::PositiveImbalance;
type NegativeImbalanceOf<T, I> =
	<<T as Trait<I>>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::NegativeImbalance;

pub trait WeightInfo {
	fn propose_spend() -> Weight;
	fn reject_proposal() -> Weight;
	fn approve_proposal() -> Weight;
	fn report_awesome(r: u32, ) -> Weight;
	fn retract_tip() -> Weight;
	fn tip_new(r: u32, t: u32, ) -> Weight;
	fn tip(t: u32, ) -> Weight;
	fn close_tip(t: u32, ) -> Weight;
	fn propose_bounty(r: u32, ) -> Weight;
	fn approve_bounty() -> Weight;
	fn propose_curator() -> Weight;
	fn unassign_curator() -> Weight;
	fn accept_curator() -> Weight;
	fn award_bounty() -> Weight;
	fn claim_bounty() -> Weight;
	fn close_bounty_proposed() -> Weight;
	fn close_bounty_active() -> Weight;
	fn extend_bounty_expiry() -> Weight;
	fn on_initialize_proposals(p: u32, ) -> Weight;
	fn on_initialize_bounties(b: u32, ) -> Weight;
}

pub trait Trait<I=DefaultInstance>: frame_system::Trait {
	/// The treasury's module id, used for deriving its sovereign account ID.
	type ModuleId: Get<ModuleId>;

	/// The staking balance.
	type Currency: Currency<Self::AccountId> + ReservableCurrency<Self::AccountId>;

	/// Origin from which approvals must come.
	type ApproveOrigin: EnsureOrigin<Self::Origin>;

	/// Origin from which rejections must come.
	type RejectOrigin: EnsureOrigin<Self::Origin>;

	/// Origin from which tippers must come.
	///
	/// `ContainsLengthBound::max_len` must be cost free (i.e. no storage read or heavy operation).
	type Tippers: Contains<Self::AccountId> + ContainsLengthBound;

	/// The period for which a tip remains open after is has achieved threshold tippers.
	type TipCountdown: Get<Self::BlockNumber>;

	/// The percent of the final tip which goes to the original reporter of the tip.
	type TipFindersFee: Get<Percent>;

	/// The amount held on deposit for placing a tip report.
	type TipReportDepositBase: Get<BalanceOf<Self, I>>;

	/// The amount held on deposit per byte within the tip report reason or bounty description.
	type DataDepositPerByte: Get<BalanceOf<Self, I>>;

	/// The overarching event type.
	type Event: From<Event<Self, I>> + Into<<Self as frame_system::Trait>::Event>;

	/// Handler for the unbalanced decrease when slashing for a rejected proposal or bounty.
	type OnSlash: OnUnbalanced<NegativeImbalanceOf<Self, I>>;

	/// Fraction of a proposal's value that should be bonded in order to place the proposal.
	/// An accepted proposal gets these back. A rejected proposal does not.
	type ProposalBond: Get<Permill>;

	/// Minimum amount of funds that should be placed in a deposit for making a proposal.
	type ProposalBondMinimum: Get<BalanceOf<Self, I>>;

	/// Period between successive spends.
	type SpendPeriod: Get<Self::BlockNumber>;

	/// Percentage of spare funds (if any) that are burnt per spend period.
	type Burn: Get<Permill>;

	/// The amount held on deposit for placing a bounty proposal.
	type BountyDepositBase: Get<BalanceOf<Self, I>>;

	/// The delay period for which a bounty beneficiary need to wait before claim the payout.
	type BountyDepositPayoutDelay: Get<Self::BlockNumber>;

	/// Bounty duration in blocks.
	type BountyUpdatePeriod: Get<Self::BlockNumber>;

	/// Percentage of the curator fee that will be reserved upfront as deposit for bounty curator.
	type BountyCuratorDeposit: Get<Permill>;

	/// Minimum value for a bounty.
	type BountyValueMinimum: Get<BalanceOf<Self, I>>;

	/// Maximum acceptable reason length.
	type MaximumReasonLength: Get<u32>;

	/// Handler for the unbalanced decrease when treasury funds are burned.
	type BurnDestination: OnUnbalanced<NegativeImbalanceOf<Self, I>>;

	/// Weight information for extrinsics in this pallet.
	type WeightInfo: WeightInfo;
}

/// An index of a proposal. Just a `u32`.
pub type ProposalIndex = u32;

/// A spending proposal.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
pub struct Proposal<AccountId, Balance> {
	/// The account proposing it.
	proposer: AccountId,
	/// The (total) amount that should be paid if the proposal is accepted.
	value: Balance,
	/// The account to whom the payment should be made if the proposal is accepted.
	beneficiary: AccountId,
	/// The amount held on deposit (reserved) for making this proposal.
	bond: Balance,
}

/// An open tipping "motion". Retains all details of a tip including information on the finder
/// and the members who have voted.
#[derive(Clone, Eq, PartialEq, Encode, Decode, RuntimeDebug)]
pub struct OpenTip<
	AccountId: Parameter,
	Balance: Parameter,
	BlockNumber: Parameter,
	Hash: Parameter,
> {
	/// The hash of the reason for the tip. The reason should be a human-readable UTF-8 encoded string. A URL would be
	/// sensible.
	reason: Hash,
	/// The account to be tipped.
	who: AccountId,
	/// The account who began this tip.
	finder: AccountId,
	/// The amount held on deposit for this tip.
	deposit: Balance,
	/// The block number at which this tip will close if `Some`. If `None`, then no closing is
	/// scheduled.
	closes: Option<BlockNumber>,
	/// The members who have voted for this tip. Sorted by AccountId.
	tips: Vec<(AccountId, Balance)>,
	/// Whether this tip should result in the finder taking a fee.
	finders_fee: bool,
}

/// An index of a bounty. Just a `u32`.
pub type BountyIndex = u32;

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

decl_storage! {
	trait Store for Module<T: Trait<I>, I: Instance=DefaultInstance> as Treasury {
		/// Number of proposals that have been made.
		ProposalCount get(fn proposal_count): ProposalIndex;

		/// Proposals that have been made.
		Proposals get(fn proposals):
			map hasher(twox_64_concat) ProposalIndex
			=> Option<Proposal<T::AccountId, BalanceOf<T, I>>>;

		/// Proposal indices that have been approved but not yet awarded.
		Approvals get(fn approvals): Vec<ProposalIndex>;

		/// Tips that are not yet completed. Keyed by the hash of `(reason, who)` from the value.
		/// This has the insecure enumerable hash function since the key itself is already
		/// guaranteed to be a secure hash.
		pub Tips get(fn tips):
			map hasher(twox_64_concat) T::Hash
			=> Option<OpenTip<T::AccountId, BalanceOf<T, I>, T::BlockNumber, T::Hash>>;

		/// Simple preimage lookup from the reason's hash to the original data. Again, has an
		/// insecure enumerable hash since the key is guaranteed to be the result of a secure hash.
		pub Reasons get(fn reasons): map hasher(identity) T::Hash => Option<Vec<u8>>;

		/// Number of bounty proposals that have been made.
		pub BountyCount get(fn bounty_count): BountyIndex;

		/// Bounties that have been made.
		pub Bounties get(fn bounties):
			map hasher(twox_64_concat) BountyIndex
			=> Option<Bounty<T::AccountId, BalanceOf<T, I>, T::BlockNumber>>;

		/// The description of each bounty.
		pub BountyDescriptions get(fn bounty_descriptions): map hasher(twox_64_concat) BountyIndex => Option<Vec<u8>>;

		/// Bounty indices that have been approved but not yet funded.
		pub BountyApprovals get(fn bounty_approvals): Vec<BountyIndex>;
	}
	add_extra_genesis {
		build(|_config| {
			// Create Treasury account
			let _ = T::Currency::make_free_balance_be(
				&<Module<T, I>>::account_id(),
				T::Currency::minimum_balance(),
			);
		});
	}
}

decl_event!(
	pub enum Event<T, I=DefaultInstance>
	where
		Balance = BalanceOf<T, I>,
		<T as frame_system::Trait>::AccountId,
		<T as frame_system::Trait>::Hash,
	{
		/// New proposal. \[proposal_index\]
		Proposed(ProposalIndex),
		/// We have ended a spend period and will now allocate funds. \[budget_remaining\]
		Spending(Balance),
		/// Some funds have been allocated. \[proposal_index, award, beneficiary\]
		Awarded(ProposalIndex, Balance, AccountId),
		/// A proposal was rejected; funds were slashed. \[proposal_index, slashed\]
		Rejected(ProposalIndex, Balance),
		/// Some of our funds have been burnt. \[burn\]
		Burnt(Balance),
		/// Spending has finished; this is the amount that rolls over until next spend.
		/// \[budget_remaining\]
		Rollover(Balance),
		/// Some funds have been deposited. \[deposit\]
		Deposit(Balance),
		/// A new tip suggestion has been opened. \[tip_hash\]
		NewTip(Hash),
		/// A tip suggestion has reached threshold and is closing. \[tip_hash\]
		TipClosing(Hash),
		/// A tip suggestion has been closed. \[tip_hash, who, payout\]
		TipClosed(Hash, AccountId, Balance),
		/// A tip suggestion has been retracted. \[tip_hash\]
		TipRetracted(Hash),
		/// New bounty proposal. [index]
		BountyProposed(BountyIndex),
		/// A bounty proposal was rejected; funds were slashed. [index, bond]
		BountyRejected(BountyIndex, Balance),
		/// A bounty proposal is funded and became active. [index]
		BountyBecameActive(BountyIndex),
		/// A bounty is awarded to a beneficiary. [index, beneficiary]
		BountyAwarded(BountyIndex, AccountId),
		/// A bounty is claimed by beneficiary. [index, payout, beneficiary]
		BountyClaimed(BountyIndex, Balance, AccountId),
		/// A bounty is cancelled. [index]
		BountyCanceled(BountyIndex),
		/// A bounty expiry is extended. [index]
		BountyExtended(BountyIndex),
	}
);

decl_error! {
	/// Error for the treasury module.
	pub enum Error for Module<T: Trait<I>, I: Instance> {
		/// Proposer's balance is too low.
		InsufficientProposersBalance,
		/// No proposal or bounty at that index.
		InvalidIndex,
		/// The reason given is just too big.
		ReasonTooBig,
		/// The tip was already found/started.
		AlreadyKnown,
		/// The tip hash is unknown.
		UnknownTip,
		/// The account attempting to retract the tip is not the finder of the tip.
		NotFinder,
		/// The tip cannot be claimed/closed because there are not enough tippers yet.
		StillOpen,
		/// The tip cannot be claimed/closed because it's still in the countdown period.
		Premature,
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
	}
}

decl_module! {
	pub struct Module<T: Trait<I>, I: Instance=DefaultInstance>
		for enum Call
		where origin: T::Origin
	{
		/// Fraction of a proposal's value that should be bonded in order to place the proposal.
		/// An accepted proposal gets these back. A rejected proposal does not.
		const ProposalBond: Permill = T::ProposalBond::get();

		/// Minimum amount of funds that should be placed in a deposit for making a proposal.
		const ProposalBondMinimum: BalanceOf<T, I> = T::ProposalBondMinimum::get();

		/// Period between successive spends.
		const SpendPeriod: T::BlockNumber = T::SpendPeriod::get();

		/// Percentage of spare funds (if any) that are burnt per spend period.
		const Burn: Permill = T::Burn::get();

		/// The period for which a tip remains open after is has achieved threshold tippers.
		const TipCountdown: T::BlockNumber = T::TipCountdown::get();

		/// The amount of the final tip which goes to the original reporter of the tip.
		const TipFindersFee: Percent = T::TipFindersFee::get();

		/// The amount held on deposit for placing a tip report.
		const TipReportDepositBase: BalanceOf<T, I> = T::TipReportDepositBase::get();

		/// The amount held on deposit per byte within the tip report reason or bounty description.
		const DataDepositPerByte: BalanceOf<T, I> = T::DataDepositPerByte::get();

		/// The treasury's module id, used for deriving its sovereign account ID.
		const ModuleId: ModuleId = T::ModuleId::get();

		/// The amount held on deposit for placing a bounty proposal.
		const BountyDepositBase: BalanceOf<T, I> = T::BountyDepositBase::get();

		/// The delay period for which a bounty beneficiary need to wait before claim the payout.
		const BountyDepositPayoutDelay: T::BlockNumber = T::BountyDepositPayoutDelay::get();

		/// Percentage of the curator fee that will be reserved upfront as deposit for bounty curator.
		const BountyCuratorDeposit: Permill = T::BountyCuratorDeposit::get();

		const BountyValueMinimum: BalanceOf<T, I> = T::BountyValueMinimum::get();

		/// Maximum acceptable reason length.
		const MaximumReasonLength: u32 = T::MaximumReasonLength::get();

		type Error = Error<T, I>;

		fn deposit_event() = default;

		/// Put forward a suggestion for spending. A deposit proportional to the value
		/// is reserved and slashed if the proposal is rejected. It is returned once the
		/// proposal is awarded.
		///
		/// # <weight>
		/// - Complexity: O(1)
		/// - DbReads: `ProposalCount`, `origin account`
		/// - DbWrites: `ProposalCount`, `Proposals`, `origin account`
		/// # </weight>
		#[weight = T::WeightInfo::propose_spend()]
		fn propose_spend(
			origin,
			#[compact] value: BalanceOf<T, I>,
			beneficiary: <T::Lookup as StaticLookup>::Source
		) {
			let proposer = ensure_signed(origin)?;
			let beneficiary = T::Lookup::lookup(beneficiary)?;

			let bond = Self::calculate_bond(value);
			T::Currency::reserve(&proposer, bond)
				.map_err(|_| Error::<T, I>::InsufficientProposersBalance)?;

			let c = Self::proposal_count();
			<ProposalCount<I>>::put(c + 1);
			<Proposals<T, I>>::insert(c, Proposal { proposer, value, beneficiary, bond });

			Self::deposit_event(RawEvent::Proposed(c));
		}

		/// Reject a proposed spend. The original deposit will be slashed.
		///
		/// May only be called from `T::RejectOrigin`.
		///
		/// # <weight>
		/// - Complexity: O(1)
		/// - DbReads: `Proposals`, `rejected proposer account`
		/// - DbWrites: `Proposals`, `rejected proposer account`
		/// # </weight>
		#[weight = (T::WeightInfo::reject_proposal(), DispatchClass::Operational)]
		fn reject_proposal(origin, #[compact] proposal_id: ProposalIndex) {
			T::RejectOrigin::ensure_origin(origin)?;

			let proposal = <Proposals<T, I>>::take(&proposal_id).ok_or(Error::<T, I>::InvalidIndex)?;
			let value = proposal.bond;
			let imbalance = T::Currency::slash_reserved(&proposal.proposer, value).0;
			T::OnSlash::on_unbalanced(imbalance);

			Self::deposit_event(Event::<T, I>::Rejected(proposal_id, value));
		}

		/// Approve a proposal. At a later time, the proposal will be allocated to the beneficiary
		/// and the original deposit will be returned.
		///
		/// May only be called from `T::ApproveOrigin`.
		///
		/// # <weight>
		/// - Complexity: O(1).
		/// - DbReads: `Proposals`, `Approvals`
		/// - DbWrite: `Approvals`
		/// # </weight>
		#[weight = (T::WeightInfo::approve_proposal(), DispatchClass::Operational)]
		fn approve_proposal(origin, #[compact] proposal_id: ProposalIndex) {
			T::ApproveOrigin::ensure_origin(origin)?;

			ensure!(<Proposals<T, I>>::contains_key(proposal_id), Error::<T, I>::InvalidIndex);
			Approvals::<I>::append(proposal_id);
		}

		/// Report something `reason` that deserves a tip and claim any eventual the finder's fee.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// Payment: `TipReportDepositBase` will be reserved from the origin account, as well as
		/// `DataDepositPerByte` for each byte in `reason`.
		///
		/// - `reason`: The reason for, or the thing that deserves, the tip; generally this will be
		///   a UTF-8-encoded URL.
		/// - `who`: The account which should be credited for the tip.
		///
		/// Emits `NewTip` if successful.
		///
		/// # <weight>
		/// - Complexity: `O(R)` where `R` length of `reason`.
		///   - encoding and hashing of 'reason'
		/// - DbReads: `Reasons`, `Tips`
		/// - DbWrites: `Reasons`, `Tips`
		/// # </weight>
		#[weight = T::WeightInfo::report_awesome(reason.len() as u32)]
		fn report_awesome(origin, reason: Vec<u8>, who: T::AccountId) {
			let finder = ensure_signed(origin)?;

			ensure!(reason.len() <= T::MaximumReasonLength::get() as usize, Error::<T, I>::ReasonTooBig);

			let reason_hash = T::Hashing::hash(&reason[..]);
			ensure!(!Reasons::<T, I>::contains_key(&reason_hash), Error::<T, I>::AlreadyKnown);
			let hash = T::Hashing::hash_of(&(&reason_hash, &who));
			ensure!(!Tips::<T, I>::contains_key(&hash), Error::<T, I>::AlreadyKnown);

			let deposit = T::TipReportDepositBase::get()
				+ T::DataDepositPerByte::get() * (reason.len() as u32).into();
			T::Currency::reserve(&finder, deposit)?;

			Reasons::<T, I>::insert(&reason_hash, &reason);
			let tip = OpenTip {
				reason: reason_hash,
				who,
				finder,
				deposit,
				closes: None,
				tips: vec![],
				finders_fee: true
			};
			Tips::<T, I>::insert(&hash, tip);
			Self::deposit_event(RawEvent::NewTip(hash));
		}

		/// Retract a prior tip-report from `report_awesome`, and cancel the process of tipping.
		///
		/// If successful, the original deposit will be unreserved.
		///
		/// The dispatch origin for this call must be _Signed_ and the tip identified by `hash`
		/// must have been reported by the signing account through `report_awesome` (and not
		/// through `tip_new`).
		///
		/// - `hash`: The identity of the open tip for which a tip value is declared. This is formed
		///   as the hash of the tuple of the original tip `reason` and the beneficiary account ID.
		///
		/// Emits `TipRetracted` if successful.
		///
		/// # <weight>
		/// - Complexity: `O(1)`
		///   - Depends on the length of `T::Hash` which is fixed.
		/// - DbReads: `Tips`, `origin account`
		/// - DbWrites: `Reasons`, `Tips`, `origin account`
		/// # </weight>
		#[weight = T::WeightInfo::retract_tip()]
		fn retract_tip(origin, hash: T::Hash) {
			let who = ensure_signed(origin)?;
			let tip = Tips::<T, I>::get(&hash).ok_or(Error::<T, I>::UnknownTip)?;
			ensure!(tip.finder == who, Error::<T, I>::NotFinder);

			Reasons::<T, I>::remove(&tip.reason);
			Tips::<T, I>::remove(&hash);
			if !tip.deposit.is_zero() {
				let _ = T::Currency::unreserve(&who, tip.deposit);
			}
			Self::deposit_event(RawEvent::TipRetracted(hash));
		}

		/// Give a tip for something new; no finder's fee will be taken.
		///
		/// The dispatch origin for this call must be _Signed_ and the signing account must be a
		/// member of the `Tippers` set.
		///
		/// - `reason`: The reason for, or the thing that deserves, the tip; generally this will be
		///   a UTF-8-encoded URL.
		/// - `who`: The account which should be credited for the tip.
		/// - `tip_value`: The amount of tip that the sender would like to give. The median tip
		///   value of active tippers will be given to the `who`.
		///
		/// Emits `NewTip` if successful.
		///
		/// # <weight>
		/// - Complexity: `O(R + T)` where `R` length of `reason`, `T` is the number of tippers.
		///   - `O(T)`: decoding `Tipper` vec of length `T`
		///     `T` is charged as upper bound given by `ContainsLengthBound`.
		///     The actual cost depends on the implementation of `T::Tippers`.
		///   - `O(R)`: hashing and encoding of reason of length `R`
		/// - DbReads: `Tippers`, `Reasons`
		/// - DbWrites: `Reasons`, `Tips`
		/// # </weight>
		#[weight = T::WeightInfo::tip_new(reason.len() as u32, T::Tippers::max_len() as u32)]
		fn tip_new(origin, reason: Vec<u8>, who: T::AccountId, #[compact] tip_value: BalanceOf<T, I>) {
			let tipper = ensure_signed(origin)?;
			ensure!(T::Tippers::contains(&tipper), BadOrigin);
			let reason_hash = T::Hashing::hash(&reason[..]);
			ensure!(!Reasons::<T, I>::contains_key(&reason_hash), Error::<T, I>::AlreadyKnown);
			let hash = T::Hashing::hash_of(&(&reason_hash, &who));

			Reasons::<T, I>::insert(&reason_hash, &reason);
			Self::deposit_event(RawEvent::NewTip(hash.clone()));
			let tips = vec![(tipper.clone(), tip_value)];
			let tip = OpenTip {
				reason: reason_hash,
				who,
				finder: tipper,
				deposit: Zero::zero(),
				closes: None,
				tips,
				finders_fee: false,
			};
			Tips::<T, I>::insert(&hash, tip);
		}

		/// Declare a tip value for an already-open tip.
		///
		/// The dispatch origin for this call must be _Signed_ and the signing account must be a
		/// member of the `Tippers` set.
		///
		/// - `hash`: The identity of the open tip for which a tip value is declared. This is formed
		///   as the hash of the tuple of the hash of the original tip `reason` and the beneficiary
		///   account ID.
		/// - `tip_value`: The amount of tip that the sender would like to give. The median tip
		///   value of active tippers will be given to the `who`.
		///
		/// Emits `TipClosing` if the threshold of tippers has been reached and the countdown period
		/// has started.
		///
		/// # <weight>
		/// - Complexity: `O(T)` where `T` is the number of tippers.
		///   decoding `Tipper` vec of length `T`, insert tip and check closing,
		///   `T` is charged as upper bound given by `ContainsLengthBound`.
		///   The actual cost depends on the implementation of `T::Tippers`.
		///
		///   Actually weight could be lower as it depends on how many tips are in `OpenTip` but it
		///   is weighted as if almost full i.e of length `T-1`.
		/// - DbReads: `Tippers`, `Tips`
		/// - DbWrites: `Tips`
		/// # </weight>
		#[weight = T::WeightInfo::tip(T::Tippers::max_len() as u32)]
		fn tip(origin, hash: T::Hash, #[compact] tip_value: BalanceOf<T, I>) {
			let tipper = ensure_signed(origin)?;
			ensure!(T::Tippers::contains(&tipper), BadOrigin);

			let mut tip = Tips::<T, I>::get(hash).ok_or(Error::<T, I>::UnknownTip)?;
			if Self::insert_tip_and_check_closing(&mut tip, tipper, tip_value) {
				Self::deposit_event(RawEvent::TipClosing(hash.clone()));
			}
			Tips::<T, I>::insert(&hash, tip);
		}

		/// Close and payout a tip.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// The tip identified by `hash` must have finished its countdown period.
		///
		/// - `hash`: The identity of the open tip for which a tip value is declared. This is formed
		///   as the hash of the tuple of the original tip `reason` and the beneficiary account ID.
		///
		/// # <weight>
		/// - Complexity: `O(T)` where `T` is the number of tippers.
		///   decoding `Tipper` vec of length `T`.
		///   `T` is charged as upper bound given by `ContainsLengthBound`.
		///   The actual cost depends on the implementation of `T::Tippers`.
		/// - DbReads: `Tips`, `Tippers`, `tip finder`
		/// - DbWrites: `Reasons`, `Tips`, `Tippers`, `tip finder`
		/// # </weight>
		#[weight = T::WeightInfo::close_tip(T::Tippers::max_len() as u32)]
		fn close_tip(origin, hash: T::Hash) {
			ensure_signed(origin)?;

			let tip = Tips::<T, I>::get(hash).ok_or(Error::<T, I>::UnknownTip)?;
			let n = tip.closes.as_ref().ok_or(Error::<T, I>::StillOpen)?;
			ensure!(system::Module::<T>::block_number() >= *n, Error::<T, I>::Premature);
			// closed.
			Reasons::<T, I>::remove(&tip.reason);
			Tips::<T, I>::remove(hash);
			Self::payout_tip(hash, tip);
		}

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
		#[weight = T::WeightInfo::propose_bounty(description.len() as u32)]
		fn propose_bounty(
			origin,
			#[compact] value: BalanceOf<T, I>,
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
		/// - Limited storage reads.
		/// - One DB change.
		/// # </weight>
		#[weight = T::WeightInfo::approve_bounty()]
		fn approve_bounty(origin, #[compact] bounty_id: ProposalIndex) {
			T::ApproveOrigin::ensure_origin(origin)?;

			Bounties::<T, I>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let mut bounty = maybe_bounty.as_mut().ok_or(Error::<T, I>::InvalidIndex)?;
				ensure!(bounty.status == BountyStatus::Proposed, Error::<T, I>::UnexpectedStatus);

				bounty.status = BountyStatus::Approved;

				BountyApprovals::<I>::append(bounty_id);

				Ok(())
			})?;
		}

		/// Assign a curator to a funded bounty.
		///
		/// May only be called from `T::ApproveOrigin`.
		///
		/// # <weight>
		/// - O(1).
		/// - Limited storage reads.
		/// - One DB change.
		/// # </weight>
		#[weight = T::WeightInfo::propose_curator()]
		fn propose_curator(
			origin,
			#[compact] bounty_id: ProposalIndex,
			curator: <T::Lookup as StaticLookup>::Source,
			#[compact] fee: BalanceOf<T, I>,
		) {
			T::ApproveOrigin::ensure_origin(origin)?;

			let curator = T::Lookup::lookup(curator)?;
			Bounties::<T, I>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let mut bounty = maybe_bounty.as_mut().ok_or(Error::<T, I>::InvalidIndex)?;
				match bounty.status {
					BountyStatus::Funded | BountyStatus::CuratorProposed { .. } => {},
					_ => return Err(Error::<T, I>::UnexpectedStatus.into()),
				};

				ensure!(fee < bounty.value, Error::<T, I>::InvalidFee);

				bounty.status = BountyStatus::CuratorProposed { curator };
				bounty.fee = fee;

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
		/// - Limited storage reads.
		/// - One DB change.
		/// # </weight>
		#[weight = T::WeightInfo::unassign_curator()]
		fn unassign_curator(
			origin,
			#[compact] bounty_id: ProposalIndex,
		) {
			let maybe_sender = ensure_signed(origin.clone())
				.map(Some)
				.or_else(|_| T::RejectOrigin::ensure_origin(origin).map(|_| None))?;

			Bounties::<T, I>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let mut bounty = maybe_bounty.as_mut().ok_or(Error::<T, I>::InvalidIndex)?;

				let slash_curator = |curator: &T::AccountId, curator_deposit: &mut BalanceOf<T, I>| {
					let imbalance = T::Currency::slash_reserved(curator, *curator_deposit).0;
					T::OnSlash::on_unbalanced(imbalance);
					*curator_deposit = Zero::zero();
				};

				match bounty.status {
					BountyStatus::Proposed | BountyStatus::Approved | BountyStatus::Funded => {
						// No curator to unassign at this point.
						return Err(Error::<T, I>::UnexpectedStatus.into())
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
										return Err(Error::<T, I>::Premature.into())
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
					}
				};

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
		/// - Limited storage reads.
		/// - One DB change.
		/// # </weight>
		#[weight = T::WeightInfo::accept_curator()]
		fn accept_curator(origin, #[compact] bounty_id: ProposalIndex) {
			let signer = ensure_signed(origin)?;

			Bounties::<T, I>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let mut bounty = maybe_bounty.as_mut().ok_or(Error::<T, I>::InvalidIndex)?;

				match bounty.status {
					BountyStatus::CuratorProposed { ref curator } => {
						ensure!(signer == *curator, Error::<T, I>::RequireCurator);

						let deposit = T::BountyCuratorDeposit::get() * bounty.fee;
						T::Currency::reserve(curator, deposit)?;
						bounty.curator_deposit = deposit;

						let update_due = system::Module::<T>::block_number() + T::BountyUpdatePeriod::get();
						bounty.status = BountyStatus::Active { curator: curator.clone(), update_due };

						Ok(())
					},
					_ => Err(Error::<T, I>::UnexpectedStatus.into()),
				}
			})?;
		}

		/// Award bounty to a beneficiary account. The beneficiary will be able to claim the funds after a delay.
		///
		/// The dispatch origin for this call must be the curator of this bounty.
		///
		/// - `bounty_id`: Bounty ID to award.
		/// - `beneficiary`: The beneficiary account whom will receive the payout.
		#[weight = T::WeightInfo::award_bounty()]
		fn award_bounty(origin, #[compact] bounty_id: ProposalIndex, beneficiary: <T::Lookup as StaticLookup>::Source) {
			let signer = ensure_signed(origin)?;
			let beneficiary = T::Lookup::lookup(beneficiary)?;

			Bounties::<T, I>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let mut bounty = maybe_bounty.as_mut().ok_or(Error::<T, I>::InvalidIndex)?;
				match &bounty.status {
					BountyStatus::Active {
						curator,
						..
					} => {
						ensure!(signer == *curator, Error::<T, I>::RequireCurator);
					},
					_ => return Err(Error::<T, I>::UnexpectedStatus.into()),
				}
				bounty.status = BountyStatus::PendingPayout {
					curator: signer,
					beneficiary: beneficiary.clone(),
					unlock_at: system::Module::<T>::block_number() + T::BountyDepositPayoutDelay::get(),
				};

				Ok(())
			})?;

			Self::deposit_event(Event::<T, I>::BountyAwarded(bounty_id, beneficiary));
		}

		/// Claim the payout from an awarded bounty after payout delay.
		///
		/// The dispatch origin for this call must be the beneficiary of this bounty.
		///
		/// - `bounty_id`: Bounty ID to claim.
		#[weight = T::WeightInfo::claim_bounty()]
		fn claim_bounty(origin, #[compact] bounty_id: BountyIndex) {
			let _ = ensure_signed(origin)?; // anyone can trigger claim

			Bounties::<T, I>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let bounty = maybe_bounty.take().ok_or(Error::<T, I>::InvalidIndex)?;
				if let BountyStatus::PendingPayout { curator, beneficiary, unlock_at } = bounty.status {
					ensure!(system::Module::<T>::block_number() >= unlock_at, Error::<T, I>::Premature);
					let bounty_account = Self::bounty_account_id(bounty_id);
					let balance = T::Currency::free_balance(&bounty_account);
					let fee = bounty.fee.min(balance); // just to be safe
					let payout = balance.saturating_sub(fee);
					let _ = T::Currency::unreserve(&curator, bounty.curator_deposit);
					let _ = T::Currency::transfer(&bounty_account, &curator, fee, AllowDeath); // should not fail
					let _ = T::Currency::transfer(&bounty_account, &beneficiary, payout, AllowDeath); // should not fail
					*maybe_bounty = None;

					BountyDescriptions::<I>::remove(bounty_id);

					Self::deposit_event(Event::<T, I>::BountyClaimed(bounty_id, payout, beneficiary));
					Ok(())
				} else {
					Err(Error::<T, I>::UnexpectedStatus.into())
				}
			})?;
		}

		/// Cancel a proposed or active bounty. All the funds will be sent to treasury and
		/// the curator deposit will be unreserved if possible.
		///
		/// Only `T::RejectOrigin` is able to cancel a bounty.
		///
		/// - `bounty_id`: Bounty ID to cancel.
		#[weight = T::WeightInfo::close_bounty_proposed().max(T::WeightInfo::close_bounty_active())]
		fn close_bounty(origin, #[compact] bounty_id: BountyIndex) -> DispatchResultWithPostInfo {
			T::RejectOrigin::ensure_origin(origin)?;

			Bounties::<T, I>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResultWithPostInfo {
				let bounty = maybe_bounty.as_ref().ok_or(Error::<T, I>::InvalidIndex)?;

				match &bounty.status {
					BountyStatus::Proposed => {
						// The reject origin would like to cancel a proposed bounty.
						BountyDescriptions::<I>::remove(bounty_id);
						let value = bounty.bond;
						let imbalance = T::Currency::slash_reserved(&bounty.proposer, value).0;
						T::OnSlash::on_unbalanced(imbalance);
						*maybe_bounty = None;

						Self::deposit_event(Event::<T, I>::BountyRejected(bounty_id, value));
						// Return early, nothing else to do.
						return Ok(Some(T::WeightInfo::close_bounty_proposed()).into())
					},
					BountyStatus::Approved => {
						// For weight reasons, we don't allow a council to cancel in this phase.
						// We ask for them to wait until it is funded before they can cancel.
						return Err(Error::<T, I>::UnexpectedStatus.into())
					},
					BountyStatus::Funded |
					BountyStatus::CuratorProposed { .. } => {
						// Nothing extra to do besides the removal of the bounty below.
					},
					BountyStatus::Active { curator, .. } => {
						// Cancelled by council, refund deposit of the working curator.
						let _ = T::Currency::unreserve(&curator, bounty.curator_deposit);
						// Then execute removal of the bounty below.
					},
					BountyStatus::PendingPayout { .. } => {
						// Bounty is already pending payout. If council wants to cancel
						// this bounty, it should mean the curator was acting maliciously.
						// So the council should first unassign the curator, slashing their
						// deposit.
						return Err(Error::<T, I>::PendingPayout.into())
					}
				}

				let bounty_account = Self::bounty_account_id(bounty_id);

				BountyDescriptions::<I>::remove(bounty_id);

				let balance = T::Currency::free_balance(&bounty_account);
				let _ = T::Currency::transfer(&bounty_account, &Self::account_id(), balance, AllowDeath); // should not fail
				*maybe_bounty = None;

				Self::deposit_event(Event::<T, I>::BountyCanceled(bounty_id));
				Ok(Some(T::WeightInfo::close_bounty_active()).into())
			})
		}

		/// Extend the expiry time of an active bounty.
		///
		/// The dispatch origin for this call must be the curator of this bounty.
		///
		/// - `bounty_id`: Bounty ID to extend.
		/// - `remark`: additional information.
		#[weight = T::WeightInfo::extend_bounty_expiry()]
		fn extend_bounty_expiry(origin, #[compact] bounty_id: BountyIndex, _remark: Vec<u8>) {
			let signer = ensure_signed(origin)?;

			Bounties::<T, I>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let bounty = maybe_bounty.as_mut().ok_or(Error::<T, I>::InvalidIndex)?;

				match bounty.status {
					BountyStatus::Active { ref curator, ref mut update_due } => {
						ensure!(*curator == signer, Error::<T, I>::RequireCurator);
						*update_due = (system::Module::<T>::block_number() + T::BountyUpdatePeriod::get()).max(*update_due);
					},
					_ => return Err(Error::<T, I>::UnexpectedStatus.into()),
				}

				Ok(())
			})?;

			Self::deposit_event(Event::<T, I>::BountyExtended(bounty_id));
		}

		/// # <weight>
		/// - Complexity: `O(A)` where `A` is the number of approvals
		/// - Db reads and writes: `Approvals`, `pot account data`
		/// - Db reads and writes per approval:
		///   `Proposals`, `proposer account data`, `beneficiary account data`
		/// - The weight is overestimated if some approvals got missed.
		/// # </weight>
		fn on_initialize(n: T::BlockNumber) -> Weight {
			// Check to see if we should spend some funds!
			if (n % T::SpendPeriod::get()).is_zero() {
				Self::spend_funds()
			} else {
				0
			}
		}
	}
}

impl<T: Trait<I>, I: Instance> Module<T, I> {
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

	/// The needed bond for a proposal whose spend is `value`.
	fn calculate_bond(value: BalanceOf<T, I>) -> BalanceOf<T, I> {
		T::ProposalBondMinimum::get().max(T::ProposalBond::get() * value)
	}

	/// Given a mutable reference to an `OpenTip`, insert the tip into it and check whether it
	/// closes, if so, then deposit the relevant event and set closing accordingly.
	///
	/// `O(T)` and one storage access.
	fn insert_tip_and_check_closing(
		tip: &mut OpenTip<T::AccountId, BalanceOf<T, I>, T::BlockNumber, T::Hash>,
		tipper: T::AccountId,
		tip_value: BalanceOf<T, I>,
	) -> bool {
		match tip.tips.binary_search_by_key(&&tipper, |x| &x.0) {
			Ok(pos) => tip.tips[pos] = (tipper, tip_value),
			Err(pos) => tip.tips.insert(pos, (tipper, tip_value)),
		}
		Self::retain_active_tips(&mut tip.tips);
		let threshold = (T::Tippers::count() + 1) / 2;
		if tip.tips.len() >= threshold && tip.closes.is_none() {
			tip.closes = Some(system::Module::<T>::block_number() + T::TipCountdown::get());
			true
		} else {
			false
		}
	}

	/// Remove any non-members of `Tippers` from a `tips` vector. `O(T)`.
	fn retain_active_tips(tips: &mut Vec<(T::AccountId, BalanceOf<T, I>)>) {
		let members = T::Tippers::sorted_members();
		let mut members_iter = members.iter();
		let mut member = members_iter.next();
		tips.retain(|(ref a, _)| loop {
			match member {
				None => break false,
				Some(m) if m > a => break false,
				Some(m) => {
					member = members_iter.next();
					if m < a {
						continue
					} else {
						break true;
					}
				}
			}
		});
	}

	/// Execute the payout of a tip.
	///
	/// Up to three balance operations.
	/// Plus `O(T)` (`T` is Tippers length).
	fn payout_tip(hash: T::Hash, tip: OpenTip<T::AccountId, BalanceOf<T, I>, T::BlockNumber, T::Hash>) {
		let mut tips = tip.tips;
		Self::retain_active_tips(&mut tips);
		tips.sort_by_key(|i| i.1);
		let treasury = Self::account_id();
		let max_payout = Self::pot();
		let mut payout = tips[tips.len() / 2].1.min(max_payout);
		if !tip.deposit.is_zero() {
			let _ = T::Currency::unreserve(&tip.finder, tip.deposit);
		}
		if tip.finders_fee {
			if tip.finder != tip.who {
				// pay out the finder's fee.
				let finders_fee = T::TipFindersFee::get() * payout;
				payout -= finders_fee;
				// this should go through given we checked it's at most the free balance, but still
				// we only make a best-effort.
				let _ = T::Currency::transfer(&treasury, &tip.finder, finders_fee, KeepAlive);
			}
		}
		// same as above: best-effort only.
		let _ = T::Currency::transfer(&treasury, &tip.who, payout, KeepAlive);
		Self::deposit_event(RawEvent::TipClosed(hash, tip.who, payout));
	}

	/// Spend some money! returns number of approvals before spend.
	fn spend_funds() -> Weight {
		let mut total_weight: Weight = Zero::zero();

		let mut budget_remaining = Self::pot();
		Self::deposit_event(RawEvent::Spending(budget_remaining));
		let account_id = Self::account_id();

		let mut missed_any = false;
		let mut imbalance = <PositiveImbalanceOf<T, I>>::zero();
		let proposals_len = Approvals::<I>::mutate(|v| {
			let proposals_approvals_len = v.len() as u32;
			v.retain(|&index| {
				// Should always be true, but shouldn't panic if false or we're screwed.
				if let Some(p) = Self::proposals(index) {
					if p.value <= budget_remaining {
						budget_remaining -= p.value;
						<Proposals<T, I>>::remove(index);

						// return their deposit.
						let _ = T::Currency::unreserve(&p.proposer, p.bond);

						// provide the allocation.
						imbalance.subsume(T::Currency::deposit_creating(&p.beneficiary, p.value));

						Self::deposit_event(RawEvent::Awarded(index, p.value, p.beneficiary));
						false
					} else {
						missed_any = true;
						true
					}
				} else {
					false
				}
			});
			proposals_approvals_len
		});

		total_weight += T::WeightInfo::on_initialize_proposals(proposals_len);

		let bounties_len = BountyApprovals::<I>::mutate(|v| {
			let bounties_approval_len = v.len() as u32;
			v.retain(|&index| {
				Bounties::<T, I>::mutate(index, |bounty| {
					// Should always be true, but shouldn't panic if false or we're screwed.
					if let Some(bounty) = bounty {
						if bounty.value <= budget_remaining {
							budget_remaining -= bounty.value;

							bounty.status = BountyStatus::Funded;

							// return their deposit.
							let _ = T::Currency::unreserve(&bounty.proposer, bounty.bond);

							// fund the bounty account
							imbalance.subsume(T::Currency::deposit_creating(&Self::bounty_account_id(index), bounty.value));

							Self::deposit_event(RawEvent::BountyBecameActive(index));
							false
						} else {
							missed_any = true;
							true
						}
					} else {
						false
					}
				})
			});
			bounties_approval_len
		});

		total_weight += T::WeightInfo::on_initialize_bounties(bounties_len);

		if !missed_any {
			// burn some proportion of the remaining budget if we run a surplus.
			let burn = (T::Burn::get() * budget_remaining).min(budget_remaining);
			budget_remaining -= burn;

			let (debit, credit) = T::Currency::pair(burn);
			imbalance.subsume(debit);
			T::BurnDestination::on_unbalanced(credit);
			Self::deposit_event(RawEvent::Burnt(burn))
		}

		// Must never be an error, but better to be safe.
		// proof: budget_remaining is account free balance minus ED;
		// Thus we can't spend more than account free balance minus ED;
		// Thus account is kept alive; qed;
		if let Err(problem) = T::Currency::settle(
			&account_id,
			imbalance,
			WithdrawReason::Transfer.into(),
			KeepAlive
		) {
			print("Inconsistent state - couldn't settle imbalance for funds spent by treasury");
			// Nothing else to do here.
			drop(problem);
		}

		Self::deposit_event(RawEvent::Rollover(budget_remaining));

		total_weight
	}

	/// Return the amount of money in the pot.
	// The existential deposit is not part of the pot so treasury account never gets deleted.
	fn pot() -> BalanceOf<T, I> {
		T::Currency::free_balance(&Self::account_id())
			// Must never be less than 0 but better be safe.
			.saturating_sub(T::Currency::minimum_balance())
	}

	fn create_bounty(
		proposer: T::AccountId,
		description: Vec<u8>,
		value: BalanceOf<T, I>,
	) -> DispatchResult {
		ensure!(description.len() <= T::MaximumReasonLength::get() as usize, Error::<T, I>::ReasonTooBig);
		ensure!(value >= T::BountyValueMinimum::get(), Error::<T, I>::InvalidValue);

		let index = Self::bounty_count();

		// reserve deposit for new bounty
		let bond = T::BountyDepositBase::get()
			+ T::DataDepositPerByte::get() * (description.len() as u32).into();
		T::Currency::reserve(&proposer, bond)
			.map_err(|_| Error::<T, I>::InsufficientProposersBalance)?;

		BountyCount::<I>::put(index + 1);

		let bounty = Bounty {
			proposer,
			value,
			fee: 0u32.into(),
			curator_deposit: 0u32.into(),
			bond,
			status: BountyStatus::Proposed,
		};

		Bounties::<T, I>::insert(index, &bounty);
		BountyDescriptions::<I>::insert(index, description);

		Self::deposit_event(RawEvent::BountyProposed(index));

		Ok(())
	}

	pub fn migrate_retract_tip_for_tip_new() {
		/// An open tipping "motion". Retains all details of a tip including information on the finder
		/// and the members who have voted.
		#[derive(Clone, Eq, PartialEq, Encode, Decode, RuntimeDebug)]
		pub struct OldOpenTip<
			AccountId: Parameter,
			Balance: Parameter,
			BlockNumber: Parameter,
			Hash: Parameter,
		> {
			/// The hash of the reason for the tip. The reason should be a human-readable UTF-8 encoded string. A URL would be
			/// sensible.
			reason: Hash,
			/// The account to be tipped.
			who: AccountId,
			/// The account who began this tip and the amount held on deposit.
			finder: Option<(AccountId, Balance)>,
			/// The block number at which this tip will close if `Some`. If `None`, then no closing is
			/// scheduled.
			closes: Option<BlockNumber>,
			/// The members who have voted for this tip. Sorted by AccountId.
			tips: Vec<(AccountId, Balance)>,
		}

		use frame_support::{Twox64Concat, migration::StorageKeyIterator};

		for (hash, old_tip) in StorageKeyIterator::<
			T::Hash,
			OldOpenTip<T::AccountId, BalanceOf<T, I>, T::BlockNumber, T::Hash>,
			Twox64Concat,
		>::new(I::PREFIX.as_bytes(), b"Tips").drain()
		{
			let (finder, deposit, finders_fee) = match old_tip.finder {
				Some((finder, deposit)) => (finder, deposit, true),
				None => (T::AccountId::default(), Zero::zero(), false),
			};
			let new_tip = OpenTip {
				reason: old_tip.reason,
				who: old_tip.who,
				finder,
				deposit,
				closes: old_tip.closes,
				tips: old_tip.tips,
				finders_fee
			};
			Tips::<T, I>::insert(hash, new_tip)
		}
	}
}

impl<T: Trait<I>, I: Instance> OnUnbalanced<NegativeImbalanceOf<T, I>> for Module<T, I> {
	fn on_nonzero_unbalanced(amount: NegativeImbalanceOf<T, I>) {
		let numeric_amount = amount.peek();

		// Must resolve into existing but better to be safe.
		let _ = T::Currency::resolve_creating(&Self::account_id(), amount);

		Self::deposit_event(RawEvent::Deposit(numeric_amount));
	}
}
