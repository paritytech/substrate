// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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
//! ## GenesisConfig
//!
//! The Treasury module depends on the [`GenesisConfig`](./struct.GenesisConfig.html).

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
use sp_std::prelude::*;
use frame_support::{decl_module, decl_storage, decl_event, ensure, print, decl_error, Parameter};
use frame_support::traits::{
	Currency, ExistenceRequirement, Get, Imbalance, OnUnbalanced, ExistenceRequirement::AllowDeath,
	ReservableCurrency, WithdrawReason
};
use sp_runtime::{Permill, ModuleId, Percent, RuntimeDebug, traits::{
	Zero, EnsureOrigin, StaticLookup, AccountIdConversion, Saturating, Hash, BadOrigin
}};
use frame_support::{weights::SimpleDispatchInfo, traits::Contains};
use codec::{Encode, Decode};
use frame_system::{self as system, ensure_signed};

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
type PositiveImbalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::PositiveImbalance;
type NegativeImbalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::NegativeImbalance;

/// The treasury's module id, used for deriving its sovereign account ID.
const MODULE_ID: ModuleId = ModuleId(*b"py/trsry");

pub trait Trait: frame_system::Trait {
	/// The staking balance.
	type Currency: Currency<Self::AccountId> + ReservableCurrency<Self::AccountId>;

	/// Origin from which approvals must come.
	type ApproveOrigin: EnsureOrigin<Self::Origin>;

	/// Origin from which rejections must come.
	type RejectOrigin: EnsureOrigin<Self::Origin>;

	/// Origin from which tippers must come.
	type Tippers: Contains<Self::AccountId>;

	/// The period for which a tip remains open after is has achieved threshold tippers.
	type TipCountdown: Get<Self::BlockNumber>;

	/// The percent of the final tip which goes to the original reporter of the tip.
	type TipFindersFee: Get<Percent>;

	/// The amount held on deposit for placing a tip report.
	type TipReportDepositBase: Get<BalanceOf<Self>>;

	/// The amount held on deposit per byte within the tip report reason.
	type TipReportDepositPerByte: Get<BalanceOf<Self>>;

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

	/// Handler for the unbalanced decrease when slashing for a rejected proposal.
	type ProposalRejection: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// Fraction of a proposal's value that should be bonded in order to place the proposal.
	/// An accepted proposal gets these back. A rejected proposal does not.
	type ProposalBond: Get<Permill>;

	/// Minimum amount of funds that should be placed in a deposit for making a proposal.
	type ProposalBondMinimum: Get<BalanceOf<Self>>;

	/// Period between successive spends.
	type SpendPeriod: Get<Self::BlockNumber>;

	/// Percentage of spare funds (if any) that are burnt per spend period.
	type Burn: Get<Permill>;
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
	/// The account who began this tip and the amount held on deposit.
	finder: Option<(AccountId, Balance)>,
	/// The block number at which this tip will close if `Some`. If `None`, then no closing is
	/// scheduled.
	closes: Option<BlockNumber>,
	/// The members who have voted for this tip. Sorted by AccountId.
	tips: Vec<(AccountId, Balance)>,
}

decl_storage! {
	trait Store for Module<T: Trait> as Treasury {
		/// Number of proposals that have been made.
		ProposalCount get(fn proposal_count): ProposalIndex;

		/// Proposals that have been made.
		Proposals get(fn proposals): map hasher(blake2_256) ProposalIndex => Option<Proposal<T::AccountId, BalanceOf<T>>>;

		/// Proposal indices that have been approved but not yet awarded.
		Approvals get(fn approvals): Vec<ProposalIndex>;

		/// Tips that are not yet completed. Keyed by the hash of `(reason, who)` from the value.
		/// This has the insecure enumerable hash function since the key itself is already
		/// guaranteed to be a secure hash.
		pub Tips get(fn tips): map hasher(twox_64_concat) T::Hash
			=> Option<OpenTip<T::AccountId, BalanceOf<T>, T::BlockNumber, T::Hash>>;

		/// Simple preimage lookup from the reason's hash to the original data. Again, has an
		/// insecure enumerable hash since the key is guaranteed to be the result of a secure hash.
		pub Reasons get(fn reasons): map hasher(twox_64_concat) T::Hash => Option<Vec<u8>>;
	}
	add_extra_genesis {
		build(|_config| {
			// Create Treasury account
			let _ = T::Currency::make_free_balance_be(
				&<Module<T>>::account_id(),
				T::Currency::minimum_balance(),
			);
		});
	}
}

decl_event!(
	pub enum Event<T>
	where
		Balance = BalanceOf<T>,
		<T as frame_system::Trait>::AccountId,
		<T as frame_system::Trait>::Hash,
	{
		/// New proposal.
		Proposed(ProposalIndex),
		/// We have ended a spend period and will now allocate funds.
		Spending(Balance),
		/// Some funds have been allocated.
		Awarded(ProposalIndex, Balance, AccountId),
		/// A proposal was rejected; funds were slashed.
		Rejected(ProposalIndex, Balance),
		/// Some of our funds have been burnt.
		Burnt(Balance),
		/// Spending has finished; this is the amount that rolls over until next spend.
		Rollover(Balance),
		/// Some funds have been deposited.
		Deposit(Balance),
		/// A new tip suggestion has been opened.
		NewTip(Hash),
		/// A tip suggestion has reached threshold and is closing.
		TipClosing(Hash),
		/// A tip suggestion has been closed.
		TipClosed(Hash, AccountId, Balance),
		/// A tip suggestion has been retracted.
		TipRetracted(Hash),
	}
);

decl_error! {
	/// Error for the treasury module.
	pub enum Error for Module<T: Trait> {
		/// Proposer's balance is too low.
		InsufficientProposersBalance,
		/// No proposal at that index.
		InvalidProposalIndex,
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
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// Fraction of a proposal's value that should be bonded in order to place the proposal.
		/// An accepted proposal gets these back. A rejected proposal does not.
		const ProposalBond: Permill = T::ProposalBond::get();

		/// Minimum amount of funds that should be placed in a deposit for making a proposal.
		const ProposalBondMinimum: BalanceOf<T> = T::ProposalBondMinimum::get();

		/// Period between successive spends.
		const SpendPeriod: T::BlockNumber = T::SpendPeriod::get();

		/// Percentage of spare funds (if any) that are burnt per spend period.
		const Burn: Permill = T::Burn::get();

		/// The period for which a tip remains open after is has achieved threshold tippers.
		const TipCountdown: T::BlockNumber = T::TipCountdown::get();

		/// The amount of the final tip which goes to the original reporter of the tip.
		const TipFindersFee: Percent = T::TipFindersFee::get();

		/// The amount held on deposit for placing a tip report.
		const TipReportDepositBase: BalanceOf<T> = T::TipReportDepositBase::get();

		/// The amount held on deposit per byte within the tip report reason.
		const TipReportDepositPerByte: BalanceOf<T> = T::TipReportDepositPerByte::get();

		type Error = Error<T>;

		fn deposit_event() = default;

		/// Put forward a suggestion for spending. A deposit proportional to the value
		/// is reserved and slashed if the proposal is rejected. It is returned once the
		/// proposal is awarded.
		///
		/// # <weight>
		/// - O(1).
		/// - Limited storage reads.
		/// - One DB change, one extra DB entry.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(500_000)]
		fn propose_spend(
			origin,
			#[compact] value: BalanceOf<T>,
			beneficiary: <T::Lookup as StaticLookup>::Source
		) {
			let proposer = ensure_signed(origin)?;
			let beneficiary = T::Lookup::lookup(beneficiary)?;

			let bond = Self::calculate_bond(value);
			T::Currency::reserve(&proposer, bond)
				.map_err(|_| Error::<T>::InsufficientProposersBalance)?;

			let c = Self::proposal_count();
			ProposalCount::put(c + 1);
			<Proposals<T>>::insert(c, Proposal { proposer, value, beneficiary, bond });

			Self::deposit_event(RawEvent::Proposed(c));
		}

		/// Reject a proposed spend. The original deposit will be slashed.
		///
		/// # <weight>
		/// - O(1).
		/// - Limited storage reads.
		/// - One DB clear.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedOperational(100_000)]
		fn reject_proposal(origin, #[compact] proposal_id: ProposalIndex) {
			T::RejectOrigin::ensure_origin(origin)?;
			let proposal = <Proposals<T>>::take(&proposal_id).ok_or(Error::<T>::InvalidProposalIndex)?;

			let value = proposal.bond;
			let imbalance = T::Currency::slash_reserved(&proposal.proposer, value).0;
			T::ProposalRejection::on_unbalanced(imbalance);

			Self::deposit_event(Event::<T>::Rejected(proposal_id, value));
		}

		/// Approve a proposal. At a later time, the proposal will be allocated to the beneficiary
		/// and the original deposit will be returned.
		///
		/// # <weight>
		/// - O(1).
		/// - Limited storage reads.
		/// - One DB change.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedOperational(100_000)]
		fn approve_proposal(origin, #[compact] proposal_id: ProposalIndex) {
			T::ApproveOrigin::ensure_origin(origin)?;

			ensure!(<Proposals<T>>::contains_key(proposal_id), Error::<T>::InvalidProposalIndex);

			Approvals::mutate(|v| v.push(proposal_id));
		}

		/// Report something `reason` that deserves a tip and claim any eventual the finder's fee.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// Payment: `TipReportDepositBase` will be reserved from the origin account, as well as
		/// `TipReportDepositPerByte` for each byte in `reason`.
		///
		/// - `reason`: The reason for, or the thing that deserves, the tip; generally this will be
		///   a UTF-8-encoded URL.
		/// - `who`: The account which should be credited for the tip.
		///
		/// Emits `NewTip` if successful.
		///
		/// # <weight>
		/// - `O(R)` where `R` length of `reason`.
		/// - One balance operation.
		/// - One storage mutation (codec `O(R)`).
		/// - One event.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(100_000)]
		fn report_awesome(origin, reason: Vec<u8>, who: T::AccountId) {
			let finder = ensure_signed(origin)?;

			const MAX_SENSIBLE_REASON_LENGTH: usize = 16384;
			ensure!(reason.len() <= MAX_SENSIBLE_REASON_LENGTH, Error::<T>::ReasonTooBig);

			let reason_hash = T::Hashing::hash(&reason[..]);
			ensure!(!Reasons::<T>::contains_key(&reason_hash), Error::<T>::AlreadyKnown);
			let hash = T::Hashing::hash_of(&(&reason_hash, &who));
			ensure!(!Tips::<T>::contains_key(&hash), Error::<T>::AlreadyKnown);

			let deposit = T::TipReportDepositBase::get()
				+ T::TipReportDepositPerByte::get() * (reason.len() as u32).into();
			T::Currency::reserve(&finder, deposit)?;

			Reasons::<T>::insert(&reason_hash, &reason);
			let finder = Some((finder, deposit));
			let tip = OpenTip { reason: reason_hash, who, finder, closes: None, tips: vec![] };
			Tips::<T>::insert(&hash, tip);
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
		/// - `O(T)`
		/// - One balance operation.
		/// - Two storage removals (one read, codec `O(T)`).
		/// - One event.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn retract_tip(origin, hash: T::Hash) {
			let who = ensure_signed(origin)?;
			let tip = Tips::<T>::get(&hash).ok_or(Error::<T>::UnknownTip)?;
			let (finder, deposit) = tip.finder.ok_or(Error::<T>::NotFinder)?;
			ensure!(finder == who, Error::<T>::NotFinder);

			Reasons::<T>::remove(&tip.reason);
			Tips::<T>::remove(&hash);
			let _ = T::Currency::unreserve(&who, deposit);
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
		/// - `O(R + T)` where `R` length of `reason`, `T` is the number of tippers. `T` is
		///   naturally capped as a membership set, `R` is limited through transaction-size.
		/// - Two storage insertions (codecs `O(R)`, `O(T)`), one read `O(1)`.
		/// - One event.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(150_000)]
		fn tip_new(origin, reason: Vec<u8>, who: T::AccountId, tip_value: BalanceOf<T>) {
			let tipper = ensure_signed(origin)?;
			ensure!(T::Tippers::contains(&tipper), BadOrigin);
			let reason_hash = T::Hashing::hash(&reason[..]);
			ensure!(!Reasons::<T>::contains_key(&reason_hash), Error::<T>::AlreadyKnown);
			let hash = T::Hashing::hash_of(&(&reason_hash, &who));

			Reasons::<T>::insert(&reason_hash, &reason);
			Self::deposit_event(RawEvent::NewTip(hash.clone()));
			let tips = vec![(tipper, tip_value)];
			let tip = OpenTip { reason: reason_hash, who, finder: None, closes: None, tips };
			Tips::<T>::insert(&hash, tip);
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
		/// - `O(T)`
		/// - One storage mutation (codec `O(T)`), one storage read `O(1)`.
		/// - Up to one event.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn tip(origin, hash: T::Hash, tip_value: BalanceOf<T>) {
			let tipper = ensure_signed(origin)?;
			ensure!(T::Tippers::contains(&tipper), BadOrigin);

			let mut tip = Tips::<T>::get(hash).ok_or(Error::<T>::UnknownTip)?;
			if Self::insert_tip_and_check_closing(&mut tip, tipper, tip_value) {
				Self::deposit_event(RawEvent::TipClosing(hash.clone()));
			}
			Tips::<T>::insert(&hash, tip);
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
		/// - `O(T)`
		/// - One storage retrieval (codec `O(T)`) and two removals.
		/// - Up to three balance operations.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn close_tip(origin, hash: T::Hash) {
			ensure_signed(origin)?;

			let tip = Tips::<T>::get(hash).ok_or(Error::<T>::UnknownTip)?;
			let n = tip.closes.as_ref().ok_or(Error::<T>::StillOpen)?;
			ensure!(system::Module::<T>::block_number() >= *n, Error::<T>::Premature);
			// closed.
			Reasons::<T>::remove(&tip.reason);
			Tips::<T>::remove(hash);
			Self::payout_tip(tip);
		}

		fn on_finalize(n: T::BlockNumber) {
			// Check to see if we should spend some funds!
			if (n % T::SpendPeriod::get()).is_zero() {
				Self::spend_funds();
			}
		}
	}
}

impl<T: Trait> Module<T> {
	// Add public immutables and private mutables.

	/// The account ID of the treasury pot.
	///
	/// This actually does computation. If you need to keep using it, then make sure you cache the
	/// value and only call this once.
	pub fn account_id() -> T::AccountId {
		MODULE_ID.into_account()
	}

	/// The needed bond for a proposal whose spend is `value`.
	fn calculate_bond(value: BalanceOf<T>) -> BalanceOf<T> {
		T::ProposalBondMinimum::get().max(T::ProposalBond::get() * value)
	}

	/// Given a mutable reference to an `OpenTip`, insert the tip into it and check whether it
	/// closes, if so, then deposit the relevant event and set closing accordingly.
	///
	/// `O(T)` and one storage access.
	fn insert_tip_and_check_closing(
		tip: &mut OpenTip<T::AccountId, BalanceOf<T>, T::BlockNumber, T::Hash>,
		tipper: T::AccountId,
		tip_value: BalanceOf<T>,
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
	fn retain_active_tips(tips: &mut Vec<(T::AccountId, BalanceOf<T>)>) {
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
	fn payout_tip(tip: OpenTip<T::AccountId, BalanceOf<T>, T::BlockNumber, T::Hash>) {
		let mut tips = tip.tips;
		Self::retain_active_tips(&mut tips);
		tips.sort_by_key(|i| i.1);
		let treasury = Self::account_id();
		let max_payout = T::Currency::free_balance(&treasury);
		let mut payout = tips[tips.len() / 2].1.min(max_payout);
		if let Some((finder, deposit)) = tip.finder {
			let _ = T::Currency::unreserve(&finder, deposit);
			if finder != tip.who {
				// pay out the finder's fee.
				let finders_fee = T::TipFindersFee::get() * payout;
				payout -= finders_fee;
				// this should go through given we checked it's at most the free balance, but still
				// we only make a best-effort.
				let _ = T::Currency::transfer(&treasury, &finder, finders_fee, AllowDeath);
			}
		}
		// same as above: best-effort only.
		let _ = T::Currency::transfer(&treasury, &tip.who, payout, AllowDeath);
	}

	// Spend some money!
	fn spend_funds() {
		let mut budget_remaining = Self::pot();
		Self::deposit_event(RawEvent::Spending(budget_remaining));

		let mut missed_any = false;
		let mut imbalance = <PositiveImbalanceOf<T>>::zero();
		Approvals::mutate(|v| {
			v.retain(|&index| {
				// Should always be true, but shouldn't panic if false or we're screwed.
				if let Some(p) = Self::proposals(index) {
					if p.value <= budget_remaining {
						budget_remaining -= p.value;
						<Proposals<T>>::remove(index);

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
		});

		if !missed_any {
			// burn some proportion of the remaining budget if we run a surplus.
			let burn = (T::Burn::get() * budget_remaining).min(budget_remaining);
			budget_remaining -= burn;
			imbalance.subsume(T::Currency::burn(burn));
			Self::deposit_event(RawEvent::Burnt(burn))
		}

		// Must never be an error, but better to be safe.
		// proof: budget_remaining is account free balance minus ED;
		// Thus we can't spend more than account free balance minus ED;
		// Thus account is kept alive; qed;
		if let Err(problem) = T::Currency::settle(
			&Self::account_id(),
			imbalance,
			WithdrawReason::Transfer.into(),
			ExistenceRequirement::KeepAlive
		) {
			print("Inconsistent state - couldn't settle imbalance for funds spent by treasury");
			// Nothing else to do here.
			drop(problem);
		}

		Self::deposit_event(RawEvent::Rollover(budget_remaining));
	}

	/// Return the amount of money in the pot.
	// The existential deposit is not part of the pot so treasury account never gets deleted.
	fn pot() -> BalanceOf<T> {
		T::Currency::free_balance(&Self::account_id())
			// Must never be less than 0 but better be safe.
			.saturating_sub(T::Currency::minimum_balance())
	}
}

impl<T: Trait> OnUnbalanced<NegativeImbalanceOf<T>> for Module<T> {
	fn on_nonzero_unbalanced(amount: NegativeImbalanceOf<T>) {
		let numeric_amount = amount.peek();

		// Must resolve into existing but better to be safe.
		let _ = T::Currency::resolve_creating(&Self::account_id(), amount);

		Self::deposit_event(RawEvent::Deposit(numeric_amount));
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use frame_support::{assert_noop, assert_ok, impl_outer_origin, parameter_types, weights::Weight};
	use frame_support::traits::Contains;
	use sp_core::H256;
	use sp_runtime::{
		Perbill,
		testing::Header,
		traits::{BlakeTwo256, OnFinalize, IdentityLookup, BadOrigin},
	};

	impl_outer_origin! {
		pub enum Origin for Test  where system = frame_system {}
	}

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
		type Call = ();
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type AvailableBlockRatio = AvailableBlockRatio;
		type MaximumBlockLength = MaximumBlockLength;
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
		type Event = ();
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type AccountStore = System;
	}
	pub struct TenToFourteen;
	impl Contains<u64> for TenToFourteen {
		fn contains(n: &u64) -> bool {
			*n >= 10 && *n <= 14
		}
		fn sorted_members() -> Vec<u64> {
			vec![10, 11, 12, 13, 14]
		}
	}
	parameter_types! {
		pub const ProposalBond: Permill = Permill::from_percent(5);
		pub const ProposalBondMinimum: u64 = 1;
		pub const SpendPeriod: u64 = 2;
		pub const Burn: Permill = Permill::from_percent(50);
		pub const TipCountdown: u64 = 1;
		pub const TipFindersFee: Percent = Percent::from_percent(20);
		pub const TipReportDepositBase: u64 = 1;
		pub const TipReportDepositPerByte: u64 = 1;
	}
	impl Trait for Test {
		type Currency = pallet_balances::Module<Test>;
		type ApproveOrigin = frame_system::EnsureRoot<u64>;
		type RejectOrigin = frame_system::EnsureRoot<u64>;
		type Tippers = TenToFourteen;
		type TipCountdown = TipCountdown;
		type TipFindersFee = TipFindersFee;
		type TipReportDepositBase = TipReportDepositBase;
		type TipReportDepositPerByte = TipReportDepositPerByte;
		type Event = ();
		type ProposalRejection = ();
		type ProposalBond = ProposalBond;
		type ProposalBondMinimum = ProposalBondMinimum;
		type SpendPeriod = SpendPeriod;
		type Burn = Burn;
	}
	type System = frame_system::Module<Test>;
	type Balances = pallet_balances::Module<Test>;
	type Treasury = Module<Test>;

	fn new_test_ext() -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		pallet_balances::GenesisConfig::<Test>{
			// Total issuance will be 200 with treasury account initialized at ED.
			balances: vec![(0, 100), (1, 98), (2, 1)],
		}.assimilate_storage(&mut t).unwrap();
		GenesisConfig::default().assimilate_storage::<Test>(&mut t).unwrap();
		t.into()
	}

	#[test]
	fn genesis_config_works() {
		new_test_ext().execute_with(|| {
			assert_eq!(Treasury::pot(), 0);
			assert_eq!(Treasury::proposal_count(), 0);
		});
	}

	fn tip_hash() -> H256 {
		BlakeTwo256::hash_of(&(BlakeTwo256::hash(b"awesome.dot"), 3u64))
	}

	#[test]
	fn tip_new_cannot_be_used_twice() {
		new_test_ext().execute_with(|| {
			Balances::make_free_balance_be(&Treasury::account_id(), 101);
			assert_ok!(Treasury::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 10));
			assert_noop!(
				Treasury::tip_new(Origin::signed(11), b"awesome.dot".to_vec(), 3, 10),
				Error::<Test>::AlreadyKnown
			);
		});
	}

	#[test]
	fn report_awesome_and_tip_works() {
		new_test_ext().execute_with(|| {
			Balances::make_free_balance_be(&Treasury::account_id(), 101);
			assert_ok!(Treasury::report_awesome(Origin::signed(0), b"awesome.dot".to_vec(), 3));
			assert_eq!(Balances::reserved_balance(0), 12);
			assert_eq!(Balances::free_balance(0), 88);

			// other reports don't count.
			assert_noop!(
				Treasury::report_awesome(Origin::signed(1), b"awesome.dot".to_vec(), 3),
				Error::<Test>::AlreadyKnown
			);

			let h = tip_hash();
			assert_ok!(Treasury::tip(Origin::signed(10), h.clone(), 10));
			assert_ok!(Treasury::tip(Origin::signed(11), h.clone(), 10));
			assert_ok!(Treasury::tip(Origin::signed(12), h.clone(), 10));
			assert_noop!(Treasury::tip(Origin::signed(9), h.clone(), 10), BadOrigin);
			System::set_block_number(2);
			assert_ok!(Treasury::close_tip(Origin::signed(100), h.into()));
			assert_eq!(Balances::reserved_balance(0), 0);
			assert_eq!(Balances::free_balance(0), 102);
			assert_eq!(Balances::free_balance(3), 8);
		});
	}

	#[test]
	fn report_awesome_from_beneficiary_and_tip_works() {
		new_test_ext().execute_with(|| {
			Balances::make_free_balance_be(&Treasury::account_id(), 101);
			assert_ok!(Treasury::report_awesome(Origin::signed(0), b"awesome.dot".to_vec(), 0));
			assert_eq!(Balances::reserved_balance(0), 12);
			assert_eq!(Balances::free_balance(0), 88);
			let h = BlakeTwo256::hash_of(&(BlakeTwo256::hash(b"awesome.dot"), 0u64));
			assert_ok!(Treasury::tip(Origin::signed(10), h.clone(), 10));
			assert_ok!(Treasury::tip(Origin::signed(11), h.clone(), 10));
			assert_ok!(Treasury::tip(Origin::signed(12), h.clone(), 10));
			System::set_block_number(2);
			assert_ok!(Treasury::close_tip(Origin::signed(100), h.into()));
			assert_eq!(Balances::reserved_balance(0), 0);
			assert_eq!(Balances::free_balance(0), 110);
		});
	}

	#[test]
	fn close_tip_works() {
		new_test_ext().execute_with(|| {
			Balances::make_free_balance_be(&Treasury::account_id(), 101);
			assert_eq!(Treasury::pot(), 100);

			assert_ok!(Treasury::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 10));
			let h = tip_hash();
			assert_ok!(Treasury::tip(Origin::signed(11), h.clone(), 10));
			assert_noop!(Treasury::close_tip(Origin::signed(0), h.into()), Error::<Test>::StillOpen);

			assert_ok!(Treasury::tip(Origin::signed(12), h.clone(), 10));
			assert_noop!(Treasury::close_tip(Origin::signed(0), h.into()), Error::<Test>::Premature);

			System::set_block_number(2);
			assert_noop!(Treasury::close_tip(Origin::NONE, h.into()), BadOrigin);
			assert_ok!(Treasury::close_tip(Origin::signed(0), h.into()));
			assert_eq!(Balances::free_balance(3), 10);

			assert_noop!(Treasury::close_tip(Origin::signed(100), h.into()), Error::<Test>::UnknownTip);
		});
	}

	#[test]
	fn retract_tip_works() {
		new_test_ext().execute_with(|| {
			Balances::make_free_balance_be(&Treasury::account_id(), 101);
			assert_ok!(Treasury::report_awesome(Origin::signed(0), b"awesome.dot".to_vec(), 3));
			let h = tip_hash();
			assert_ok!(Treasury::tip(Origin::signed(10), h.clone(), 10));
			assert_ok!(Treasury::tip(Origin::signed(11), h.clone(), 10));
			assert_ok!(Treasury::tip(Origin::signed(12), h.clone(), 10));
			assert_noop!(Treasury::retract_tip(Origin::signed(10), h.clone()), Error::<Test>::NotFinder);
			assert_ok!(Treasury::retract_tip(Origin::signed(0), h.clone()));
			System::set_block_number(2);
			assert_noop!(Treasury::close_tip(Origin::signed(0), h.into()), Error::<Test>::UnknownTip);
		});
	}

	#[test]
	fn tip_median_calculation_works() {
		new_test_ext().execute_with(|| {
			Balances::make_free_balance_be(&Treasury::account_id(), 101);
			assert_ok!(Treasury::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 0));
			let h = tip_hash();
			assert_ok!(Treasury::tip(Origin::signed(11), h.clone(), 10));
			assert_ok!(Treasury::tip(Origin::signed(12), h.clone(), 1000000));
			System::set_block_number(2);
			assert_ok!(Treasury::close_tip(Origin::signed(0), h.into()));
			assert_eq!(Balances::free_balance(3), 10);
		});
	}

	#[test]
	fn tip_changing_works() {
		new_test_ext().execute_with(|| {
			Balances::make_free_balance_be(&Treasury::account_id(), 101);
			assert_ok!(Treasury::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 10000));
			let h = tip_hash();
			assert_ok!(Treasury::tip(Origin::signed(11), h.clone(), 10000));
			assert_ok!(Treasury::tip(Origin::signed(12), h.clone(), 10000));
			assert_ok!(Treasury::tip(Origin::signed(13), h.clone(), 0));
			assert_ok!(Treasury::tip(Origin::signed(14), h.clone(), 0));
			assert_ok!(Treasury::tip(Origin::signed(12), h.clone(), 1000));
			assert_ok!(Treasury::tip(Origin::signed(11), h.clone(), 100));
			assert_ok!(Treasury::tip(Origin::signed(10), h.clone(), 10));
			System::set_block_number(2);
			assert_ok!(Treasury::close_tip(Origin::signed(0), h.into()));
			assert_eq!(Balances::free_balance(3), 10);
		});
	}

	#[test]
	fn minting_works() {
		new_test_ext().execute_with(|| {
			// Check that accumulate works when we have Some value in Dummy already.
			Balances::make_free_balance_be(&Treasury::account_id(), 101);
			assert_eq!(Treasury::pot(), 100);
		});
	}

	#[test]
	fn spend_proposal_takes_min_deposit() {
		new_test_ext().execute_with(|| {
			assert_ok!(Treasury::propose_spend(Origin::signed(0), 1, 3));
			assert_eq!(Balances::free_balance(0), 99);
			assert_eq!(Balances::reserved_balance(0), 1);
		});
	}

	#[test]
	fn spend_proposal_takes_proportional_deposit() {
		new_test_ext().execute_with(|| {
			assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
			assert_eq!(Balances::free_balance(0), 95);
			assert_eq!(Balances::reserved_balance(0), 5);
		});
	}

	#[test]
	fn spend_proposal_fails_when_proposer_poor() {
		new_test_ext().execute_with(|| {
			assert_noop!(
				Treasury::propose_spend(Origin::signed(2), 100, 3),
				Error::<Test>::InsufficientProposersBalance,
			);
		});
	}

	#[test]
	fn accepted_spend_proposal_ignored_outside_spend_period() {
		new_test_ext().execute_with(|| {
			Balances::make_free_balance_be(&Treasury::account_id(), 101);

			assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
			assert_ok!(Treasury::approve_proposal(Origin::ROOT, 0));

			<Treasury as OnFinalize<u64>>::on_finalize(1);
			assert_eq!(Balances::free_balance(3), 0);
			assert_eq!(Treasury::pot(), 100);
		});
	}

	#[test]
	fn unused_pot_should_diminish() {
		new_test_ext().execute_with(|| {
			let init_total_issuance = Balances::total_issuance();
			Balances::make_free_balance_be(&Treasury::account_id(), 101);
			assert_eq!(Balances::total_issuance(), init_total_issuance + 100);

			<Treasury as OnFinalize<u64>>::on_finalize(2);
			assert_eq!(Treasury::pot(), 50);
			assert_eq!(Balances::total_issuance(), init_total_issuance + 50);
		});
	}

	#[test]
	fn rejected_spend_proposal_ignored_on_spend_period() {
		new_test_ext().execute_with(|| {
			Balances::make_free_balance_be(&Treasury::account_id(), 101);

			assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
			assert_ok!(Treasury::reject_proposal(Origin::ROOT, 0));

			<Treasury as OnFinalize<u64>>::on_finalize(2);
			assert_eq!(Balances::free_balance(3), 0);
			assert_eq!(Treasury::pot(), 50);
		});
	}

	#[test]
	fn reject_already_rejected_spend_proposal_fails() {
		new_test_ext().execute_with(|| {
			Balances::make_free_balance_be(&Treasury::account_id(), 101);

			assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
			assert_ok!(Treasury::reject_proposal(Origin::ROOT, 0));
			assert_noop!(Treasury::reject_proposal(Origin::ROOT, 0), Error::<Test>::InvalidProposalIndex);
		});
	}

	#[test]
	fn reject_non_existent_spend_proposal_fails() {
		new_test_ext().execute_with(|| {
			assert_noop!(Treasury::reject_proposal(Origin::ROOT, 0), Error::<Test>::InvalidProposalIndex);
		});
	}

	#[test]
	fn accept_non_existent_spend_proposal_fails() {
		new_test_ext().execute_with(|| {
			assert_noop!(Treasury::approve_proposal(Origin::ROOT, 0), Error::<Test>::InvalidProposalIndex);
		});
	}

	#[test]
	fn accept_already_rejected_spend_proposal_fails() {
		new_test_ext().execute_with(|| {
			Balances::make_free_balance_be(&Treasury::account_id(), 101);

			assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
			assert_ok!(Treasury::reject_proposal(Origin::ROOT, 0));
			assert_noop!(Treasury::approve_proposal(Origin::ROOT, 0), Error::<Test>::InvalidProposalIndex);
		});
	}

	#[test]
	fn accepted_spend_proposal_enacted_on_spend_period() {
		new_test_ext().execute_with(|| {
			Balances::make_free_balance_be(&Treasury::account_id(), 101);
			assert_eq!(Treasury::pot(), 100);

			assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
			assert_ok!(Treasury::approve_proposal(Origin::ROOT, 0));

			<Treasury as OnFinalize<u64>>::on_finalize(2);
			assert_eq!(Balances::free_balance(3), 100);
			assert_eq!(Treasury::pot(), 0);
		});
	}

	#[test]
	fn pot_underflow_should_not_diminish() {
		new_test_ext().execute_with(|| {
			Balances::make_free_balance_be(&Treasury::account_id(), 101);
			assert_eq!(Treasury::pot(), 100);

			assert_ok!(Treasury::propose_spend(Origin::signed(0), 150, 3));
			assert_ok!(Treasury::approve_proposal(Origin::ROOT, 0));

			<Treasury as OnFinalize<u64>>::on_finalize(2);
			assert_eq!(Treasury::pot(), 100); // Pot hasn't changed

			let _ = Balances::deposit_into_existing(&Treasury::account_id(), 100).unwrap();
			<Treasury as OnFinalize<u64>>::on_finalize(4);
			assert_eq!(Balances::free_balance(3), 150); // Fund has been spent
			assert_eq!(Treasury::pot(), 25); // Pot has finally changed
		});
	}

	// Treasury account doesn't get deleted if amount approved to spend is all its free balance.
	// i.e. pot should not include existential deposit needed for account survival.
	#[test]
	fn treasury_account_doesnt_get_deleted() {
		new_test_ext().execute_with(|| {
			Balances::make_free_balance_be(&Treasury::account_id(), 101);
			assert_eq!(Treasury::pot(), 100);
			let treasury_balance = Balances::free_balance(&Treasury::account_id());

			assert_ok!(Treasury::propose_spend(Origin::signed(0), treasury_balance, 3));
			assert_ok!(Treasury::approve_proposal(Origin::ROOT, 0));

			<Treasury as OnFinalize<u64>>::on_finalize(2);
			assert_eq!(Treasury::pot(), 100); // Pot hasn't changed

			assert_ok!(Treasury::propose_spend(Origin::signed(0), Treasury::pot(), 3));
			assert_ok!(Treasury::approve_proposal(Origin::ROOT, 1));

			<Treasury as OnFinalize<u64>>::on_finalize(4);
			assert_eq!(Treasury::pot(), 0); // Pot is emptied
			assert_eq!(Balances::free_balance(Treasury::account_id()), 1); // but the account is still there
		});
	}

	// In case treasury account is not existing then it works fine.
	// This is useful for chain that will just update runtime.
	#[test]
	fn inexistent_account_works() {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		pallet_balances::GenesisConfig::<Test>{
			balances: vec![(0, 100), (1, 99), (2, 1)],
		}.assimilate_storage(&mut t).unwrap();
		// Treasury genesis config is not build thus treasury account does not exist
		let mut t: sp_io::TestExternalities = t.into();

		t.execute_with(|| {
			assert_eq!(Balances::free_balance(Treasury::account_id()), 0); // Account does not exist
			assert_eq!(Treasury::pot(), 0); // Pot is empty

			assert_ok!(Treasury::propose_spend(Origin::signed(0), 99, 3));
			assert_ok!(Treasury::approve_proposal(Origin::ROOT, 0));
			assert_ok!(Treasury::propose_spend(Origin::signed(0), 1, 3));
			assert_ok!(Treasury::approve_proposal(Origin::ROOT, 1));
			<Treasury as OnFinalize<u64>>::on_finalize(2);
			assert_eq!(Treasury::pot(), 0); // Pot hasn't changed
			assert_eq!(Balances::free_balance(3), 0); // Balance of `3` hasn't changed

			Balances::make_free_balance_be(&Treasury::account_id(), 100);
			assert_eq!(Treasury::pot(), 99); // Pot now contains funds
			assert_eq!(Balances::free_balance(Treasury::account_id()), 100); // Account does exist

			<Treasury as OnFinalize<u64>>::on_finalize(4);

			assert_eq!(Treasury::pot(), 0); // Pot has changed
			assert_eq!(Balances::free_balance(3), 99); // Balance of `3` has changed
		});
	}
}
