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

//! # Treasury Pallet
//!
//! The Treasury pallet provides a "pot" of funds that can be managed by stakeholders in the system
//! and a structure for making spending proposals from this pot.
//!
//! - [`Config`]
//! - [`Call`]
//!
//! ## Overview
//!
//! The Treasury Pallet itself provides the pot to store funds, and a means for stakeholders to
//! propose, approve, and deny expenditures. The chain will need to provide a method (e.g.
//! inflation, fees) for collecting funds.
//!
//! By way of example, the Council could vote to fund the Treasury with a portion of the block
//! reward and use the funds to pay developers.
//!
//!
//! ### Terminology
//!
//! - **Proposal:** A suggestion to allocate funds from the pot to a beneficiary.
//! - **Beneficiary:** An account who will receive the funds from a proposal iff the proposal is
//!   approved.
//! - **Deposit:** Funds that a proposer must lock when making a proposal. The deposit will be
//!   returned or slashed if the proposal is approved or rejected respectively.
//! - **Pot:** Unspent funds accumulated by the treasury pallet.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! General spending/proposal protocol:
//! - `propose_spend` - Make a spending proposal and stake the required deposit.
//! - `reject_proposal` - Reject a proposal, slashing the deposit.
//! - `approve_proposal` - Accept the proposal, returning the deposit.
//! - `remove_approval` - Remove an approval, the deposit will no longer be returned.
//!
//! ## GenesisConfig
//!
//! The Treasury pallet depends on the [`GenesisConfig`].

#![cfg_attr(not(feature = "std"), no_std)]

mod benchmarking;
#[cfg(test)]
mod tests;
pub mod weights;

use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	print,
	traits::{
		fungible::{self, HandleImbalanceDrop, *},
		fungibles::{
			self, Balanced as FunsBalanced, BalancedHold as FunsBalancedHold, Credit, Debt,
			Inspect as FunsInspect, Mutate as FunsMutate, MutateHold as FunsMutateHold,
			Unbalanced as FunsUnbalanced, *,
		},
		tokens::{AssetId, Precision, Preservation},
		Get,
	},
	weights::Weight,
	PalletId,
};
pub use pallet::*;
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{AccountIdConversion, StaticLookup},
	DispatchError, Permill, RuntimeDebug,
};
use sp_std::prelude::*;
pub use weights::WeightInfo;

pub type BalanceOf<T, I = ()> = <<T as Config<I>>::Assets as fungibles::Inspect<
	<T as frame_system::Config>::AccountId,
>>::Balance;

pub type DebtOf<T, I = ()> = Debt<<T as frame_system::Config>::AccountId, <T as Config<I>>::Assets>;
pub type CreditOf<T, I = ()> =
	Credit<<T as frame_system::Config>::AccountId, <T as Config<I>>::Assets>;
type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;

/// A trait to allow the Treasury Pallet to spend it's funds for other purposes.
/// There is an expectation that the implementer of this trait will correctly manage
/// the mutable variables passed to it:
/// * `budget_remaining`: How much available funds that can be spent by the treasury. As funds are
///   spent, you must correctly deduct from this value.
/// * `imbalance`: Any imbalances that you create should be subsumed in here to maximize efficiency
///   of updating the total issuance. (i.e. `deposit_creating`)
/// * `total_weight`: Track any weight that your `spend_fund` implementation uses by updating this
///   value.
/// * `missed_any`: If there were items that you want to spend on, but there were not enough funds,
///   mark this value as `true`. This will prevent the treasury from burning the excess funds.
// #[impl_trait_for_tuples::impl_for_tuples(30)]
pub trait SpendFunds<T: Config<I>, I: 'static = ()> {
	fn spend_funds(
		budget_remaining: &mut Vec<(T::AssetId, BalanceOf<T, I>)>,
		// imbalance: &mut DebtOf<T, I>,
		total_weight: &mut Weight,
		missed_any: &mut bool,
	) {
	}
}

/// An index of a proposal. Just a `u32`.
pub type ProposalIndex = u32;

/// A spending proposal.
#[cfg_attr(feature = "std", derive(serde::Serialize, serde::Deserialize))]
#[derive(Encode, Decode, Clone, PartialEq, Eq, MaxEncodedLen, RuntimeDebug, TypeInfo)]
pub struct Proposal<AccountId, AssetId, Balance> {
	/// The account proposing it.
	proposer: AccountId,
	/// The (total) amount that should be paid if the proposal is accepted.
	value: Balance,
	/// The account to whom the payment should be made if the proposal is accepted.
	beneficiary: AccountId,
	/// The amount held on deposit (reserved) for making this proposal.
	bond: Balance,
	/// The asset which we are refering to.
	asset_id: AssetId,
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T, I = ()>(PhantomData<(T, I)>);

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		type AssetId: AssetId + PartialOrd;

		type Assets: FunsInspect<Self::AccountId, AssetId = Self::AssetId>
			+ FunsMutate<Self::AccountId>
			+ FunsUnbalanced<Self::AccountId>
			+ FunsBalanced<Self::AccountId>
			+ FunsMutateHold<Self::AccountId>
			+ FunsBalancedHold<Self::AccountId>;

		/// The name for the reserve ID.
		#[pallet::constant]
		type HoldReason: Get<<Self::Assets as fungibles::InspectHold<Self::AccountId>>::Reason>;

		/// The name for the reserve ID.
		#[pallet::constant]
		type HoldAssetReason: Get<<Self::Assets as fungibles::InspectHold<Self::AccountId>>::Reason>;

		/// Origin from which approvals must come.
		type ApproveOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// Origin from which rejections must come.
		type RejectOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// The overarching event type.
		type RuntimeEvent: From<Event<Self, I>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Handler for the unbalanced decrease when slashing for a rejected proposal or bounty.
		type OnSlash: HandleImbalanceDrop<CreditOf<Self, I>>;

		/// Fraction of a proposal's value that should be bonded in order to place the proposal.
		/// An accepted proposal gets these back. A rejected proposal does not.
		#[pallet::constant]
		type ProposalBond: Get<Permill>;

		/// Minimum amount of funds that should be placed in a deposit for making a proposal.
		#[pallet::constant]
		type ProposalBondMinimum: Get<BalanceOf<Self, I>>;

		/// Maximum amount of funds that should be placed in a deposit for making a proposal.
		#[pallet::constant]
		type ProposalBondMaximum: Get<Option<BalanceOf<Self, I>>>;

		/// Period between successive spends.
		#[pallet::constant]
		type SpendPeriod: Get<Self::BlockNumber>;

		/// Percentage of spare funds (if any) that are burnt per spend period.
		#[pallet::constant]
		type Burn: Get<Permill>;

		/// The treasury's pallet id, used for deriving its sovereign account ID.
		#[pallet::constant]
		type PalletId: Get<PalletId>;

		/// Handler for the unbalanced decrease when treasury funds are burned.
		type BurnDestination: HandleImbalanceDrop<CreditOf<Self, I>>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;

		/// Runtime hooks to external pallet using treasury to compute spend funds.
		type SpendFunds: SpendFunds<Self, I>;

		/// The maximum number of approvals that can wait in the spending queue.
		///
		/// NOTE: This parameter is also used within the Bounties Pallet extension if enabled.
		#[pallet::constant]
		type MaxApprovals: Get<u32>;

		/// The origin required for approving spends from the treasury outside of the proposal
		/// process. The `Success` value is the maximum amount that this origin is allowed to
		/// spend at a time.
		type SpendOrigin: EnsureOrigin<Self::RuntimeOrigin, Success = BalanceOf<Self, I>>;
	}

	/// Number of proposals that have been made.
	#[pallet::storage]
	#[pallet::getter(fn proposal_count)]
	pub(crate) type ProposalCount<T, I = ()> = StorageValue<_, ProposalIndex, ValueQuery>;

	/// Proposals that have been made.
	#[pallet::storage]
	#[pallet::getter(fn proposals)]
	pub type Proposals<T: Config<I>, I: 'static = ()> = StorageMap<
		_,
		Twox64Concat,
		ProposalIndex,
		Proposal<T::AccountId, T::AssetId, BalanceOf<T, I>>,
		OptionQuery,
	>;

	/// The amount which has been reported as inactive to Currency.
	#[pallet::storage]
	pub type Deactivated<T: Config<I>, I: 'static = ()> =
		StorageValue<_, BalanceOf<T, I>, ValueQuery>;

	/// Proposal indices that have been approved but not yet awarded.
	#[pallet::storage]
	#[pallet::getter(fn approvals)]
	pub type Approvals<T: Config<I>, I: 'static = ()> =
		StorageValue<_, BoundedVec<ProposalIndex, T::MaxApprovals>, ValueQuery>;

	#[pallet::genesis_config]
	pub struct GenesisConfig;

	#[cfg(feature = "std")]
	impl Default for GenesisConfig {
		fn default() -> Self {
			Self
		}
	}

	#[cfg(feature = "std")]
	impl GenesisConfig {
		/// Direct implementation of `GenesisBuild::assimilate_storage`.
		#[deprecated(
			note = "use `<GensisConfig<T, I> as GenesisBuild<T, I>>::assimilate_storage` instead"
		)]
		pub fn assimilate_storage<T: Config<I>, I: 'static>(
			&self,
			storage: &mut sp_runtime::Storage,
		) -> Result<(), String> {
			<Self as GenesisBuild<T, I>>::assimilate_storage(self, storage)
		}
	}

	#[pallet::genesis_build]
	impl<T: Config<I>, I: 'static> GenesisBuild<T, I> for GenesisConfig {
		fn build(&self) {
			// // Create Treasury account
			// let account_id = <Pallet<T, I>>::account_id();
			// let min = <T::Assets as fungibles::Inspect<T::AccountId>>::minimum_balance();
			// if T::Currency::balance(&account_id) < min {
			// 	let _ = T::Currency::set_balance(&account_id, min);
			// }
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// We have ended a spend period and will now allocate funds.
		Spending { budget_remaining: BalanceOf<T, I> },
		/// Some of our funds have been burnt.
		Burnt { burnt_funds: BalanceOf<T, I> },
		/// Spending has finished; this is the amount that rolls over until next spend.
		Rollover { rollover_balances: Vec<(T::AssetId, BalanceOf<T, I>)> },
		/// Some funds have been deposited.
		Deposit { value: BalanceOf<T, I> },
		/// A new spend proposal has been approved.
		SpendApproved {
			proposal_index: ProposalIndex,
			amount: BalanceOf<T, I>,
			beneficiary: T::AccountId,
		},
		/// The inactive funds of the pallet have been updated.
		UpdatedInactive { reactivated: BalanceOf<T, I>, deactivated: BalanceOf<T, I> },
	}

	/// Error for the treasury pallet.
	#[pallet::error]
	pub enum Error<T, I = ()> {
		/// Proposer's balance is too low.
		InsufficientProposersBalance,
		/// No proposal or bounty at that index.
		InvalidIndex,
		/// Too many approvals in the queue.
		TooManyApprovals,
		/// The spend origin is valid but the amount it is allowed to spend is lower than the
		/// amount to be spent.
		InsufficientPermission,
		/// Proposal has not been approved.
		ProposalNotApproved,
		/// Invalid asset_id
		InvalidAssetId,
		/// Insufficient balance in the pot for given asset.
		InsufficientAssetBalance,
	}

	#[pallet::hooks]
	impl<T: Config<I>, I: 'static> Hooks<BlockNumberFor<T>> for Pallet<T, I> {
		/// ## Complexity
		/// - `O(A)` where `A` is the number of approvals
		fn on_initialize(n: T::BlockNumber) -> Weight {
			// let pot = Self::pot();
			// let deactivated = Deactivated::<T, I>::get();
			// if pot != deactivated {
			// 	<T::Currency as fungible::Unbalanced<T::AccountId>>::reactivate(deactivated);
			// 	<T::Currency as fungible::Unbalanced<T::AccountId>>::deactivate(pot);
			// 	Deactivated::<T, I>::put(&pot);
			// 	Self::deposit_event(Event::<T, I>::UpdatedInactive {
			// 		reactivated: deactivated,
			// 		deactivated: pot,
			// 	});
			// }

			// // Check to see if we should spend some funds!
			// if (n % T::SpendPeriod::get()).is_zero() {
			// 	Self::spend_funds()
			// } else {
			// 	Weight::zero()
			// }
			Weight::zero()
		}
	}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Propose and approve a spend of treasury funds.
		///
		/// - `origin`: Must be `SpendOrigin` with the `Success` value being at least `amount`.
		/// - `asset`: An identifier for the given asset which we're spending. It could refer to the
		/// native asset or an actual asset.
		/// - `amount`: The amount to be transferred from the treasury to the `beneficiary`.
		/// - `beneficiary`: The destination account for the transfer.
		///
		/// NOTE: For record-keeping purposes, the proposer is deemed to be equivalent to the
		/// beneficiary.
		#[pallet::call_index(3)]
		#[pallet::weight(T::WeightInfo::spend())]
		pub fn spend(
			origin: OriginFor<T>,
			asset_id: T::AssetId,
			#[pallet::compact] amount: BalanceOf<T, I>,
			beneficiary: AccountIdLookupOf<T>,
		) -> DispatchResult {
			let max_amount = T::SpendOrigin::ensure_origin(origin)?;
			let beneficiary = T::Lookup::lookup(beneficiary)?;

			// ensure!(amount <= max_amount, Error::<T, I>::InsufficientPermission);
			let proposal_index = Self::proposal_count();
			Approvals::<T, I>::try_append(proposal_index)
				.map_err(|_| Error::<T, I>::TooManyApprovals)?;

			let proposal = Proposal {
				proposer: beneficiary.clone(),
				value: amount,
				beneficiary: beneficiary.clone(),
				bond: amount,
				asset_id,
			};
			Proposals::<T, I>::insert(proposal_index, proposal);
			ProposalCount::<T, I>::put(proposal_index + 1);

			Self::deposit_event(Event::SpendApproved { proposal_index, amount, beneficiary });
			Ok(())
		}
	}
}

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	// Add public immutables and private mutables.

	/// The account ID of the treasury pot.
	///
	/// This actually does computation. If you need to keep using it, then make sure you cache the
	/// value and only call this once.
	pub fn account_id() -> T::AccountId {
		T::PalletId::get().into_account_truncating()
	}

	// /// The needed bond for a proposal whose spend is `value`.
	fn calculate_bond(value: BalanceOf<T, I>) -> BalanceOf<T, I> {
		let mut r = T::ProposalBondMinimum::get().max(T::ProposalBond::get() * value);
		if let Some(m) = T::ProposalBondMaximum::get() {
			r = r.min(m);
		}
		r
	}

	pub fn spend_funds() -> Weight {
		let mut total_weight = Weight::zero();
		let mut budgets_remaining = Self::pot();
		let account_id = Self::account_id();

		let mut missed_any = false;
		let proposals_len = Approvals::<T, I>::mutate(|v| {
			let proposals_approvals_len = v.len() as u32;
			v.retain(|&index| {
				if let Some(p) = Self::proposals(index) {
					if let Ok(_) = Self::process_proposal(p, &mut budgets_remaining) {
						return false
					}
				}
				missed_any = true;
				true
			});
			proposals_approvals_len
		});
		total_weight += T::WeightInfo::on_initialize_proposals(proposals_len);

		// Call Runtime hooks to external pallet using treasury to compute spend funds.
		T::SpendFunds::spend_funds(
			&mut budgets_remaining,
			// &mut imbalance,
			&mut total_weight,
			&mut missed_any,
		);

		if !missed_any {
			// burn some proportion of the remaining budget if we run a surplus.
			// TODO: how should we track burn configs? Is it per token?

			let burn_rate = T::Burn::get();
			for i in 1..budgets_remaining.len() {
				let (asset_id, budget_remaining) = budgets_remaining[i];
				let burn = (burn_rate * budget_remaining).min(budget_remaining);
				budgets_remaining[i] = (asset_id, budget_remaining - burn);

				let (debit, credit) =
					<T::Assets as fungibles::Balanced<T::AccountId>>::pair(asset_id, burn);
				T::BurnDestination::handle(credit);
				Self::deposit_event(Event::Burnt { burnt_funds: burn })
			}
		}

		// // Thus account is kept alive; qed;
		// if let Err(problem) = <T::Assets as fungibles::Balanced<T::AccountId>>::settle(
		// 	&account_id,
		// 	imbalance,
		// 	Preservation::Preserve,
		// ) {
		// 	print("Inconsistent state - couldn't settle imbalance for funds spent by treasury");
		// 	// Nothing else to do here.
		// 	drop(problem);
		// }
		Self::deposit_event(Event::Rollover { rollover_balances: budgets_remaining });

		total_weight
	}

	fn process_proposal(
		p: Proposal<T::AccountId, T::AssetId, BalanceOf<T, I>>,
		balances: &mut Vec<(T::AssetId, BalanceOf<T, I>)>,
	) -> Result<(), DispatchError> {
		let (asset_id, budget_remaining) = balances
			.iter()
			.find(|(asset_id, value)| *asset_id == p.asset_id)
			.ok_or(Error::<T, I>::InvalidAssetId)?;

		if *budget_remaining <= p.value {
			return Err(Error::<T, I>::InsufficientAssetBalance.into())
		}

		// return their deposit.
		let released_amount = T::Assets::release(
			p.asset_id,
			&T::HoldAssetReason::get(),
			&p.proposer,
			p.bond,
			Precision::Exact,
		);
		debug_assert!(released_amount.is_ok());

		// provide the allocation. Rely on the T::Assets::OnDropDebt to handle the resulting Debt.
		T::Assets::deposit(p.asset_id, &p.beneficiary, p.value, Precision::Exact)?;
		Ok(())
	}

	// /// Return the amount of money in the pot.
	// // The existential deposit is not part of the pot so treasury account never gets deleted.
	// pub fn pot() -> BalanceOf<T, I> {
	// 	T::Currency::reducible_balance(
	// 		&Self::account_id(),
	// 		Preservation::Protect,
	// 		Fortitude::Polite,
	// 	)
	// }
	pub fn pot() -> Vec<(T::AssetId, BalanceOf<T, I>)> {
		vec![]
	}
}

// impl<T: Config<I>, I: 'static> HandleImbalanceDrop<CreditOf<T, I>> for Pallet<T, I> {
// 	fn handle(amount: CreditOf<T, I>) {
// 		let numeric_amount = amount.peek();

// 		// Must resolve into existing but better to be safe.
// 		let _ = T::Currency::resolve(&Self::account_id(), amount);

// 		Self::deposit_event(Event::Deposit { value: numeric_amount });
// 	}
// }
