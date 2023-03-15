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
use scale_info::TypeInfo;

use codec::FullCodec;
use frame_support::{
	dispatch::fmt::Debug,
	traits::{
		tokens::{AssetId, Balance, BalanceConversion},
		Get,
	},
	weights::Weight,
	PalletId,
};
use sp_runtime::{
	traits::{CheckedAdd, Saturating, StaticLookup, Zero},
	Permill, RuntimeDebug,
};
use sp_std::{collections::btree_map::BTreeMap, prelude::*};

pub use pallet::*;
pub use weights::WeightInfo;

/// Status for making a payment via the `Pay::pay` trait function.
#[cfg_attr(feature = "std", derive(serde::Serialize, serde::Deserialize))]
#[derive(Encode, Decode, Eq, PartialEq, Clone, TypeInfo, MaxEncodedLen, RuntimeDebug)]
pub enum PaymentStatus {
	/// Payment is in progress. Nothing to report yet.
	InProgress,
	/// Payment status is unknowable. It will never be reported successful or failed.
	Unknown,
	/// Payment happened successfully.
	Success,
	/// Payment failed. It may safely be retried.
	Failure,
}

// TODO: Should be replaced with a version in frame_support
pub trait Pay {
	/// The type by which we measure units of the currency in which we make payments.
	type Balance: Balance;
	/// The type by which we identify the individuals to whom a payment may be made.
	type AccountId;
	/// An identifier given to an individual payment.
	type Id: FullCodec + MaxEncodedLen + TypeInfo + Clone + Eq + PartialEq + Debug + Copy;
	type AssetId: AssetId;
	/// Make a payment and return an identifier for later evaluation of success in some off-chain
	/// mechanism (likely an event, but possibly not on this chain).
	fn pay(
		who: &Self::AccountId,
		asset_id: Self::AssetId,
		amount: Self::Balance,
	) -> Result<Self::Id, ()>;
	/// Check how a payment has proceeded. `id` must have been a previously returned by `pay` for
	/// the result of this call to be meaningful.
	fn check_payment(id: Self::Id) -> PaymentStatus;
	/// Ensure that a call to pay with the given parameters will be successful if done immediately
	/// after this call. Used in benchmarking code.
	#[cfg(feature = "runtime-benchmarks")]
	fn ensure_successful(who: &Self::AccountId, amount: Self::Balance);
	/// Ensure that a call to `check_payment` with the given parameters will return either `Success`
	/// or `Failure`.
	#[cfg(feature = "runtime-benchmarks")]
	fn ensure_concluded(id: Self::Id);
}

pub type BalanceOf<T, I> = <<T as Config<I>>::Paymaster as Pay>::Balance;

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
#[impl_trait_for_tuples::impl_for_tuples(30)]
pub trait SpendFunds<T: Config<I>, I: 'static = ()> {
	fn spend_funds(total_weight: &mut Weight, total_spent: T::Balance, total_missed: u32);
}

/// An index of a proposal. Just a `u32`.
pub type ProposalIndex = u32;
/// A count of proposals. Just a `u32`.
pub type ProposalsCount = u32;

/// A spending proposal.
#[cfg_attr(feature = "std", derive(serde::Serialize, serde::Deserialize))]
#[derive(Encode, Decode, Clone, PartialEq, Eq, MaxEncodedLen, RuntimeDebug, TypeInfo)]
pub struct Proposal<AccountId, Balance, AssetId, SpendBalance, PaymentId> {
	/// The account proposing it.
	proposer: AccountId,
	/// The asset_id of the amount to be paid
	asset_id: AssetId,
	/// The (total) amount that should be paid.
	value: SpendBalance,
	/// The account to whom the payment should be made if the proposal is accepted.
	beneficiary: AccountId,
	/// The amount to be paid, but normalized to the native asset class
	normalized_value: Balance,
	// payment_status: PaymentStatus,
	payment_id: Option<PaymentId>,
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::{
		dispatch_context::with_context, pallet_prelude::*, traits::tokens::AssetId,
	};
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	pub struct Pallet<T, I = ()>(PhantomData<(T, I)>);

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		type Balance: Balance;

		/// The identifier for what asset should be spent.
		type AssetId: AssetId;

		/// Means by which we can make payments to accounts. This also defines the currency and the
		/// balance which we use to denote that currency.
		type Paymaster: Pay<
			AccountId = <Self as frame_system::Config>::AccountId,
			AssetId = Self::AssetId,
		>;

		type BalanceConverter: BalanceConversion<
			BalanceOf<Self, I>,
			Self::AssetId,
			Self::Balance,
			Error = Error<Self, I>,
		>;

		/// The overarching event type.
		type RuntimeEvent: From<Event<Self, I>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Period between successive spends.
		#[pallet::constant]
		type SpendPeriod: Get<Self::BlockNumber>;

		/// Percentage of spare funds (if any) that are burnt per spend period.
		#[pallet::constant]
		type Burn: Get<Permill>;

		/// The treasury's pallet id, used for deriving its sovereign account ID.
		#[pallet::constant]
		type PalletId: Get<PalletId>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;

		/// Runtime hooks to external pallet using treasury to compute spend funds.
		type SpendFunds: SpendFunds<Self, I>;

		/// The origin required for approving spends from the treasury outside of the proposal
		/// process. The `Success` value is the maximum amount that this origin is allowed to
		/// spend at a time.
		type SpendOrigin: EnsureOrigin<Self::RuntimeOrigin, Success = BalanceOf<Self, I>>;
	}

	/// Proposals that have been made.
	#[pallet::storage]
	#[pallet::getter(fn proposals)]
	pub type Proposals<T: Config<I>, I: 'static = ()> = CountedStorageMap<
		_,
		Twox64Concat,
		ProposalIndex,
		Proposal<T::AccountId, T::Balance, T::AssetId, BalanceOf<T, I>, <T::Paymaster as Pay>::Id>,
		OptionQuery,
	>;

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
		fn build(&self) {}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// New proposal.
		Proposed { proposal_index: ProposalIndex },
		/// We have ended a spend period and will now allocate funds.
		Spending { waiting_proposals: ProposalsCount },
		/// Spending has finished; this is the number of proposals rolled over till next
		/// T::SpendPeriod.
		Rollover { rollover_proposals: ProposalsCount, allocated_proposals: ProposalsCount },
		/// A new spend proposal has been approved.
		SpendApproved {
			proposal_index: ProposalIndex,
			amount: BalanceOf<T, I>,
			beneficiary: T::AccountId,
		},
		/// The inactive funds of the pallet have been updated.
		UpdatedInactive { reactivated: BalanceOf<T, I>, deactivated: BalanceOf<T, I> },
		/// The proposal was paid successfully
		ProposalPaymentSuccess {
			proposal_index: ProposalIndex,
			asset_id: T::AssetId,
			amount: BalanceOf<T, I>,
		},
		// The proposal payment failed. Payment will be retried in next spend period.
		ProposalPaymentFailure {
			proposal_index: ProposalIndex,
			asset_id: T::AssetId,
			amount: BalanceOf<T, I>,
		},
	}

	/// Error for the treasury pallet.
	#[pallet::error]
	pub enum Error<T, I = ()> {
		/// No proposal or bounty at that index.
		InvalidIndex,
		// /// Too many approvals in the queue.
		// TooManyApprovals,
		/// The spend origin is valid but the amount it is allowed to spend is lower than the
		/// amount to be spent.
		InsufficientPermission,
		/// Unable to convert asset to native balance
		BalanceConversionFailed,
	}

	#[pallet::hooks]
	impl<T: Config<I>, I: 'static> Hooks<BlockNumberFor<T>> for Pallet<T, I> {
		/// ## Complexity
		/// - `O(A)` where `A` is the number of approvals
		fn on_initialize(n: T::BlockNumber) -> Weight {
			// Check to see if we should spend some funds!
			if (n % T::SpendPeriod::get()).is_zero() {
				Self::spend_funds()
			} else {
				Weight::zero()
			}
		}
	}

	#[derive(Default)]
	struct SpendContext<Balance> {
		spend_in_context: BTreeMap<Balance, Balance>,
	}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Propose and approve a spend of treasury funds.
		///
		/// - `origin`: Must be `SpendOrigin` with the `Success` value being at least `amount`.
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
			ensure!(amount <= max_amount, Error::<T, I>::InsufficientPermission);

			with_context::<SpendContext<BalanceOf<T, I>>, _>(|v| {
				let context = v.or_default();

				// We group based on `max_amount`, to dinstinguish between different kind of
				// origins. (assumes that all origins have different `max_amount`)
				//
				// Worst case is that we reject some "valid" request.
				let spend = context.spend_in_context.entry(max_amount).or_default();

				// Ensure that we don't overflow nor use more than `max_amount`
				if spend.checked_add(&amount).map(|s| s > max_amount).unwrap_or(true) {
					Err(Error::<T, I>::InsufficientPermission)
				} else {
					*spend = spend.saturating_add(amount);

					Ok(())
				}
			})
			.unwrap_or(Ok(()))?;

			let beneficiary = T::Lookup::lookup(beneficiary)?;

			let proposal = Proposal {
				proposer: beneficiary.clone(),
				asset_id,
				value: amount,
				beneficiary: beneficiary.clone(),
				normalized_value: T::BalanceConverter::to_asset_balance(amount, asset_id)?,
				// payment_status: PaymentStatus::Unknown,
				payment_id: None,
			};

			let proposal_index = Proposals::<T, I>::count();
			Proposals::<T, I>::insert(proposal_index, proposal);

			Self::deposit_event(Event::SpendApproved { proposal_index, amount, beneficiary });
			Ok(())
		}
	}
}

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Spend some money! returns number of approvals before spend.
	pub fn spend_funds() -> Weight {
		let mut total_weight = Weight::zero();
		let mut total_spent = T::Balance::zero();
		let mut missed_proposals: u32 = 0;
		let proposals_len = Proposals::<T, I>::count();

		Self::deposit_event(Event::Spending { waiting_proposals: proposals_len });

		for key in Proposals::<T, I>::iter_keys() {
			if let Some(mut p) = Proposals::<T, I>::get(key) {
				match p.payment_id {
					None =>
						if let Ok(id) = T::Paymaster::pay(&p.beneficiary, p.asset_id, p.value) {
							total_spent += p.normalized_value;
							p.payment_id = Some(id);
							Proposals::<T, I>::set(key, Some(p));
						} else {
							missed_proposals = missed_proposals.saturating_add(1);
						},
					Some(payment_id) => match T::Paymaster::check_payment(payment_id) {
						PaymentStatus::Failure => {
							// try again in the next `T::SpendPeriod`.
							missed_proposals = missed_proposals.saturating_add(1);
							Self::deposit_event(Event::ProposalPaymentFailure {
								proposal_index: key,
								asset_id: p.asset_id,
								amount: p.value,
							});
						},
						PaymentStatus::Success => {
							Proposals::<T, I>::remove(key);
							Self::deposit_event(Event::ProposalPaymentSuccess {
								proposal_index: key,
								asset_id: p.asset_id,
								amount: p.value,
							});
						},
						// PaymentStatus::InProgress and PaymentStatus::Unknown indicate that the
						// proposal status is inconclusive, and might still be successful or failed
						// in the future.
						_ => {},
					},
				}
			} else {
			}
		}

		total_weight += T::WeightInfo::on_initialize_proposals(proposals_len);

		// Call Runtime hooks to external pallet using treasury to compute spend funds.
		// We could trigger burning of funds in the spendFunds hook as well.
		T::SpendFunds::spend_funds(&mut total_weight, total_spent, missed_proposals);

		Self::deposit_event(Event::Rollover {
			rollover_proposals: missed_proposals,
			allocated_proposals: proposals_len.saturating_sub(missed_proposals),
		});

		total_weight
	}
}
