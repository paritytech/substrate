// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Make periodic payment to members of a ranked collective according to rank.

#![cfg_attr(not(feature = "std"), no_std)]
#![recursion_limit = "128"]

use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
use sp_arithmetic::traits::{Saturating, Zero};
use sp_runtime::Perbill;
use sp_std::{marker::PhantomData, prelude::*};

use frame_support::{
	dispatch::DispatchResultWithPostInfo,
	ensure,
	traits::{
		tokens::{GetSalary, Pay, PaymentStatus},
		RankedMembers,
	},
	RuntimeDebug,
};

#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
pub mod weights;

pub use pallet::*;
pub use weights::WeightInfo;

/// Payroll cycle.
pub type Cycle = u32;

/// The status of the pallet instance.
#[derive(Encode, Decode, Eq, PartialEq, Clone, TypeInfo, MaxEncodedLen, RuntimeDebug)]
pub struct StatusType<CycleIndex, BlockNumber, Balance> {
	/// The index of the "current cycle" (i.e. the last cycle being processed).
	cycle_index: CycleIndex,
	/// The first block of the "current cycle" (i.e. the last cycle being processed).
	cycle_start: BlockNumber,
	/// The total budget available for all payments in the current cycle.
	budget: Balance,
	/// The total amount of the payments registered in the current cycle.
	total_registrations: Balance,
	/// The total amount of unregistered payments which have been made in the current cycle.
	total_unregistered_paid: Balance,
}

/// The state of a specific payment claim.
#[derive(Encode, Decode, Eq, PartialEq, Clone, TypeInfo, MaxEncodedLen, RuntimeDebug)]
pub enum ClaimState<Balance, Id> {
	/// No claim recorded.
	Nothing,
	/// Amount reserved when last active.
	Registered(Balance),
	/// Amount attempted to be paid when last active as well as the identity of the payment.
	Attempted { registered: Option<Balance>, id: Id, amount: Balance },
}

use ClaimState::*;

/// The status of a single payee/claimant.
#[derive(Encode, Decode, Eq, PartialEq, Clone, TypeInfo, MaxEncodedLen, RuntimeDebug)]
pub struct ClaimantStatus<CycleIndex, Balance, Id> {
	/// The most recent cycle in which the claimant was active.
	last_active: CycleIndex,
	/// The state of the payment/claim with in the above cycle.
	status: ClaimState<Balance, Id>,
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::{dispatch::Pays, pallet_prelude::*};
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	pub struct Pallet<T, I = ()>(PhantomData<(T, I)>);

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;

		/// The runtime event type.
		type RuntimeEvent: From<Event<Self, I>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Means by which we can make payments to accounts. This also defines the currency and the
		/// balance which we use to denote that currency.
		type Paymaster: Pay<Beneficiary = <Self as frame_system::Config>::AccountId, AssetKind = ()>;

		/// The current membership of payees.
		type Members: RankedMembers<AccountId = <Self as frame_system::Config>::AccountId>;

		/// The maximum payout to be made for a single period to an active member of the given rank.
		///
		/// The benchmarks require that this be non-zero for some rank at most 255.
		type Salary: GetSalary<
			<Self::Members as RankedMembers>::Rank,
			Self::AccountId,
			<Self::Paymaster as Pay>::Balance,
		>;

		/// The number of blocks within a cycle which accounts have to register their intent to
		/// claim.
		///
		/// The number of blocks between sequential payout cycles is the sum of this and
		/// `PayoutPeriod`.
		#[pallet::constant]
		type RegistrationPeriod: Get<Self::BlockNumber>;

		/// The number of blocks within a cycle which accounts have to claim the payout.
		///
		/// The number of blocks between sequential payout cycles is the sum of this and
		/// `RegistrationPeriod`.
		#[pallet::constant]
		type PayoutPeriod: Get<Self::BlockNumber>;

		/// The total budget per cycle.
		///
		/// This may change over the course of a cycle without any problem.
		#[pallet::constant]
		type Budget: Get<BalanceOf<Self, I>>;
	}

	pub type CycleIndexOf<T> = <T as frame_system::Config>::BlockNumber;
	pub type BalanceOf<T, I> = <<T as Config<I>>::Paymaster as Pay>::Balance;
	pub type IdOf<T, I> = <<T as Config<I>>::Paymaster as Pay>::Id;
	pub type StatusOf<T, I> =
		StatusType<CycleIndexOf<T>, <T as frame_system::Config>::BlockNumber, BalanceOf<T, I>>;
	pub type ClaimantStatusOf<T, I> = ClaimantStatus<CycleIndexOf<T>, BalanceOf<T, I>, IdOf<T, I>>;

	/// The overall status of the system.
	#[pallet::storage]
	pub(super) type Status<T: Config<I>, I: 'static = ()> =
		StorageValue<_, StatusOf<T, I>, OptionQuery>;

	/// The status of a claimant.
	#[pallet::storage]
	pub(super) type Claimant<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, T::AccountId, ClaimantStatusOf<T, I>, OptionQuery>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// A member is inducted into the payroll.
		Inducted { who: T::AccountId },
		/// A member registered for a payout.
		Registered { who: T::AccountId, amount: BalanceOf<T, I> },
		/// A payment happened.
		Paid {
			who: T::AccountId,
			beneficiary: T::AccountId,
			amount: BalanceOf<T, I>,
			id: <T::Paymaster as Pay>::Id,
		},
		/// The next cycle begins.
		CycleStarted { index: CycleIndexOf<T> },
	}

	#[pallet::error]
	pub enum Error<T, I = ()> {
		/// The salary system has already been started.
		AlreadyStarted,
		/// The account is not a ranked member.
		NotMember,
		/// The account is already inducted.
		AlreadyInducted,
		// The account is not yet inducted into the system.
		NotInducted,
		/// The member does not have a current valid claim.
		NoClaim,
		/// The member's claim is zero.
		ClaimZero,
		/// Current cycle's registration period is over.
		TooLate,
		/// Current cycle's payment period is not yet begun.
		TooEarly,
		/// Cycle is not yet over.
		NotYet,
		/// The payout cycles have not yet started.
		NotStarted,
		/// There is no budget left for the payout.
		Bankrupt,
		/// There was some issue with the mechanism of payment.
		PayError,
		/// The payment has neither failed nor succeeded yet.
		Inconclusive,
		/// The cycle is after that in which the payment was made.
		NotCurrent,
	}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Start the first payout cycle.
		///
		/// - `origin`: A `Signed` origin of an account.
		#[pallet::weight(T::WeightInfo::init())]
		#[pallet::call_index(0)]
		pub fn init(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let _ = ensure_signed(origin)?;
			let now = frame_system::Pallet::<T>::block_number();
			ensure!(!Status::<T, I>::exists(), Error::<T, I>::AlreadyStarted);
			let status = StatusType {
				cycle_index: Zero::zero(),
				cycle_start: now,
				budget: T::Budget::get(),
				total_registrations: Zero::zero(),
				total_unregistered_paid: Zero::zero(),
			};
			Status::<T, I>::put(&status);

			Self::deposit_event(Event::<T, I>::CycleStarted { index: status.cycle_index });
			Ok(Pays::No.into())
		}

		/// Move to next payout cycle, assuming that the present block is now within that cycle.
		///
		/// - `origin`: A `Signed` origin of an account.
		#[pallet::weight(T::WeightInfo::bump())]
		#[pallet::call_index(1)]
		pub fn bump(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let _ = ensure_signed(origin)?;
			let now = frame_system::Pallet::<T>::block_number();
			let cycle_period = Self::cycle_period();
			let mut status = Status::<T, I>::get().ok_or(Error::<T, I>::NotStarted)?;
			status.cycle_start.saturating_accrue(cycle_period);
			ensure!(now >= status.cycle_start, Error::<T, I>::NotYet);
			status.cycle_index.saturating_inc();
			status.budget = T::Budget::get();
			status.total_registrations = Zero::zero();
			status.total_unregistered_paid = Zero::zero();
			Status::<T, I>::put(&status);

			Self::deposit_event(Event::<T, I>::CycleStarted { index: status.cycle_index });
			Ok(Pays::No.into())
		}

		/// Induct oneself into the payout system.
		#[pallet::weight(T::WeightInfo::induct())]
		#[pallet::call_index(2)]
		pub fn induct(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let cycle_index = Status::<T, I>::get().ok_or(Error::<T, I>::NotStarted)?.cycle_index;
			let _ = T::Members::rank_of(&who).ok_or(Error::<T, I>::NotMember)?;
			ensure!(!Claimant::<T, I>::contains_key(&who), Error::<T, I>::AlreadyInducted);

			Claimant::<T, I>::insert(
				&who,
				ClaimantStatus { last_active: cycle_index, status: Nothing },
			);

			Self::deposit_event(Event::<T, I>::Inducted { who });
			Ok(Pays::No.into())
		}

		/// Register for a payout.
		///
		/// Will only work if we are in the first `RegistrationPeriod` blocks since the cycle
		/// started.
		///
		/// - `origin`: A `Signed` origin of an account which is a member of `Members`.
		#[pallet::weight(T::WeightInfo::register())]
		#[pallet::call_index(3)]
		pub fn register(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let rank = T::Members::rank_of(&who).ok_or(Error::<T, I>::NotMember)?;
			let mut status = Status::<T, I>::get().ok_or(Error::<T, I>::NotStarted)?;
			let mut claimant = Claimant::<T, I>::get(&who).ok_or(Error::<T, I>::NotInducted)?;
			let now = frame_system::Pallet::<T>::block_number();
			ensure!(
				now < status.cycle_start + T::RegistrationPeriod::get(),
				Error::<T, I>::TooLate
			);
			ensure!(claimant.last_active < status.cycle_index, Error::<T, I>::NoClaim);
			let payout = T::Salary::get_salary(rank, &who);
			ensure!(!payout.is_zero(), Error::<T, I>::ClaimZero);
			claimant.last_active = status.cycle_index;
			claimant.status = Registered(payout);
			status.total_registrations.saturating_accrue(payout);

			Claimant::<T, I>::insert(&who, &claimant);
			Status::<T, I>::put(&status);

			Self::deposit_event(Event::<T, I>::Registered { who, amount: payout });
			Ok(Pays::No.into())
		}

		/// Request a payout.
		///
		/// Will only work if we are after the first `RegistrationPeriod` blocks since the cycle
		/// started but by no more than `PayoutPeriod` blocks.
		///
		/// - `origin`: A `Signed` origin of an account which is a member of `Members`.
		#[pallet::weight(T::WeightInfo::payout())]
		#[pallet::call_index(4)]
		pub fn payout(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			Self::do_payout(who.clone(), who)?;
			Ok(Pays::No.into())
		}

		/// Request a payout to a secondary account.
		///
		/// Will only work if we are after the first `RegistrationPeriod` blocks since the cycle
		/// started but by no more than `PayoutPeriod` blocks.
		///
		/// - `origin`: A `Signed` origin of an account which is a member of `Members`.
		/// - `beneficiary`: The account to receive payment.
		#[pallet::weight(T::WeightInfo::payout_other())]
		#[pallet::call_index(5)]
		pub fn payout_other(
			origin: OriginFor<T>,
			beneficiary: T::AccountId,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			Self::do_payout(who, beneficiary)?;
			Ok(Pays::No.into())
		}

		/// Update a payment's status; if it failed, alter the state so the payment can be retried.
		///
		/// This must be called within the same cycle as the failed payment. It will fail with
		/// `Event::NotCurrent` otherwise.
		///
		/// - `origin`: A `Signed` origin of an account which is a member of `Members` who has
		///   received a payment this cycle.
		#[pallet::weight(T::WeightInfo::check_payment())]
		#[pallet::call_index(6)]
		pub fn check_payment(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			let mut status = Status::<T, I>::get().ok_or(Error::<T, I>::NotStarted)?;
			let mut claimant = Claimant::<T, I>::get(&who).ok_or(Error::<T, I>::NotInducted)?;
			ensure!(claimant.last_active == status.cycle_index, Error::<T, I>::NotCurrent);
			let (id, registered, amount) = match claimant.status {
				Attempted { id, registered, amount } => (id, registered, amount),
				_ => return Err(Error::<T, I>::NoClaim.into()),
			};
			match T::Paymaster::check_payment(id) {
				PaymentStatus::Failure => {
					// Payment failed: we reset back to the status prior to payment.
					if let Some(amount) = registered {
						// Account registered; this makes it simple to roll back and allow retry.
						claimant.status = ClaimState::Registered(amount);
					} else {
						// Account didn't register; we set it to `Nothing` but must decrement
						// the `last_active` also to ensure a retry works.
						claimant.last_active.saturating_reduce(1u32.into());
						claimant.status = ClaimState::Nothing;
						// Since it is not registered, we must walk back our counter for what has
						// been paid.
						status.total_unregistered_paid.saturating_reduce(amount);
					}
				},
				PaymentStatus::Success => claimant.status = ClaimState::Nothing,
				_ => return Err(Error::<T, I>::Inconclusive.into()),
			}
			Claimant::<T, I>::insert(&who, &claimant);
			Status::<T, I>::put(&status);

			Ok(Pays::No.into())
		}
	}

	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		pub fn status() -> Option<StatusOf<T, I>> {
			Status::<T, I>::get()
		}
		pub fn last_active(who: &T::AccountId) -> Result<CycleIndexOf<T>, DispatchError> {
			Ok(Claimant::<T, I>::get(&who).ok_or(Error::<T, I>::NotInducted)?.last_active)
		}
		pub fn cycle_period() -> T::BlockNumber {
			T::RegistrationPeriod::get() + T::PayoutPeriod::get()
		}
		fn do_payout(who: T::AccountId, beneficiary: T::AccountId) -> DispatchResult {
			let mut status = Status::<T, I>::get().ok_or(Error::<T, I>::NotStarted)?;
			let mut claimant = Claimant::<T, I>::get(&who).ok_or(Error::<T, I>::NotInducted)?;

			let now = frame_system::Pallet::<T>::block_number();
			ensure!(
				now >= status.cycle_start + T::RegistrationPeriod::get(),
				Error::<T, I>::TooEarly,
			);

			let (payout, registered) = match claimant.status {
				Registered(unpaid) if claimant.last_active == status.cycle_index => {
					// Registered for this cycle. Pay accordingly.
					let payout = if status.total_registrations <= status.budget {
						// Can pay in full.
						unpaid
					} else {
						// Must be reduced pro-rata
						Perbill::from_rational(status.budget, status.total_registrations)
							.mul_floor(unpaid)
					};
					(payout, Some(unpaid))
				},
				Nothing | Attempted { .. } if claimant.last_active < status.cycle_index => {
					// Not registered for this cycle. Pay from whatever is left.
					let rank = T::Members::rank_of(&who).ok_or(Error::<T, I>::NotMember)?;
					let ideal_payout = T::Salary::get_salary(rank, &who);

					let pot = status
						.budget
						.saturating_sub(status.total_registrations)
						.saturating_sub(status.total_unregistered_paid);

					let payout = ideal_payout.min(pot);
					ensure!(!payout.is_zero(), Error::<T, I>::ClaimZero);

					status.total_unregistered_paid.saturating_accrue(payout);
					(payout, None)
				},
				_ => return Err(Error::<T, I>::NoClaim.into()),
			};

			claimant.last_active = status.cycle_index;

			let id = T::Paymaster::pay(&beneficiary, (), payout)
				.map_err(|()| Error::<T, I>::PayError)?;

			claimant.status = Attempted { registered, id, amount: payout };

			Claimant::<T, I>::insert(&who, &claimant);
			Status::<T, I>::put(&status);

			Self::deposit_event(Event::<T, I>::Paid { who, beneficiary, amount: payout, id });
			Ok(())
		}
	}
}
