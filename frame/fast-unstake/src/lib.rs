// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! A pallet that's designed to JUST do the following:
//!
//! If a nominator is not exposed in any `ErasStakers` (i.e. "has not actively backed any
//! validators in the last `BondingDuration` days"), then they can register themselves in this
//! pallet, unstake faster than having to wait an entire bonding duration.
//!
//! Appearing in the exposure of a validator means being exposed equal to that validator from the
//! point of view of the staking system. This usually means earning rewards with the validator, and
//! also being at the risk of slashing with the validator. This is equivalent to the "Active
//! Nominator" role explained in the
//! [February Staking Update](https://polkadot.network/blog/staking-update-february-2022/).
//!
//! This pallet works off the basis of `on_idle`, meaning that it provides no guarantee about when
//! it will succeed, if at all. Moreover, the queue implementation is unordered. In case of
//! congestion, no FIFO ordering is provided.
//!
//! Stakers who are certain about NOT being exposed can register themselves with
//! [`Call::register_fast_unstake`]. This will chill, and fully unbond the staker, and place them in
//! the queue to be checked.
//!
//! Once queued, but not being actively processed, stakers can withdraw their request via
//! [`Call::deregister`].
//!
//! Once queued, a staker wishing to unbond can perform no further action in pallet-staking. This is
//! to prevent them from accidentally exposing themselves behind a validator etc.
//!
//! Once processed, if successful, no additional fee for the checking process is taken, and the
//! staker is instantly unbonded.
//!
//! If unsuccessful, meaning that the staker was exposed sometime in the last `BondingDuration` eras
//! they will end up being slashed for the amount of wasted work they have inflicted on the chian.

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

// NOTE: enable benchmarking in tests as well.
#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
pub mod types;
pub mod weights;

pub const LOG_TARGET: &'static str = "runtime::fast-unstake";

// syntactic sugar for logging.
#[macro_export]
macro_rules! log {
	($level:tt, $patter:expr $(, $values:expr)* $(,)?) => {
		log::$level!(
			target: crate::LOG_TARGET,
			concat!("[{:?}] 💨 ", $patter), <frame_system::Pallet<T>>::block_number() $(, $values)*
		)
	};
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use crate::types::*;
	use frame_election_provider_support::ElectionProviderBase;
	use frame_support::{
		pallet_prelude::*,
		traits::{Defensive, ReservableCurrency},
	};
	use frame_system::{pallet_prelude::*, RawOrigin};
	use pallet_staking::Pallet as Staking;
	use sp_runtime::{
		traits::{Saturating, Zero},
		DispatchResult,
	};
	use sp_staking::EraIndex;
	use sp_std::{prelude::*, vec::Vec};
	pub use weights::WeightInfo;

	#[derive(scale_info::TypeInfo, codec::Encode, codec::Decode, codec::MaxEncodedLen)]
	#[codec(mel_bound(T: Config))]
	#[scale_info(skip_type_params(T))]
	pub struct MaxChecking<T: Config>(sp_std::marker::PhantomData<T>);
	impl<T: Config> frame_support::traits::Get<u32> for MaxChecking<T> {
		fn get() -> u32 {
			<T as pallet_staking::Config>::BondingDuration::get() + 1
		}
	}

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config + pallet_staking::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>
			+ TryInto<Event<Self>>;

		/// The currency used for deposits.
		type DepositCurrency: ReservableCurrency<Self::AccountId, Balance = BalanceOf<Self>>;

		/// Deposit to take for unstaking, to make sure we're able to slash the it in order to cover
		/// the costs of resources on unsuccessful unstake.
		type Deposit: Get<BalanceOf<Self>>;

		/// The origin that can control this pallet.
		type ControlOrigin: frame_support::traits::EnsureOrigin<Self::RuntimeOrigin>;

		/// The weight information of this pallet.
		type WeightInfo: WeightInfo;
	}

	/// The current "head of the queue" being unstaked.
	#[pallet::storage]
	pub type Head<T: Config> =
		StorageValue<_, UnstakeRequest<T::AccountId, MaxChecking<T>, BalanceOf<T>>, OptionQuery>;

	/// The map of all accounts wishing to be unstaked.
	///
	/// Keeps track of `AccountId` wishing to unstake and it's corresponding deposit.
	#[pallet::storage]
	pub type Queue<T: Config> = CountedStorageMap<_, Twox64Concat, T::AccountId, BalanceOf<T>>;

	/// Number of eras to check per block.
	///
	/// If set to 0, this pallet does absolutely nothing.
	///
	/// Based on the amount of weight available at `on_idle`, up to this many eras of a single
	/// nominator might be checked.
	#[pallet::storage]
	pub type ErasToCheckPerBlock<T: Config> = StorageValue<_, u32, ValueQuery>;

	/// The events of this pallet.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A staker was unstaked.
		Unstaked { stash: T::AccountId, result: DispatchResult },
		/// A staker was slashed for requesting fast-unstake whilst being exposed.
		Slashed { stash: T::AccountId, amount: BalanceOf<T> },
		/// A staker was partially checked for the given eras, but the process did not finish.
		Checking { stash: T::AccountId, eras: Vec<EraIndex> },
		/// Some internal error happened while migrating stash. They are removed as head as a
		/// consequence.
		Errored { stash: T::AccountId },
		/// An internal error happened. Operations will be paused now.
		InternalError,
	}

	#[pallet::error]
	#[cfg_attr(test, derive(PartialEq))]
	pub enum Error<T> {
		/// The provided Controller account was not found.
		///
		/// This means that the given account is not bonded.
		NotController,
		/// The bonded account has already been queued.
		AlreadyQueued,
		/// The bonded account has active unlocking chunks.
		NotFullyBonded,
		/// The provided un-staker is not in the `Queue`.
		NotQueued,
		/// The provided un-staker is already in Head, and cannot deregister.
		AlreadyHead,
		/// The call is not allowed at this point because the pallet is not active.
		CallNotAllowed,
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<T::BlockNumber> for Pallet<T> {
		fn on_idle(_: T::BlockNumber, remaining_weight: Weight) -> Weight {
			if remaining_weight.any_lt(T::DbWeight::get().reads(2)) {
				return Weight::from_ref_time(0)
			}

			Self::do_on_idle(remaining_weight)
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Register oneself for fast-unstake.
		///
		/// The dispatch origin of this call must be signed by the controller account, similar to
		/// `staking::unbond`.
		///
		/// The stash associated with the origin must have no ongoing unlocking chunks. If
		/// successful, this will fully unbond and chill the stash. Then, it will enqueue the stash
		/// to be checked in further blocks.
		///
		/// If by the time this is called, the stash is actually eligible for fast-unstake, then
		/// they are guaranteed to remain eligible, because the call will chill them as well.
		///
		/// If the check works, the entire staking data is removed, i.e. the stash is fully
		/// unstaked.
		///
		/// If the check fails, the stash remains chilled and waiting for being unbonded as in with
		/// the normal staking system, but they lose part of their unbonding chunks due to consuming
		/// the chain's resources.
		#[pallet::weight(<T as Config>::WeightInfo::register_fast_unstake())]
		pub fn register_fast_unstake(origin: OriginFor<T>) -> DispatchResult {
			let ctrl = ensure_signed(origin)?;

			ensure!(ErasToCheckPerBlock::<T>::get() != 0, <Error<T>>::CallNotAllowed);

			let ledger =
				pallet_staking::Ledger::<T>::get(&ctrl).ok_or(Error::<T>::NotController)?;
			ensure!(!Queue::<T>::contains_key(&ledger.stash), Error::<T>::AlreadyQueued);
			ensure!(
				Head::<T>::get().map_or(true, |UnstakeRequest { stash, .. }| stash != ledger.stash),
				Error::<T>::AlreadyHead
			);
			// second part of the && is defensive.
			ensure!(
				ledger.active == ledger.total && ledger.unlocking.is_empty(),
				Error::<T>::NotFullyBonded
			);

			// chill and fully unstake.
			Staking::<T>::chill(RawOrigin::Signed(ctrl.clone()).into())?;
			Staking::<T>::unbond(RawOrigin::Signed(ctrl).into(), ledger.total)?;

			T::DepositCurrency::reserve(&ledger.stash, T::Deposit::get())?;

			// enqueue them.
			Queue::<T>::insert(ledger.stash, T::Deposit::get());
			Ok(())
		}

		/// Deregister oneself from the fast-unstake.
		///
		/// This is useful if one is registered, they are still waiting, and they change their mind.
		///
		/// Note that the associated stash is still fully unbonded and chilled as a consequence of
		/// calling `register_fast_unstake`. This should probably be followed by a call to
		/// `Staking::rebond`.
		#[pallet::weight(<T as Config>::WeightInfo::deregister())]
		pub fn deregister(origin: OriginFor<T>) -> DispatchResult {
			let ctrl = ensure_signed(origin)?;

			ensure!(ErasToCheckPerBlock::<T>::get() != 0, <Error<T>>::CallNotAllowed);

			let stash = pallet_staking::Ledger::<T>::get(&ctrl)
				.map(|l| l.stash)
				.ok_or(Error::<T>::NotController)?;
			ensure!(Queue::<T>::contains_key(&stash), Error::<T>::NotQueued);
			ensure!(
				Head::<T>::get().map_or(true, |UnstakeRequest { stash, .. }| stash != stash),
				Error::<T>::AlreadyHead
			);
			let deposit = Queue::<T>::take(stash.clone());

			if let Some(deposit) = deposit.defensive() {
				let remaining = T::DepositCurrency::unreserve(&stash, deposit);
				if !remaining.is_zero() {
					frame_support::defensive!("`not enough balance to unreserve`");
					ErasToCheckPerBlock::<T>::put(0);
					Self::deposit_event(Event::<T>::InternalError)
				}
			}

			Ok(())
		}

		/// Control the operation of this pallet.
		///
		/// Dispatch origin must be signed by the [`Config::ControlOrigin`].
		#[pallet::weight(<T as Config>::WeightInfo::control())]
		pub fn control(origin: OriginFor<T>, unchecked_eras_to_check: EraIndex) -> DispatchResult {
			let _ = T::ControlOrigin::ensure_origin(origin)?;
			ErasToCheckPerBlock::<T>::put(unchecked_eras_to_check);
			Ok(())
		}
	}

	impl<T: Config> Pallet<T> {
		/// process up to `remaining_weight`.
		///
		/// Returns the actual weight consumed.
		///
		/// Written for readability in mind, not efficiency. For example:
		///
		/// 1. We assume this is only ever called once per `on_idle`. This is because we know that
		/// in all use cases, even a single nominator cannot be unbonded in a single call. Multiple
		/// calls to this function are thus not needed.
		///
		/// 2. We will only mark a staker as unstaked if at the beginning of a check cycle, they are
		/// found out to have no eras to check. At the end of a check cycle, even if they are fully
		/// checked, we don't finish the process.
		pub(crate) fn do_on_idle(remaining_weight: Weight) -> Weight {
			let mut eras_to_check_per_block = ErasToCheckPerBlock::<T>::get();
			if eras_to_check_per_block.is_zero() {
				return T::DbWeight::get().reads(1)
			}

			// NOTE: here we're assuming that the number of validators has only ever increased,
			// meaning that the number of exposures to check is either this per era, or less.
			let validator_count = pallet_staking::ValidatorCount::<T>::get();

			// determine the number of eras to check. This is based on both `ErasToCheckPerBlock`
			// and `remaining_weight` passed on to us from the runtime executive.
			let max_weight = |v, u| {
				<T as Config>::WeightInfo::on_idle_check(v * u)
					.max(<T as Config>::WeightInfo::on_idle_unstake())
			};
			while max_weight(validator_count, eras_to_check_per_block).any_gt(remaining_weight) {
				eras_to_check_per_block.saturating_dec();
				if eras_to_check_per_block.is_zero() {
					log!(debug, "early existing because eras_to_check_per_block is zero");
					return T::DbWeight::get().reads(2)
				}
			}

			if <<T as pallet_staking::Config>::ElectionProvider as ElectionProviderBase>::ongoing()
			{
				// NOTE: we assume `ongoing` does not consume any weight.
				// there is an ongoing election -- we better not do anything. Imagine someone is not
				// exposed anywhere in the last era, and the snapshot for the election is already
				// taken. In this time period, we don't want to accidentally unstake them.
				return T::DbWeight::get().reads(2)
			}

			let UnstakeRequest { stash, mut checked, deposit } =
				match Head::<T>::take().or_else(|| {
					// NOTE: there is no order guarantees in `Queue`.
					Queue::<T>::drain()
						.map(|(stash, deposit)| UnstakeRequest {
							stash,
							deposit,
							checked: Default::default(),
						})
						.next()
				}) {
					None => {
						// There's no `Head` and nothing in the `Queue`, nothing to do here.
						return T::DbWeight::get().reads(4)
					},
					Some(head) => head,
				};

			log!(
				debug,
				"checking {:?}, eras_to_check_per_block = {:?}, remaining_weight = {:?}",
				stash,
				eras_to_check_per_block,
				remaining_weight
			);

			// the range that we're allowed to check in this round.
			let current_era = pallet_staking::CurrentEra::<T>::get().unwrap_or_default();
			let bonding_duration = <T as pallet_staking::Config>::BondingDuration::get();
			// prune all the old eras that we don't care about. This will help us keep the bound
			// of `checked`.
			checked.retain(|e| *e >= current_era.saturating_sub(bonding_duration));
			let unchecked_eras_to_check = {
				// get the last available `bonding_duration` eras up to current era in reverse
				// order.
				let total_check_range = (current_era.saturating_sub(bonding_duration)..=
					current_era)
					.rev()
					.collect::<Vec<_>>();
				debug_assert!(
					total_check_range.len() <= (bonding_duration + 1) as usize,
					"{:?}",
					total_check_range
				);

				// remove eras that have already been checked, take a maximum of
				// eras_to_check_per_block.
				total_check_range
					.into_iter()
					.filter(|e| !checked.contains(e))
					.take(eras_to_check_per_block as usize)
					.collect::<Vec<_>>()
			};

			log!(
				debug,
				"{} eras to check: {:?}",
				unchecked_eras_to_check.len(),
				unchecked_eras_to_check
			);

			if unchecked_eras_to_check.is_empty() {
				// `stash` is not exposed in any era now -- we can let go of them now.
				let num_slashing_spans = Staking::<T>::slashing_spans(&stash).iter().count() as u32;

				let result = pallet_staking::Pallet::<T>::force_unstake(
					RawOrigin::Root.into(),
					stash.clone(),
					num_slashing_spans,
				);

				let remaining = T::DepositCurrency::unreserve(&stash, deposit);
				if !remaining.is_zero() {
					frame_support::defensive!("`not enough balance to unreserve`");
					ErasToCheckPerBlock::<T>::put(0);
					Self::deposit_event(Event::<T>::InternalError)
				} else {
					log!(info, "unstaked {:?}, outcome: {:?}", stash, result);
					Self::deposit_event(Event::<T>::Unstaked { stash, result });
				}

				<T as Config>::WeightInfo::on_idle_unstake()
			} else {
				// eras remaining to be checked.
				let mut eras_checked = 0u32;
				let is_exposed = unchecked_eras_to_check.iter().any(|e| {
					eras_checked.saturating_inc();
					Self::is_exposed_in_era(&stash, e)
				});

				log!(
					debug,
					"checked {:?} eras, exposed? {}, (v: {:?}, u: {:?})",
					eras_checked,
					is_exposed,
					validator_count,
					unchecked_eras_to_check.len()
				);

				// NOTE: you can be extremely unlucky and get slashed here: You are not exposed in
				// the last 28 eras, have registered yourself to be unstaked, midway being checked,
				// you are exposed.
				if is_exposed {
					T::DepositCurrency::slash_reserved(&stash, deposit);
					log!(info, "slashed {:?} by {:?}", stash, deposit);
					Self::deposit_event(Event::<T>::Slashed { stash, amount: deposit });
				} else {
					// Not exposed in these eras.
					match checked.try_extend(unchecked_eras_to_check.clone().into_iter()) {
						Ok(_) => {
							Head::<T>::put(UnstakeRequest {
								stash: stash.clone(),
								checked,
								deposit,
							});
							Self::deposit_event(Event::<T>::Checking {
								stash,
								eras: unchecked_eras_to_check,
							});
						},
						Err(_) => {
							// don't put the head back in -- there is an internal error in the
							// pallet.
							frame_support::defensive!("`checked is pruned via retain above`");
							ErasToCheckPerBlock::<T>::put(0);
							Self::deposit_event(Event::<T>::InternalError);
						},
					}
				}

				<T as Config>::WeightInfo::on_idle_check(validator_count * eras_checked)
			}
		}

		/// Checks whether an account `staker` has been exposed in an era.
		fn is_exposed_in_era(staker: &T::AccountId, era: &EraIndex) -> bool {
			pallet_staking::ErasStakers::<T>::iter_prefix(era).any(|(validator, exposures)| {
				validator == *staker || exposures.others.iter().any(|i| i.who == *staker)
			})
		}
	}
}
