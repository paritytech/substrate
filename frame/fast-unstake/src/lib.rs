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

//! A pallet that's designed to ONLY do:
//!
//! If a nominator is not exposed at all in any `ErasStakers` (i.e. "has not backed any validators
//! in the last `BondingDuration` days"), then they can register themselves in this pallet, and move
//! quickly into a nomination pool.
//!
//! This pallet works of the basis of `on_idle`, meaning that it provides no guarantee about when it
//! will succeed, if at all. Moreover, the queue implementation is unordered. In case of congestion,
//! not FIFO ordering is provided.
//!
//! Stakers who are certain about NOT being exposed can register themselves with
//! [`Call::register_fast_unstake`]. This will chill, and fully unbond the staker, and place them in
//! the queue to be checked.
//!
//! Once queued, but not being actively processed, stakers can withdraw their request via
//! [`Call::deregister`].
//!
//! Once queued, a staker wishing to unbond can perform to further action in pallet-staking. This is
//! to prevent them from accidentally exposing themselves behind a validator etc.
//!
//! Once processed, if successful, no additional fees for the checking process is taken, and the
//! staker is instantly unbonded. Optionally, if the have asked to join a pool, their *entire* stake
//! is joined into their pool of choice.
//!
//! If unsuccessful, meaning that the staker was exposed sometime in the last `BondingDuration` eras
//! they will end up being slashed for the amount of wasted work they have inflicted on the chian.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;

pub use pallet::*;

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
	use frame_election_provider_support::ElectionProvider;
	use frame_support::{
		pallet_prelude::*,
		traits::{Currency, IsSubType},
	};
	use frame_system::{pallet_prelude::*, RawOrigin};
	use pallet_nomination_pools::PoolId;
	use pallet_staking::Pallet as Staking;
	use sp_runtime::{
		traits::{Saturating, Zero},
		transaction_validity::{InvalidTransaction, TransactionValidityError},
		DispatchResult,
	};
	use sp_staking::EraIndex;
	use sp_std::{prelude::*, vec::Vec};

	pub trait WeightInfo {
		fn register_fast_unstake() -> Weight;
		fn deregister() -> Weight;
		fn control() -> Weight;

		fn on_idle_unstake() -> Weight;
		fn on_idle_check(v: u32, e: u32) -> Weight;
	}

	impl WeightInfo for () {
		fn register_fast_unstake() -> Weight {
			0
		}
		fn deregister() -> Weight {
			0
		}
		fn control() -> Weight {
			0
		}
		fn on_idle_unstake() -> Weight {
			0
		}
		fn on_idle_check(_: u32, _: u32) -> Weight {
			0
		}
	}

	type BalanceOf<T> = <<T as pallet_staking::Config>::Currency as Currency<
		<T as frame_system::Config>::AccountId,
	>>::Balance;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config:
		frame_system::Config
		+ pallet_staking::Config<
			CurrencyBalance = <Self as pallet_nomination_pools::Config>::CurrencyBalance,
		> + pallet_nomination_pools::Config
	{
		/// The overarching event type.
		type Event: From<Event<Self>>
			+ IsType<<Self as frame_system::Config>::Event>
			+ TryInto<Event<Self>>;

		/// The amount of balance slashed per each era that was wastefully checked.
		///
		/// A reasonable value could be `runtime_weight_to_fee(weight_per_era_check)`.
		type SlashPerEra: Get<BalanceOf<Self>>;

		/// The origin that can control this pallet.
		type ControlOrigin: frame_support::traits::EnsureOrigin<Self::Origin>;

		/// The weight information of this pallet.
		type WeightInfo: WeightInfo;
	}

	/// An unstake request.
	#[derive(
		Encode, Decode, Eq, PartialEq, Clone, scale_info::TypeInfo, frame_support::RuntimeDebug,
	)]
	pub struct UnstakeRequest<AccountId> {
		/// Their stash account.
		pub(crate) stash: AccountId,
		/// The list of eras for which they have been checked.
		pub(crate) checked: Vec<EraIndex>,
		/// The pool they wish to join, if any.
		pub(crate) maybe_pool_id: Option<PoolId>,
	}

	/// The current "head of the queue" being unstaked.
	#[pallet::storage]
	#[pallet::unbounded]
	pub type Head<T: Config> = StorageValue<_, UnstakeRequest<T::AccountId>, OptionQuery>;

	/// The map of all accounts wishing to be unstaked.
	///
	/// Points the `AccountId` wishing to unstake to the optional `PoolId` they wish to join
	/// thereafter.
	#[pallet::storage]
	pub type Queue<T: Config> = StorageMap<_, Twox64Concat, T::AccountId, Option<PoolId>>;

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
		Unstaked { stash: T::AccountId, maybe_pool_id: Option<PoolId>, result: DispatchResult },
		/// A staker was slashed for requesting fast-unstake whilst being exposed.
		Slashed { stash: T::AccountId, amount: BalanceOf<T> },
		/// A staker was partially checked for the given eras, but the process did not finish.
		Checked { stash: T::AccountId, eras: Vec<EraIndex> },
		/// Some internal error happened while migrating stash. They are removed as head as a
		/// consequence.
		Errored { stash: T::AccountId },
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<T::BlockNumber> for Pallet<T> {
		fn on_idle(_block: T::BlockNumber, remaining_weight: Weight) -> Weight {
			Self::process_head(remaining_weight)
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Register oneself for fast-unstake.
		///
		/// The dispatch origin of this call must be signed by the controller account, similar to
		/// `staking::unbond`.
		///
		/// The stash associated with the origin must have no ongoing unlocking chunks.  If
		/// successful, this will fully unbond and chill the stash. Then, it will enqueue the stash
		/// to be checked in further blocks.
		///
		/// If by the time this is called, the stash is actually eligible for fast-unstake, then
		/// they are guaranteed to remain eligible, because the call will chill them as well.
		///
		/// If the check works, the entire staking data is removed, i.e. the stash is fully
		/// unstaked, and they potentially join a pool with their entire bonded stake.
		///
		/// If the check fails, the stash remains chilled and waiting for being unbonded as in with
		/// the normal staking system, but they lose part of their unbonding chunks due to consuming
		/// the chain's resources.
		#[pallet::weight(<T as Config>::WeightInfo::register_fast_unstake())]
		pub fn register_fast_unstake(
			origin: OriginFor<T>,
			maybe_pool_id: Option<PoolId>,
		) -> DispatchResult {
			let ctrl = ensure_signed(origin)?;

			let ledger = pallet_staking::Ledger::<T>::get(&ctrl).ok_or("NotController")?;
			ensure!(pallet_staking::Nominators::<T>::contains_key(&ledger.stash), "NotNominator");

			ensure!(!Queue::<T>::contains_key(&ledger.stash), "AlreadyQueued");
			ensure!(
				Head::<T>::get().map_or(true, |UnstakeRequest { stash, .. }| stash != ledger.stash),
				"AlreadyHead"
			);
			// second part of the && is defensive.
			ensure!(ledger.active == ledger.total && ledger.unlocking.is_empty(), "NotFullyBonded");

			// chill and fully unstake.
			Staking::<T>::chill(RawOrigin::Signed(ctrl.clone()).into())?;
			Staking::<T>::unbond(RawOrigin::Signed(ctrl).into(), ledger.total)?;

			// enqueue them.
			Queue::<T>::insert(ledger.stash, maybe_pool_id);
			Ok(())
		}

		/// Deregister oneself from the fast-unstake (and possibly joining a pool).
		///
		/// This is useful id one is registered, they are still waiting, and they change their mind.
		///
		/// Note that the associated stash is still fully unbonded and chilled as a consequence of
		/// calling `register_fast_unstake`. This should probably be followed by a call to
		/// `Staking::rebond`.
		#[pallet::weight(<T as Config>::WeightInfo::deregister())]
		pub fn deregister(origin: OriginFor<T>) -> DispatchResult {
			let ctrl = ensure_signed(origin)?;
			let stash = pallet_staking::Ledger::<T>::get(&ctrl)
				.map(|l| l.stash)
				.ok_or("NotController")?;
			ensure!(Queue::<T>::contains_key(&stash), "NotQueued");
			ensure!(
				Head::<T>::get().map_or(true, |UnstakeRequest { stash, .. }| stash != stash),
				"AlreadyHead"
			);

			Queue::<T>::remove(stash);
			Ok(())
		}

		/// Control the operation of this pallet.
		///
		/// Dispatch origin must be signed by the [`Config::ControlOrigin`].
		#[pallet::weight(<T as Config>::WeightInfo::control())]
		pub fn control(origin: OriginFor<T>, eras_to_check: EraIndex) -> DispatchResult {
			let _ = T::ControlOrigin::ensure_origin(origin)?;
			ErasToCheckPerBlock::<T>::put(eras_to_check);

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
		/// calls to this function are thus not needed. 2. We will only mark a staker
		#[cfg_attr(feature = "runtime-benchmarks", allow(unused_variables))]
		fn process_head(remaining_weight: Weight) -> Weight {
			let eras_to_check_per_block = ErasToCheckPerBlock::<T>::get();
			if eras_to_check_per_block.is_zero() {
				return T::DbWeight::get().reads(1)
			}

			// NOTE: here we're assuming that the number of validators has only ever increased,
			// meaning that the number of exposures to check is either this per era, or less.s
			let validator_count = pallet_staking::ValidatorCount::<T>::get();

			// determine the number of eras to check. This is based on both `ErasToCheckPerBlock`
			// and `remaining_weight` passed on to us from the runtime executive.
			#[cfg(feature = "runtime-benchmarks")]
			let final_eras_to_check = eras_to_check_per_block;
			#[cfg(not(feature = "runtime-benchmarks"))]
			let final_eras_to_check = {
				let worse_weight = |v, u| {
					<T as Config>::WeightInfo::on_idle_check(v, u)
						.max(<T as Config>::WeightInfo::on_idle_unstake())
				};
				let mut try_eras_to_check = eras_to_check_per_block;
				while worse_weight(validator_count, try_eras_to_check) > remaining_weight {
					try_eras_to_check.saturating_dec();
					if try_eras_to_check.is_zero() {
						return T::DbWeight::get().reads(1)
					}
				}

				drop(eras_to_check_per_block);
				try_eras_to_check
			};

			if <T as pallet_staking::Config>::ElectionProvider::ongoing() {
				// NOTE: we assume `ongoing` does not consume any weight.
				// there is an ongoing election -- we better not do anything. Imagine someone is not
				// exposed anywhere in the last era, and the snapshot for the election is already
				// taken. In this time period, we don't want to accidentally unstake them.
				return T::DbWeight::get().reads(2)
			}

			let UnstakeRequest { stash, mut checked, maybe_pool_id } = match Head::<T>::take()
				.or_else(|| {
					Queue::<T>::drain()
						.take(1)
						.map(|(stash, maybe_pool_id)| UnstakeRequest {
							stash,
							maybe_pool_id,
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

			log!(debug, "checking {:?}", stash);

			// the range that we're allowed to check in this round.
			let current_era = pallet_staking::CurrentEra::<T>::get().unwrap_or_default();
			let eras_to_check = {
				let bonding_duration = <T as pallet_staking::Config>::BondingDuration::get();

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
				// final_eras_to_check.
				total_check_range
					.into_iter()
					.filter(|e| !checked.contains(e))
					.take(final_eras_to_check as usize)
					.collect::<Vec<_>>()
			};

			log!(debug, "{} eras to check: {:?}", eras_to_check.len(), eras_to_check);

			if eras_to_check.is_empty() {
				// `stash` is not exposed in any era now -- we can let go of them now.
				let num_slashing_spans = Staking::<T>::slashing_spans(&stash).iter().count() as u32;

				let ctrl = match pallet_staking::Bonded::<T>::get(&stash) {
					Some(ctrl) => ctrl,
					None => {
						Self::deposit_event(Event::<T>::Errored { stash });
						return <T as Config>::WeightInfo::on_idle_unstake()
					},
				};

				let ledger = match pallet_staking::Ledger::<T>::get(ctrl) {
					Some(ledger) => ledger,
					None => {
						Self::deposit_event(Event::<T>::Errored { stash });
						return <T as Config>::WeightInfo::on_idle_unstake()
					},
				};

				let unstake_result = pallet_staking::Pallet::<T>::force_unstake(
					RawOrigin::Root.into(),
					stash.clone(),
					num_slashing_spans,
				);

				let pool_stake_result = if let Some(pool_id) = maybe_pool_id {
					pallet_nomination_pools::Pallet::<T>::join(
						RawOrigin::Signed(stash.clone()).into(),
						ledger.total,
						pool_id,
					)
				} else {
					Ok(())
				};

				let result = unstake_result.and(pool_stake_result);
				Self::deposit_event(Event::<T>::Unstaked { stash, maybe_pool_id, result });

				<T as Config>::WeightInfo::on_idle_unstake()
			} else {
				// eras remaining to be checked.
				let mut eras_checked = 0u32;
				let is_exposed = eras_to_check.iter().any(|e| {
					eras_checked.saturating_inc();
					Self::is_exposed_in_era(&stash, e)
				});

				log!(
					debug,
					"checked {:?} eras, (v: {:?}, u: {:?})",
					eras_checked,
					validator_count,
					eras_to_check.len()
				);

				// NOTE: you can be extremely unlucky and get slashed here: You are not exposed in
				// the last 28 eras, have registered yourself to be unstaked, midway being checked,
				// you are exposed.
				if is_exposed {
					let amount = T::SlashPerEra::get().saturating_mul(eras_checked.into());
					pallet_staking::slashing::do_slash::<T>(
						&stash,
						amount,
						&mut Default::default(),
						&mut Default::default(),
						current_era,
					);
					Self::deposit_event(Event::<T>::Slashed { stash, amount });
				} else {
					// Not exposed in these two eras.
					checked.extend(eras_to_check.clone());
					Head::<T>::put(UnstakeRequest { stash: stash.clone(), checked, maybe_pool_id });
					Self::deposit_event(Event::<T>::Checked { stash, eras: eras_to_check });
				}

				<T as Config>::WeightInfo::on_idle_check(validator_count, final_eras_to_check)
			}
		}

		/// Checks whether an account `who` has been exposed in an era.
		fn is_exposed_in_era(who: &T::AccountId, era: &EraIndex) -> bool {
			pallet_staking::ErasStakers::<T>::iter_prefix(era)
				.any(|(_, exposures)| exposures.others.iter().any(|i| i.who == *who))
		}
	}

	#[derive(Encode, Decode, Clone, Eq, PartialEq, TypeInfo, RuntimeDebugNoBound)]
	#[scale_info(skip_type_params(T))]
	pub struct PreventStakingOpsIfUnbonding<T: Config + Send + Sync>(
		sp_std::marker::PhantomData<T>,
	);

	impl<T: Config + Send + Sync> sp_runtime::traits::SignedExtension
		for PreventStakingOpsIfUnbonding<T>
	where
		<T as frame_system::Config>::Call: IsSubType<pallet_staking::Call<T>>,
	{
		type AccountId = T::AccountId;
		type Call = <T as frame_system::Config>::Call;
		type AdditionalSigned = ();
		type Pre = ();
		const IDENTIFIER: &'static str = "PreventStakingOpsIfUnbonding";

		fn additional_signed(&self) -> Result<Self::AdditionalSigned, TransactionValidityError> {
			Ok(())
		}

		fn pre_dispatch(
			self,
			// NOTE: we want to prevent this stash-controller pair from doing anything in the
			// staking system as long as they are registered here. `who` can be a stash or a
			// controller.
			stash_or_controller: &Self::AccountId,
			call: &Self::Call,
			_info: &sp_runtime::traits::DispatchInfoOf<Self::Call>,
			_len: usize,
		) -> Result<Self::Pre, TransactionValidityError> {
			// we don't check this in the tx-pool as it requires a storage read.
			if <Self::Call as IsSubType<pallet_staking::Call<T>>>::is_sub_type(call).is_some() {
				let check_stash = |stash: &T::AccountId| {
					if Queue::<T>::contains_key(&stash) ||
						Head::<T>::get().map_or(false, |u| &u.stash == stash)
					{
						Err(TransactionValidityError::Invalid(InvalidTransaction::Call))
					} else {
						Ok(())
					}
				};
				match (
					pallet_staking::Ledger::<T>::get(&stash_or_controller),
					pallet_staking::Bonded::<T>::get(&stash_or_controller),
				) {
					(Some(ledger), None) => {
						// it is a controller.
						check_stash(&ledger.stash)
					},
					(_, Some(_)) => {
						// it is a stash.
						let stash = stash_or_controller;
						check_stash(stash)
					},
					(None, None) => {
						// They are not a staker -- let them execute.
						Ok(())
					},
				}
			} else {
				Ok(())
			}
		}
	}
}
