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

//! > Made with *Substrate*, for *Polkadot*.
//!
//! [![github]](https://github.com/paritytech/substrate/frame/fast-unstake) -
//! [![polkadot]](https://polkadot.network)
//!
//! [polkadot]: https://img.shields.io/badge/polkadot-E6007A?style=for-the-badge&logo=polkadot&logoColor=white
//! [github]: https://img.shields.io/badge/github-8da0cb?style=for-the-badge&labelColor=555555&logo=github
//!
//! # Fast Unstake Pallet
//!
//! A pallet to allow participants of the staking system (represented by [`Config::Staking`], being
//! [`StakingInterface`]) to unstake quicker, if and only if they meet the condition of not being
//! exposed to any slashes.
//!
//! ## Overview
//!
//! If a nominator is not exposed anywhere in the staking system, checked via
//! [`StakingInterface::is_exposed_in_era`] (i.e. "has not actively backed any validators in the
//! last [`StakingInterface::bonding_duration`] days"), then they can register themselves in this
//! pallet and unstake faster than having to wait an entire bonding duration.
//!
//! *Being exposed with validator* from the point of view of the staking system means earning
//! rewards with the validator, and also being at the risk of slashing with the validator. This is
//! equivalent to the "Active Nominator" role explained in
//! [here](https://polkadot.network/blog/staking-update-february-2022/).
//!
//! Stakers who are certain about NOT being exposed can register themselves with
//! [`Pallet::register_fast_unstake`]. This will chill, fully unbond the staker and place them
//! in the queue to be checked.
//!
//! A successful registration implies being fully unbonded and chilled in the staking system. These
//! effects persist even if the fast-unstake registration is retracted (see [`Pallet::deregister`]
//! and further).
//!
//! Once registered as a fast-unstaker, the staker will be queued and checked by the system. This
//! can take a variable number of blocks based on demand, but will almost certainly be "faster" (as
//! the name suggest) than waiting the standard bonding duration.
//!
//! A fast-unstaker is either in [`Queue`] or actively being checked, at which point it lives in
//! [`Head`]. Once in [`Head`], the request cannot be retracted anymore. But, once in [`Queue`], it
//! can, via [`Pallet::deregister`].
//!
//! A deposit equal to [`Config::Deposit`] is collected for this process, and is returned in case a
//! successful unstake occurs (`Event::Unstaked` signals that).
//!
//! Once processed, if successful, no additional fee for the checking process is taken, and the
//! staker is instantly unbonded.
//!
//! If unsuccessful, meaning that the staker was exposed, the aforementioned deposit will be slashed
//! for the amount of wasted work they have inflicted on the chain.
//!
//! All in all, this pallet is meant to provide an easy off-ramp for some stakers.
//!
//! ### Example
//!
//! 1. Fast-unstake with multiple participants in the queue.
#![doc = docify::embed!("src/tests.rs", successful_multi_queue)]
//!
//! 2. Fast unstake failing because a nominator is exposed.
#![doc = docify::embed!("src/tests.rs", exposed_nominator_cannot_unstake)]
//!
//! ## Pallet API
//!
//! See the [`pallet`] module for more information about the interfaces this pallet exposes,
//! including its configuration trait, dispatchables, storage items, events and errors.
//!
//! ## Low Level / Implementation Details
//!
//! This pallet works off the basis of `on_idle`, meaning that it provides no guarantee about when
//! it will succeed, if at all. Moreover, the queue implementation is unordered. In case of
//! congestion, no FIFO ordering is provided.
//!
//! A few important considerations can be concluded based on the `on_idle`-based implementation:
//!
//! * It is crucial for the weights of this pallet to be correct. The code inside
//! [`Pallet::on_idle`] MUST be able to measure itself and report the remaining weight correctly
//! after execution.
//!
//! * If the weight measurement is incorrect, it can lead to perpetual overweight (consequently
//!   slow) blocks.
//!
//! * The amount of weight that `on_idle` consumes is a direct function of [`ErasToCheckPerBlock`].
//!
//! * Thus, a correct value of [`ErasToCheckPerBlock`] (which can be set via [`Pallet::control`])
//!   should be chosen, such that a reasonable amount of weight is used `on_idle`. If
//!   [`ErasToCheckPerBlock`] is too large, `on_idle` will always conclude that it has not enough
//!   weight to proceed, and will early-return. Nonetheless, this should also be *safe* as long as
//!   the benchmarking/weights are *accurate*.
//!
//! * See the inline code-comments on `do_on_idle` (private) for more details.
//!
//! * For further safety, in case of any unforeseen errors, the pallet will emit
//!   [`Event::InternalError`] and set [`ErasToCheckPerBlock`] back to 0, which essentially means
//!   the pallet will halt/disable itself.

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

// NOTE: enable benchmarking in tests as well.
#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
pub mod migrations;
pub mod types;
pub mod weights;

// some extra imports for docs to link properly.
#[cfg(doc)]
pub use frame_support::traits::Hooks;
#[cfg(doc)]
pub use sp_staking::StakingInterface;

/// The logging target of this pallet.
pub const LOG_TARGET: &'static str = "runtime::fast-unstake";

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
	use frame_support::{
		pallet_prelude::*,
		traits::{Defensive, ReservableCurrency, StorageVersion},
	};
	use frame_system::pallet_prelude::*;
	use sp_runtime::{traits::Zero, DispatchResult};
	use sp_staking::{EraIndex, StakingInterface};
	use sp_std::{prelude::*, vec::Vec};
	pub use weights::WeightInfo;

	#[cfg(feature = "try-runtime")]
	use sp_runtime::TryRuntimeError;

	const STORAGE_VERSION: StorageVersion = StorageVersion::new(1);

	#[pallet::pallet]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>
			+ TryInto<Event<Self>>;

		/// The currency used for deposits.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// Deposit to take for unstaking, to make sure we're able to slash the it in order to cover
		/// the costs of resources on unsuccessful unstake.
		#[pallet::constant]
		type Deposit: Get<BalanceOf<Self>>;

		/// The origin that can control this pallet, in other words invoke [`Pallet::control`].
		type ControlOrigin: frame_support::traits::EnsureOrigin<Self::RuntimeOrigin>;

		/// Batch size.
		///
		/// This many stashes are processed in each unstake request.
		type BatchSize: Get<u32>;

		/// The access to staking functionality.
		type Staking: StakingInterface<Balance = BalanceOf<Self>, AccountId = Self::AccountId>;

		/// Maximum value for `ErasToCheckPerBlock`, checked in [`Pallet::control`].
		///
		/// This should be slightly bigger than the actual value in order to have accurate
		/// benchmarks.
		type MaxErasToCheckPerBlock: Get<u32>;

		/// The weight information of this pallet.
		type WeightInfo: WeightInfo;

		/// Use only for benchmarking.
		#[cfg(feature = "runtime-benchmarks")]
		type MaxBackersPerValidator: Get<u32>;
	}

	/// The current "head of the queue" being unstaked.
	///
	/// The head in itself can be a batch of up to [`Config::BatchSize`] stakers.
	#[pallet::storage]
	pub type Head<T: Config> = StorageValue<_, UnstakeRequest<T>, OptionQuery>;

	/// The map of all accounts wishing to be unstaked.
	///
	/// Keeps track of `AccountId` wishing to unstake and it's corresponding deposit.
	// Hasher: Twox safe since `AccountId` is a secure hash.
	#[pallet::storage]
	pub type Queue<T: Config> = CountedStorageMap<_, Twox64Concat, T::AccountId, BalanceOf<T>>;

	/// Number of eras to check per block.
	///
	/// If set to 0, this pallet does absolutely nothing. Cannot be set to more than
	/// [`Config::MaxErasToCheckPerBlock`].
	///
	/// Based on the amount of weight available at [`Pallet::on_idle`], up to this many eras are
	/// checked. The checking is represented by updating [`UnstakeRequest::checked`], which is
	/// stored in [`Head`].
	#[pallet::storage]
	#[pallet::getter(fn eras_to_check_per_block)]
	pub type ErasToCheckPerBlock<T: Config> = StorageValue<_, u32, ValueQuery>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A staker was unstaked.
		Unstaked { stash: T::AccountId, result: DispatchResult },
		/// A staker was slashed for requesting fast-unstake whilst being exposed.
		Slashed { stash: T::AccountId, amount: BalanceOf<T> },
		/// A batch was partially checked for the given eras, but the process did not finish.
		BatchChecked { eras: Vec<EraIndex> },
		/// A batch of a given size was terminated.
		///
		/// This is always follows by a number of `Unstaked` or `Slashed` events, marking the end
		/// of the batch. A new batch will be created upon next block.
		BatchFinished { size: u32 },
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
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_idle(_: BlockNumberFor<T>, remaining_weight: Weight) -> Weight {
			if remaining_weight.any_lt(T::DbWeight::get().reads(2)) {
				return Weight::from_parts(0, 0)
			}

			Self::do_on_idle(remaining_weight)
		}

		fn integrity_test() {
			sp_std::if_std! {
				sp_io::TestExternalities::new_empty().execute_with(|| {
					// ensure that the value of `ErasToCheckPerBlock` is less than
					// `T::MaxErasToCheckPerBlock`.
					assert!(
						ErasToCheckPerBlock::<T>::get() <= T::MaxErasToCheckPerBlock::get(),
						"the value of `ErasToCheckPerBlock` is greater than `T::MaxErasToCheckPerBlock`",
					);
				});
			}
		}

		#[cfg(feature = "try-runtime")]
		fn try_state(_n: BlockNumberFor<T>) -> Result<(), TryRuntimeError> {
			// ensure that the value of `ErasToCheckPerBlock` is less than
			// `T::MaxErasToCheckPerBlock`.
			ensure!(
				ErasToCheckPerBlock::<T>::get() <= T::MaxErasToCheckPerBlock::get(),
				"the value of `ErasToCheckPerBlock` is greater than `T::MaxErasToCheckPerBlock`",
			);

			Ok(())
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Register oneself for fast-unstake.
		///
		/// ## Dispatch Origin
		///
		/// The dispatch origin of this call must be *signed* by whoever is permitted to call
		/// unbond funds by the staking system. See [`Config::Staking`].
		///
		/// ## Details
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
		///
		/// ## Events
		///
		/// Some events from the staking and currency system might be emitted.
		#[pallet::call_index(0)]
		#[pallet::weight(<T as Config>::WeightInfo::register_fast_unstake())]
		pub fn register_fast_unstake(origin: OriginFor<T>) -> DispatchResult {
			let ctrl = ensure_signed(origin)?;

			ensure!(ErasToCheckPerBlock::<T>::get() != 0, <Error<T>>::CallNotAllowed);
			let stash_account =
				T::Staking::stash_by_ctrl(&ctrl).map_err(|_| Error::<T>::NotController)?;
			ensure!(!Queue::<T>::contains_key(&stash_account), Error::<T>::AlreadyQueued);
			ensure!(!Self::is_head(&stash_account), Error::<T>::AlreadyHead);
			ensure!(!T::Staking::is_unbonding(&stash_account)?, Error::<T>::NotFullyBonded);

			// chill and fully unstake.
			T::Staking::chill(&stash_account)?;
			T::Staking::fully_unbond(&stash_account)?;

			T::Currency::reserve(&stash_account, T::Deposit::get())?;

			// enqueue them.
			Queue::<T>::insert(stash_account, T::Deposit::get());
			Ok(())
		}

		/// Deregister oneself from the fast-unstake.
		///
		/// ## Dispatch Origin
		///
		/// The dispatch origin of this call must be *signed* by whoever is permitted to call
		/// unbond funds by the staking system. See [`Config::Staking`].
		///
		/// ## Details
		///
		/// This is useful if one is registered, they are still waiting, and they change their mind.
		///
		/// Note that the associated stash is still fully unbonded and chilled as a consequence of
		/// calling [`Pallet::register_fast_unstake`]. Therefore, this should probably be followed
		/// by a call to `rebond` in the staking system.
		///
		/// ## Events
		///
		/// Some events from the staking and currency system might be emitted.
		#[pallet::call_index(1)]
		#[pallet::weight(<T as Config>::WeightInfo::deregister())]
		pub fn deregister(origin: OriginFor<T>) -> DispatchResult {
			let ctrl = ensure_signed(origin)?;

			ensure!(ErasToCheckPerBlock::<T>::get() != 0, <Error<T>>::CallNotAllowed);

			let stash_account =
				T::Staking::stash_by_ctrl(&ctrl).map_err(|_| Error::<T>::NotController)?;
			ensure!(Queue::<T>::contains_key(&stash_account), Error::<T>::NotQueued);
			ensure!(!Self::is_head(&stash_account), Error::<T>::AlreadyHead);
			let deposit = Queue::<T>::take(stash_account.clone());

			if let Some(deposit) = deposit.defensive() {
				let remaining = T::Currency::unreserve(&stash_account, deposit);
				if !remaining.is_zero() {
					Self::halt("not enough balance to unreserve");
				}
			}

			Ok(())
		}

		/// Control the operation of this pallet.
		///
		/// ## Dispatch Origin
		///
		/// The dispatch origin of this call must be [`Config::ControlOrigin`].
		///
		/// ## Details
		///
		/// Can set the number of eras to check per block, and potentially other admin work.
		///
		/// ## Events
		///
		/// No events are emitted from this dispatch.
		#[pallet::call_index(2)]
		#[pallet::weight(<T as Config>::WeightInfo::control())]
		pub fn control(origin: OriginFor<T>, eras_to_check: EraIndex) -> DispatchResult {
			let _ = T::ControlOrigin::ensure_origin(origin)?;
			ensure!(eras_to_check <= T::MaxErasToCheckPerBlock::get(), Error::<T>::CallNotAllowed);
			ErasToCheckPerBlock::<T>::put(eras_to_check);
			Ok(())
		}
	}

	impl<T: Config> Pallet<T> {
		/// Returns `true` if `staker` is anywhere to be found in the `head`.
		pub(crate) fn is_head(staker: &T::AccountId) -> bool {
			Head::<T>::get().map_or(false, |UnstakeRequest { stashes, .. }| {
				stashes.iter().any(|(stash, _)| stash == staker)
			})
		}

		/// Halt the operations of this pallet.
		pub(crate) fn halt(reason: &'static str) {
			frame_support::defensive!(reason);
			ErasToCheckPerBlock::<T>::put(0);
			Self::deposit_event(Event::<T>::InternalError)
		}

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
			// any weight that is unaccounted for
			let mut unaccounted_weight = Weight::from_parts(0, 0);

			let eras_to_check_per_block = ErasToCheckPerBlock::<T>::get();
			if eras_to_check_per_block.is_zero() {
				return T::DbWeight::get().reads(1).saturating_add(unaccounted_weight)
			}

			// NOTE: here we're assuming that the number of validators has only ever increased,
			// meaning that the number of exposures to check is either this per era, or less.
			let validator_count = T::Staking::desired_validator_count();
			let (next_batch_size, reads_from_queue) = Head::<T>::get()
				.map_or((Queue::<T>::count().min(T::BatchSize::get()), true), |head| {
					(head.stashes.len() as u32, false)
				});

			// determine the number of eras to check. This is based on both `ErasToCheckPerBlock`
			// and `remaining_weight` passed on to us from the runtime executive.
			let max_weight = |v, b| {
				// NOTE: this potentially under-counts by up to `BatchSize` reads from the queue.
				<T as Config>::WeightInfo::on_idle_check(v, b)
					.max(<T as Config>::WeightInfo::on_idle_unstake(b))
					.saturating_add(if reads_from_queue {
						T::DbWeight::get().reads(next_batch_size.into())
					} else {
						Zero::zero()
					})
			};

			if max_weight(validator_count, next_batch_size).any_gt(remaining_weight) {
				log!(debug, "early exit because eras_to_check_per_block is zero");
				return T::DbWeight::get().reads(3).saturating_add(unaccounted_weight)
			}

			if T::Staking::election_ongoing() {
				// NOTE: we assume `ongoing` does not consume any weight.
				// there is an ongoing election -- we better not do anything. Imagine someone is not
				// exposed anywhere in the last era, and the snapshot for the election is already
				// taken. In this time period, we don't want to accidentally unstake them.
				return T::DbWeight::get().reads(4).saturating_add(unaccounted_weight)
			}

			let UnstakeRequest { stashes, mut checked } = match Head::<T>::take().or_else(|| {
				// NOTE: there is no order guarantees in `Queue`.
				let stashes: BoundedVec<_, T::BatchSize> = Queue::<T>::drain()
					.take(T::BatchSize::get() as usize)
					.collect::<Vec<_>>()
					.try_into()
					.expect("take ensures bound is met; qed");
				unaccounted_weight.saturating_accrue(
					T::DbWeight::get().reads_writes(stashes.len() as u64, stashes.len() as u64),
				);
				if stashes.is_empty() {
					None
				} else {
					Some(UnstakeRequest { stashes, checked: Default::default() })
				}
			}) {
				None => {
					// There's no `Head` and nothing in the `Queue`, nothing to do here.
					return T::DbWeight::get().reads(4)
				},
				Some(head) => head,
			};

			log!(
				debug,
				"checking {:?} stashes, eras_to_check_per_block = {:?}, checked {:?}, remaining_weight = {:?}",
				stashes.len(),
				eras_to_check_per_block,
				checked,
				remaining_weight,
			);

			// the range that we're allowed to check in this round.
			let current_era = T::Staking::current_era();
			let bonding_duration = T::Staking::bonding_duration();

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

			let unstake_stash = |stash: T::AccountId, deposit| {
				let result = T::Staking::force_unstake(stash.clone());
				let remaining = T::Currency::unreserve(&stash, deposit);
				if !remaining.is_zero() {
					Self::halt("not enough balance to unreserve");
				} else {
					log!(info, "unstaked {:?}, outcome: {:?}", stash, result);
					Self::deposit_event(Event::<T>::Unstaked { stash, result });
				}
			};

			let check_stash = |stash, deposit| {
				let is_exposed = unchecked_eras_to_check
					.iter()
					.any(|e| T::Staking::is_exposed_in_era(&stash, e));

				if is_exposed {
					T::Currency::slash_reserved(&stash, deposit);
					log!(info, "slashed {:?} by {:?}", stash, deposit);
					Self::deposit_event(Event::<T>::Slashed { stash, amount: deposit });
					false
				} else {
					true
				}
			};

			if unchecked_eras_to_check.is_empty() {
				// `stashes` are not exposed in any era now -- we can let go of them now.
				let size = stashes.len() as u32;
				stashes.into_iter().for_each(|(stash, deposit)| unstake_stash(stash, deposit));
				Self::deposit_event(Event::<T>::BatchFinished { size });
				<T as Config>::WeightInfo::on_idle_unstake(size).saturating_add(unaccounted_weight)
			} else {
				let pre_length = stashes.len();
				let stashes: BoundedVec<(T::AccountId, BalanceOf<T>), T::BatchSize> = stashes
					.into_iter()
					.filter(|(stash, deposit)| check_stash(stash.clone(), *deposit))
					.collect::<Vec<_>>()
					.try_into()
					.expect("filter can only lessen the length; still in bound; qed");
				let post_length = stashes.len();

				log!(
					debug,
					"checked {:?}, pre stashes: {:?}, post: {:?}",
					unchecked_eras_to_check,
					pre_length,
					post_length,
				);

				match checked.try_extend(unchecked_eras_to_check.clone().into_iter()) {
					Ok(_) =>
						if stashes.is_empty() {
							Self::deposit_event(Event::<T>::BatchFinished { size: 0 });
						} else {
							Head::<T>::put(UnstakeRequest { stashes, checked });
							Self::deposit_event(Event::<T>::BatchChecked {
								eras: unchecked_eras_to_check,
							});
						},
					Err(_) => {
						// don't put the head back in -- there is an internal error in the pallet.
						Self::halt("checked is pruned via retain above")
					},
				}

				<T as Config>::WeightInfo::on_idle_check(validator_count, pre_length as u32)
					.saturating_add(unaccounted_weight)
			}
		}
	}
}
