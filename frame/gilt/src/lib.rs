// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! # Gilt Pallet
//! A pallet allowing accounts to auction for being frozen and receive open-ended
//! inflation-protection in return.
//!
//! ## Overview
//!
//! Lock up tokens, for at least as long as you offer, and be free from both inflation and
//! intermediate reward or exchange until the tokens become unlocked.
//!
//! ## Design
//!
//! Queues for each of 1-`QueueCount` periods, given in blocks (`Period`). Queues are limited in
//! size to something sensible, `MaxQueueLen`. A secondary storage item with `QueueCount` x `u32`
//! elements with the number of items in each queue.
//!
//! Queues are split into two parts. The first part is a priority queue based on bid size. The
//! second part is just a FIFO (the size of the second part is set with `FifoQueueLen`). Items are
//! always prepended so that removal is always O(1) since removal often happens many times under a
//! single weighed function (`on_initialize`) yet placing bids only ever happens once per weighed
//! function (`place_bid`). If the queue has a priority portion, then it remains sorted in order of
//! bid size so that smaller bids fall off as it gets too large.
//!
//! Account may enqueue a balance with some number of `Period`s lock up, up to a maximum of
//! `QueueCount`. The balance gets reserved. There's a minimum of `MinFreeze` to avoid dust.
//!
//! Until your bid is turned into an issued gilt you can retract it instantly and the funds are
//! unreserved.
//!
//! There's a target proportion of effective total issuance (i.e. accounting for existing gilts)
//! which the we attempt to have frozen at any one time. It will likely be gradually increased over
//! time by governance.
//!
//! As the total funds frozen under gilts drops below `FrozenFraction` of the total effective
//! issuance, then bids are taken from queues, with the queue of the greatest period taking
//! priority. If the item in the queue's locked amount is greater than the amount left to be
//! frozen, then it is split up into multiple bids and becomes partially frozen under gilt.
//!
//! Once an account's balance is frozen, it remains frozen until the owner thaws the balance of the
//! account. This may happen no earlier than queue's period after the point at which the gilt is
//! issued.
//!
//! ## Suggested Values
//!
//! - `QueueCount`: 300
//! - `Period`: 432,000
//! - `MaxQueueLen`: 1000
//! - `MinFreeze`: Around CHF 100 in value.

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;
mod benchmarking;
pub mod weights;

#[frame_support::pallet]
pub mod pallet {
	use sp_std::prelude::*;
	use sp_arithmetic::{Perquintill, PerThing};
	use sp_runtime::traits::{Zero, Saturating, SaturatedConversion};
	use frame_support::traits::{Currency, OnUnbalanced, ReservableCurrency};
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	pub use crate::weights::WeightInfo;

	type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
	type PositiveImbalanceOf<T> =
		<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::PositiveImbalance;
	type NegativeImbalanceOf<T> =
		<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::NegativeImbalance;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// Overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// Currency type that this works on.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// Origin required for setting the target proportion to be under gilt.
		type AdminOrigin: EnsureOrigin<Self::Origin>;

		/// Unbalanced handler to account for funds created (in case of a higher total issuance over
		/// freezing period).
		type Deficit: OnUnbalanced<PositiveImbalanceOf<Self>>;

		/// Unbalanced handler to account for funds destroyed (in case of a lower total issuance
		/// over freezing period).
		type Surplus: OnUnbalanced<NegativeImbalanceOf<Self>>;

		/// Number of duration queues in total. This sets the maximum duration supported, which is
		/// this value multiplied by `Period`.
		#[pallet::constant]
		type QueueCount: Get<u32>;

		/// Maximum number of items that may be in each duration queue.
		#[pallet::constant]
		type MaxQueueLen: Get<u32>;

		/// Portion of the queue which is free from ordering and just a FIFO.
		///
		/// Must be no greater than `MaxQueueLen`.
		#[pallet::constant]
		type FifoQueueLen: Get<u32>;

		/// The base period for the duration queues. This is the common multiple across all
		/// supported freezing durations that can be bid upon.
		#[pallet::constant]
		type Period: Get<Self::BlockNumber>;

		/// The minimum amount of funds that may be offered to freeze for a gilt. Note that this
		/// does not actually limit the amount which may be frozen in a gilt since gilts may be
		/// split up in order to satisfy the desired amount of funds under gilts.
		///
		/// It should be at least big enough to ensure that there is no possible storage spam attack
		/// or queue-filling attack.
		#[pallet::constant]
		type MinFreeze: Get<BalanceOf<Self>>;

		/// The number of blocks between consecutive attempts to issue more gilts in an effort to
		/// get to the target amount to be frozen.
		///
		/// A larger value results in fewer storage hits each block, but a slower period to get to
		/// the target.
		#[pallet::constant]
		type IntakePeriod: Get<Self::BlockNumber>;

		/// The maximum amount of bids that can be turned into issued gilts each block. A larger
		/// value here means less of the block available for transactions should there be a glut of
		/// bids to make into gilts to reach the target.
		#[pallet::constant]
		type MaxIntakeBids: Get<u32>;

		/// Information on runtime weights.
		type WeightInfo: WeightInfo;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	/// A single bid on a gilt, an item of a *queue* in `Queues`.
	#[derive(Clone, Eq, PartialEq, Default, Encode, Decode, RuntimeDebug)]
	pub struct GiltBid<Balance, AccountId> {
		/// The amount bid.
		pub amount: Balance,
		/// The owner of the bid.
		pub who: AccountId,
	}

	/// Information representing an active gilt.
	#[derive(Clone, Eq, PartialEq, Default, Encode, Decode, RuntimeDebug)]
	pub struct ActiveGilt<Balance, AccountId, BlockNumber> {
		/// The proportion of the effective total issuance (i.e. accounting for any eventual gilt
		/// expansion or contraction that may eventually be claimed).
		pub proportion: Perquintill,
		/// The amount reserved under this gilt.
		pub amount: Balance,
		/// The account to whom this gilt belongs.
		pub who: AccountId,
		/// The time after which this gilt can be redeemed for the proportional amount of balance.
		pub expiry: BlockNumber,
	}

	/// An index for a gilt.
	pub type ActiveIndex = u32;

	/// Overall information package on the active gilts.
	///
	/// The way of determining the net issuance (i.e. after factoring in all maturing frozen funds)
	/// is:
	///
	/// `total_issuance - frozen + proportion * total_issuance`
	#[derive(Clone, Eq, PartialEq, Default, Encode, Decode, RuntimeDebug)]
	pub struct ActiveGiltsTotal<Balance> {
		/// The total amount of funds held in reserve for all active gilts.
		pub frozen: Balance,
		/// The proportion of funds that the `frozen` balance represents to total issuance.
		pub proportion: Perquintill,
		/// The total number of gilts issued so far.
		pub index: ActiveIndex,
		/// The target proportion of gilts within total issuance.
		pub target: Perquintill,
	}

	/// The totals of items and balances within each queue. Saves a lot of storage reads in the
	/// case of sparsely packed queues.
	///
	/// The vector is indexed by duration in `Period`s, offset by one, so information on the queue
	/// whose duration is one `Period` would be storage `0`.
	#[pallet::storage]
	pub type QueueTotals<T> = StorageValue<_, Vec<(u32, BalanceOf<T>)>, ValueQuery>;

	/// The queues of bids ready to become gilts. Indexed by duration (in `Period`s).
	#[pallet::storage]
	pub type Queues<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		u32,
		Vec<GiltBid<BalanceOf<T>, T::AccountId>>,
		ValueQuery,
	>;

	/// Information relating to the gilts currently active.
	#[pallet::storage]
	pub type ActiveTotal<T> = StorageValue<_, ActiveGiltsTotal<BalanceOf<T>>, ValueQuery>;

	/// The currently active gilts, indexed according to the order of creation.
	#[pallet::storage]
	pub type Active<T> = StorageMap<
		_,
		Blake2_128Concat,
		ActiveIndex,
		ActiveGilt<BalanceOf<T>, <T as frame_system::Config>::AccountId, <T as frame_system::Config>::BlockNumber>,
		OptionQuery,
	>;

	#[pallet::genesis_config]
	#[derive(Default)]
	pub struct GenesisConfig;

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig {
	 	fn build(&self) {
			QueueTotals::<T>::put(vec![(0, BalanceOf::<T>::zero()); T::QueueCount::get() as usize]);
		}
	}

	#[pallet::event]
	#[pallet::metadata(T::AccountId = "AccountId")]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A bid was successfully placed.
		/// \[ who, amount, duration \]
		BidPlaced(T::AccountId, BalanceOf<T>, u32),
		/// A bid was successfully removed (before being accepted as a gilt).
		/// \[ who, amount, duration \]
		BidRetracted(T::AccountId, BalanceOf<T>, u32),
		/// A bid was accepted as a gilt. The balance may not be released until expiry.
		/// \[ index, expiry, who, amount \]
		GiltIssued(ActiveIndex, T::BlockNumber, T::AccountId, BalanceOf<T>),
		/// An expired gilt has been thawed.
		/// \[ index, who, original_amount, additional_amount \]
		GiltThawed(ActiveIndex, T::AccountId, BalanceOf<T>, BalanceOf<T>),
	}

	#[pallet::error]
	pub enum Error<T> {
		/// The duration of the bid is less than one.
		DurationTooSmall,
		/// The duration is the bid is greater than the number of queues.
		DurationTooBig,
		/// The amount of the bid is less than the minimum allowed.
		AmountTooSmall,
		/// The queue for the bid's duration is full and the amount bid is too low to get in through
		/// replacing an existing bid.
		BidTooLow,
		/// Gilt index is unknown.
		Unknown,
		/// Not the owner of the gilt.
		NotOwner,
		/// Gilt not yet at expiry date.
		NotExpired,
		/// The given bid for retraction is not found.
		NotFound,
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(n: T::BlockNumber) -> Weight {
			if (n % T::IntakePeriod::get()).is_zero() {
				Self::pursue_target(T::MaxIntakeBids::get())
			} else {
				0
			}
		}
	}

	#[pallet::call]
	impl<T:Config> Pallet<T> {
		/// Place a bid for a gilt to be issued.
		///
		/// Origin must be Signed, and account must have at least `amount` in free balance.
		///
		/// - `amount`: The amount of the bid; these funds will be reserved. If the bid is
		/// successfully elevated into an issued gilt, then these funds will continue to be
		/// reserved until the gilt expires. Must be at least `MinFreeze`.
		/// - `duration`: The number of periods for which the funds will be locked if the gilt is
		/// issued. It will expire only after this period has elapsed after the point of issuance.
		/// Must be greater than 1 and no more than `QueueCount`.
		///
		/// Complexities:
		/// - `Queues[duration].len()` (just take max).
		#[pallet::weight(T::WeightInfo::place_bid_max())]
		pub fn place_bid(
			origin: OriginFor<T>,
			#[pallet::compact] amount: BalanceOf<T>,
			duration: u32,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			ensure!(amount >= T::MinFreeze::get(), Error::<T>::AmountTooSmall);
			let queue_count = T::QueueCount::get() as usize;
			let queue_index = duration.checked_sub(1)
				.ok_or(Error::<T>::DurationTooSmall)? as usize;
			ensure!(queue_index < queue_count, Error::<T>::DurationTooBig);

			let net = Queues::<T>::try_mutate(duration, |q|
				-> Result<(u32, BalanceOf::<T>), DispatchError>
			{
				let queue_full = q.len() == T::MaxQueueLen::get() as usize;
				ensure!(!queue_full || q[0].amount < amount, Error::<T>::BidTooLow);
				T::Currency::reserve(&who, amount)?;

				// queue is <Ordered: Lowest ... Highest><Fifo: Last ... First>
				let mut bid = GiltBid { amount, who: who.clone() };
				let net = if queue_full {
					sp_std::mem::swap(&mut q[0], &mut bid);
					T::Currency::unreserve(&bid.who, bid.amount);
					(0, amount - bid.amount)
				} else {
					q.insert(0, bid);
					(1, amount)
				};

				let sorted_item_count = q.len().saturating_sub(T::FifoQueueLen::get() as usize);
				if sorted_item_count > 1 {
					q[0..sorted_item_count].sort_by_key(|x| x.amount);
				}

				Ok(net)
			})?;
			QueueTotals::<T>::mutate(|qs| {
				qs.resize(queue_count, (0, Zero::zero()));
				qs[queue_index].0 += net.0;
				qs[queue_index].1 = qs[queue_index].1.saturating_add(net.1);
			});
			Self::deposit_event(Event::BidPlaced(who.clone(), amount, duration));

			Ok(().into())
		}

		/// Retract a previously placed bid.
		///
		/// Origin must be Signed, and the account should have previously issued a still-active bid
		/// of `amount` for `duration`.
		///
		/// - `amount`: The amount of the previous bid.
		/// - `duration`: The duration of the previous bid.
		#[pallet::weight(T::WeightInfo::place_bid(T::MaxQueueLen::get()))]
		pub fn retract_bid(
			origin: OriginFor<T>,
			#[pallet::compact] amount: BalanceOf<T>,
			duration: u32,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			let queue_count = T::QueueCount::get() as usize;
			let queue_index = duration.checked_sub(1)
				.ok_or(Error::<T>::DurationTooSmall)? as usize;
			ensure!(queue_index < queue_count, Error::<T>::DurationTooBig);

			let bid = GiltBid { amount, who };
			let new_len = Queues::<T>::try_mutate(duration, |q| -> Result<u32, DispatchError> {
				let pos = q.iter().position(|i| i == &bid).ok_or(Error::<T>::NotFound)?;
				q.remove(pos);
				Ok(q.len() as u32)
			})?;

			QueueTotals::<T>::mutate(|qs| {
				qs.resize(queue_count, (0, Zero::zero()));
				qs[queue_index].0 = new_len;
				qs[queue_index].1 = qs[queue_index].1.saturating_sub(bid.amount);
			});

			T::Currency::unreserve(&bid.who, bid.amount);
			Self::deposit_event(Event::BidRetracted(bid.who, bid.amount, duration));

			Ok(().into())
		}

		/// Set target proportion of gilt-funds.
		///
		/// Origin must be `AdminOrigin`.
		///
		/// - `target`: The target proportion of effective issued funds that should be under gilts
		/// at any one time.
		#[pallet::weight(T::WeightInfo::set_target())]
		pub fn set_target(
			origin: OriginFor<T>,
			#[pallet::compact] target: Perquintill,
		) -> DispatchResultWithPostInfo {
			T::AdminOrigin::ensure_origin(origin)?;
			ActiveTotal::<T>::mutate(|totals| totals.target = target);
			Ok(().into())
		}

		/// Remove an active but expired gilt. Reserved funds under gilt are freed and balance is
		/// adjusted to ensure that the funds grow or shrink to maintain the equivalent proportion
		/// of effective total issued funds.
		///
		/// Origin must be Signed and the account must be the owner of the gilt of the given index.
		///
		/// - `index`: The index of the gilt to be thawed.
		#[pallet::weight(T::WeightInfo::thaw())]
		pub fn thaw(
			origin: OriginFor<T>,
			#[pallet::compact] index: ActiveIndex,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			// Look for `index`
			let gilt = Active::<T>::get(index).ok_or(Error::<T>::Unknown)?;
			// If found, check the owner is `who`.
			ensure!(gilt.who == who, Error::<T>::NotOwner);
			let now = frame_system::Module::<T>::block_number();
			ensure!(now >= gilt.expiry, Error::<T>::NotExpired);
			// Remove it
			Active::<T>::remove(index);

			// Multiply the proportion it is by the total issued.
			let total_issuance = T::Currency::total_issuance();
			ActiveTotal::<T>::mutate(|totals| {
				let nongilt_issuance: u128 = total_issuance.saturating_sub(totals.frozen)
					.saturated_into();
				let effective_issuance = totals.proportion.left_from_one()
					.saturating_reciprocal_mul(nongilt_issuance);
				let gilt_value: BalanceOf<T> = (gilt.proportion * effective_issuance).saturated_into();

				totals.frozen = totals.frozen.saturating_sub(gilt.amount);
				totals.proportion = totals.proportion.saturating_sub(gilt.proportion);

				// Remove or mint the additional to the amount using `Deficit`/`Surplus`.
				if gilt_value > gilt.amount {
					// Unreserve full amount.
					T::Currency::unreserve(&gilt.who, gilt.amount);
					let amount = gilt_value - gilt.amount;
					let deficit = T::Currency::deposit_creating(&gilt.who, amount);
					T::Deficit::on_unbalanced(deficit);
				} else {
					if gilt_value < gilt.amount {
						// We take anything reserved beyond the gilt's final value.
						let rest = gilt.amount - gilt_value;
						// `slash` might seem a little aggressive, but it's the only way to do it
						// in case it's locked into the staking system.
						let surplus = T::Currency::slash_reserved(&gilt.who, rest).0;
						T::Surplus::on_unbalanced(surplus);
					}
					// Unreserve only its new value (less than the amount reserved). Everything
					// should add up, but (defensive) in case it doesn't, unreserve takes lower
					// priority over the funds.
					let err_amt = T::Currency::unreserve(&gilt.who, gilt_value);
					debug_assert!(err_amt.is_zero());
				}

				let e = Event::GiltThawed(index, gilt.who, gilt.amount, gilt_value);
				Self::deposit_event(e);
			});

			Ok(().into())
		}
	}

	impl<T: Config> Pallet<T> {
		/// Attempt to enlarge our gilt-set from bids in order to satisfy our desired target amount
		/// of funds frozen into gilts.
		pub fn pursue_target(max_bids: u32) -> Weight {
			let totals = ActiveTotal::<T>::get();
			if totals.proportion < totals.target {
				let missing = totals.target.saturating_sub(totals.proportion);

				let total_issuance = T::Currency::total_issuance();
				let nongilt_issuance: u128 = total_issuance.saturating_sub(totals.frozen)
					.saturated_into();
				let effective_issuance = totals.proportion.left_from_one()
					.saturating_reciprocal_mul(nongilt_issuance);
				let intake: BalanceOf<T> = (missing * effective_issuance).saturated_into();

				let (bids_taken, queues_hit) = Self::enlarge(intake, max_bids);
				let first_from_each_queue = T::WeightInfo::pursue_target_per_queue(queues_hit);
				let rest_from_each_queue = T::WeightInfo::pursue_target_per_item(bids_taken)
						.saturating_sub(T::WeightInfo::pursue_target_per_item(queues_hit));
				first_from_each_queue + rest_from_each_queue
			} else {
				T::WeightInfo::pursue_target_noop()
			}
		}

		/// Freeze additional funds from queue of bids up to `amount`. Use at most `max_bids`
		/// from the queue.
		///
		/// Return the number of bids taken and the number of distinct queues taken from.
		pub fn enlarge(
			amount: BalanceOf<T>,
			max_bids: u32,
		) -> (u32, u32) {
			let total_issuance = T::Currency::total_issuance();
			let mut remaining = amount;
			let mut bids_taken = 0;
			let mut queues_hit = 0;
			let now = frame_system::Module::<T>::block_number();

			ActiveTotal::<T>::mutate(|totals| {
				QueueTotals::<T>::mutate(|qs| {
					for duration in (1..=T::QueueCount::get()).rev() {
						if qs[duration as usize - 1].0 == 0 {
							continue
						}
						let queue_index = duration as usize - 1;
						let expiry = now.saturating_add(T::Period::get().saturating_mul(duration.into()));
						Queues::<T>::mutate(duration, |q| {
							while let Some(mut bid) = q.pop() {
								if remaining < bid.amount {
									let overflow = bid.amount - remaining;
									bid.amount = remaining;
									q.push(GiltBid { amount: overflow, who: bid.who.clone() });
								}
								let amount = bid.amount;
								// Can never overflow due to block above.
								remaining -= amount;
								// Should never underflow since it should track the total of the bids
								// exactly, but we'll be defensive.
								qs[queue_index].1 = qs[queue_index].1.saturating_sub(bid.amount);

								// Now to activate the bid...
								let nongilt_issuance: u128 = total_issuance.saturating_sub(totals.frozen)
									.saturated_into();
								let effective_issuance = totals.proportion.left_from_one()
									.saturating_reciprocal_mul(nongilt_issuance);
								let n: u128 = amount.saturated_into();
								let d = effective_issuance;
								let proportion = Perquintill::from_rational_approximation(n, d);
								let who = bid.who;
								let index = totals.index;
								totals.frozen += bid.amount;
								totals.proportion = totals.proportion.saturating_add(proportion);
								totals.index += 1;
								let e = Event::GiltIssued(index, expiry, who.clone(), amount);
								Self::deposit_event(e);
								let gilt = ActiveGilt { amount, proportion, who, expiry };
								Active::<T>::insert(index, gilt);

								bids_taken += 1;

								if remaining.is_zero() || bids_taken == max_bids {
									break;
								}
							}
							queues_hit += 1;
							qs[queue_index].0 = q.len() as u32;
						});
						if remaining.is_zero() || bids_taken == max_bids {
							break
						}
					}
				});
			});
			(bids_taken, queues_hit)
		}
	}
}
