// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! # Non-Interactive Staking (NIS) Pallet
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
//! Until your bid is turned into an issued bond you can retract it instantly and the funds are
//! unreserved.
//!
//! There's a target proportion of effective total issuance (i.e. accounting for existing bonds)
//! which the we attempt to have frozen at any one time. It will likely be gradually increased over
//! time by governance.
//!
//! As the total funds frozen under bonds drops below `FrozenFraction` of the total effective
//! issuance, then bids are taken from queues, with the queue of the greatest period taking
//! priority. If the item in the queue's locked amount is greater than the amount left to be
//! frozen, then it is split up into multiple bids and becomes partially frozen under bond.
//!
//! Once an account's balance is frozen, it remains frozen until the owner thaws the balance of the
//! account. This may happen no earlier than queue's period after the point at which the bond is
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

mod benchmarking;
#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;
pub mod weights;

pub struct WithMaximumOf<A: sp_core::TypedGet>(sp_std::marker::PhantomData<A>);
impl<A: sp_core::TypedGet> sp_runtime::traits::Convert<sp_runtime::Perquintill, A::Type>
	for WithMaximumOf<A>
where
	A::Type: Clone + sp_arithmetic::traits::Unsigned + From<u64>,
	u64: TryFrom<A::Type>,
{
	fn convert(a: sp_runtime::Perquintill) -> A::Type {
		a * A::get()
	}
}

// TODO: Partial thawing.

#[frame_support::pallet]
pub mod pallet {
	pub use crate::weights::WeightInfo;
	use frame_support::{
		pallet_prelude::*,
		traits::{
			fungible::{Inspect as FungibleInspect, Mutate as FungibleMutate},
			nonfungible::{Inspect as NonfungibleInspect, Transfer as NonfungibleTransfer},
			Currency, Defensive, DefensiveSaturating,
			ExistenceRequirement::AllowDeath,
			OnUnbalanced, ReservableCurrency,
		},
		PalletId,
	};
	use frame_system::pallet_prelude::*;
	use sp_arithmetic::{PerThing, Perquintill};
	use sp_runtime::{
		traits::{AccountIdConversion, Convert, Saturating, Zero},
		TokenError,
	};
	use sp_std::prelude::*;

	type BalanceOf<T> =
		<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
	type PositiveImbalanceOf<T> = <<T as Config>::Currency as Currency<
		<T as frame_system::Config>::AccountId,
	>>::PositiveImbalance;
	type NegativeImbalanceOf<T> = <<T as Config>::Currency as Currency<
		<T as frame_system::Config>::AccountId,
	>>::NegativeImbalance;

	pub struct NoCounterpart<T>(sp_std::marker::PhantomData<T>);
	impl<T> FungibleInspect<T> for NoCounterpart<T> {
		type Balance = u32;
		fn total_issuance() -> u32 {
			0
		}
		fn minimum_balance() -> u32 {
			0
		}
		fn balance(_who: &T) -> u32 {
			0
		}
		fn reducible_balance(_who: &T, _keep_alive: bool) -> u32 {
			0
		}
		fn can_deposit(
			_who: &T,
			_amount: u32,
			_mint: bool,
		) -> frame_support::traits::tokens::DepositConsequence {
			frame_support::traits::tokens::DepositConsequence::Success
		}
		fn can_withdraw(
			_who: &T,
			_amount: u32,
		) -> frame_support::traits::tokens::WithdrawConsequence<u32> {
			frame_support::traits::tokens::WithdrawConsequence::Success
		}
	}
	impl<T> FungibleMutate<T> for NoCounterpart<T> {
		fn mint_into(_who: &T, _amount: u32) -> DispatchResult {
			Ok(())
		}
		fn burn_from(_who: &T, _amount: u32) -> Result<u32, DispatchError> {
			Ok(0)
		}
	}
	impl<T> Convert<Perquintill, u32> for NoCounterpart<T> {
		fn convert(_: Perquintill) -> u32 {
			0
		}
	}

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// Information on runtime weights.
		type WeightInfo: WeightInfo;

		/// Overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Currency type that this works on.
		type Currency: ReservableCurrency<Self::AccountId, Balance = Self::CurrencyBalance>;

		/// Just the `Currency::Balance` type; we have this item to allow us to constrain it to
		/// `From<u64>`.
		type CurrencyBalance: sp_runtime::traits::AtLeast32BitUnsigned
			+ codec::FullCodec
			+ Copy
			+ MaybeSerializeDeserialize
			+ sp_std::fmt::Debug
			+ Default
			+ From<u64>
			+ TypeInfo
			+ MaxEncodedLen;

		/// Origin required for setting the target proportion to be under bond.
		type AdminOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// Unbalanced handler to account for funds created (in case of a higher total issuance over
		/// freezing period).
		type Deficit: OnUnbalanced<PositiveImbalanceOf<Self>>;

		/// Unbalanced handler to account for funds destroyed (in case of a lower total issuance
		/// over freezing period).
		type Surplus: OnUnbalanced<NegativeImbalanceOf<Self>>;

		/// The issuance to ignore. This is subtracted from the `Currency`'s `total_issuance` to get
		/// the issuance with which we determine the thawed value of a bond.
		type IgnoredIssuance: Get<BalanceOf<Self>>;

		type Counterpart: FungibleMutate<Self::AccountId>;

		type CounterpartAmount: Convert<
			Perquintill,
			<Self::Counterpart as FungibleInspect<Self::AccountId>>::Balance,
		>;

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

		/// The minimum amount of funds that may be offered to freeze for a bond. Note that this
		/// does not actually limit the amount which may be frozen in a bond since bonds may be
		/// split up in order to satisfy the desired amount of funds under bonds.
		///
		/// It should be at least big enough to ensure that there is no possible storage spam attack
		/// or queue-filling attack.
		#[pallet::constant]
		type MinFreeze: Get<BalanceOf<Self>>;

		/// The number of blocks between consecutive attempts to issue more bonds in an effort to
		/// get to the target amount to be frozen.
		///
		/// A larger value results in fewer storage hits each block, but a slower period to get to
		/// the target.
		#[pallet::constant]
		type IntakePeriod: Get<Self::BlockNumber>;

		/// The maximum amount of bids that can become bonds each block. A larger
		/// value here means less of the block available for transactions should there be a glut of
		/// bids to make into bonds to reach the target.
		#[pallet::constant]
		type MaxIntakeBids: Get<u32>;

		/// The treasury's pallet id, used for deriving its sovereign account ID.
		#[pallet::constant]
		type PalletId: Get<PalletId>;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	/// A single bid on a bond, an item of a *queue* in `Queues`.
	#[derive(
		Clone, Eq, PartialEq, Default, Encode, Decode, RuntimeDebug, TypeInfo, MaxEncodedLen,
	)]
	pub struct Bid<Balance, AccountId> {
		/// The amount bid.
		pub amount: Balance,
		/// The owner of the bid.
		pub who: AccountId,
	}

	/// Information representing an active bond.
	#[derive(
		Clone, Eq, PartialEq, Default, Encode, Decode, RuntimeDebug, TypeInfo, MaxEncodedLen,
	)]
	pub struct ReceiptRecord<Balance, AccountId, BlockNumber> {
		/// The proportion of the effective total issuance (i.e. accounting for any eventual bond
		/// expansion or contraction that may eventually be claimed).
		pub proportion: Perquintill,
		/// The amount reserved under this bond.
		pub amount: Balance,
		/// The account to whom this bond belongs.
		pub who: AccountId,
		/// The time after which this bond can be redeemed for the proportional amount of balance.
		pub expiry: BlockNumber,
	}

	/// An index for a bond.
	pub type ActiveIndex = u32;

	/// Overall information package on the active bonds.
	///
	/// The way of determining the net issuance (i.e. after factoring in all maturing frozen funds)
	/// is:
	///
	/// `issuance - frozen + proportion * issuance`
	///
	/// where `issuance = total_issuance - IgnoredIssuance`
	#[derive(
		Clone, Eq, PartialEq, Default, Encode, Decode, RuntimeDebug, TypeInfo, MaxEncodedLen,
	)]
	pub struct SummaryRecord<Balance> {
		/// The total amount of funds held in reserve for all active bonds.
		pub frozen: Balance,
		/// The proportion of funds that the `frozen` balance represents to total issuance.
		pub proportion: Perquintill,
		/// The total number of bonds issued so far.
		pub index: ActiveIndex,
		/// The target proportion of bonds within total issuance.
		pub target: Perquintill,
	}

	/// The totals of items and balances within each queue. Saves a lot of storage reads in the
	/// case of sparsely packed queues.
	///
	/// The vector is indexed by duration in `Period`s, offset by one, so information on the queue
	/// whose duration is one `Period` would be storage `0`.
	#[pallet::storage]
	pub type QueueTotals<T: Config> =
		StorageValue<_, BoundedVec<(u32, BalanceOf<T>), T::QueueCount>, ValueQuery>;

	/// The queues of bids ready to become bonds. Indexed by duration (in `Period`s).
	#[pallet::storage]
	pub type Queues<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		u32,
		BoundedVec<Bid<BalanceOf<T>, T::AccountId>, T::MaxQueueLen>,
		ValueQuery,
	>;

	/// Information relating to the bonds currently active.
	#[pallet::storage]
	pub type Summary<T> = StorageValue<_, SummaryRecord<BalanceOf<T>>, ValueQuery>;

	/// The currently active bonds, indexed according to the order of creation.
	#[pallet::storage]
	pub type Receipts<T> = StorageMap<
		_,
		Blake2_128Concat,
		ActiveIndex,
		ReceiptRecord<
			BalanceOf<T>,
			<T as frame_system::Config>::AccountId,
			<T as frame_system::Config>::BlockNumber,
		>,
		OptionQuery,
	>;

	#[pallet::genesis_config]
	#[derive(Default)]
	pub struct GenesisConfig;

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig {
		fn build(&self) {
			let unbounded = vec![(0, BalanceOf::<T>::zero()); T::QueueCount::get() as usize];
			let bounded: BoundedVec<_, _> = unbounded
				.try_into()
				.expect("QueueTotals should support up to QueueCount items. qed");
			QueueTotals::<T>::put(bounded);
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A bid was successfully placed.
		BidPlaced { who: T::AccountId, amount: BalanceOf<T>, duration: u32 },
		/// A bid was successfully removed (before being accepted).
		BidRetracted { who: T::AccountId, amount: BalanceOf<T>, duration: u32 },
		/// A bid was accepted. The balance may not be released until expiry.
		Issued {
			index: ActiveIndex,
			expiry: T::BlockNumber,
			who: T::AccountId,
			amount: BalanceOf<T>,
		},
		/// An expired bond has been thawed.
		Thawed {
			index: ActiveIndex,
			who: T::AccountId,
			original_amount: BalanceOf<T>,
			additional_amount: BalanceOf<T>,
		},
	}

	#[pallet::error]
	pub enum Error<T> {
		/// The duration of the bid is less than one.
		DurationTooSmall,
		/// The duration is the bid is greater than the number of queues.
		DurationTooBig,
		/// The amount of the bid is less than the minimum allowed.
		AmountTooSmall,
		/// The queue for the bid's duration is full and the amount bid is too low to get in
		/// through replacing an existing bid.
		BidTooLow,
		/// Bond index is unknown.
		Unknown,
		/// Not the owner of the bond.
		NotOwner,
		/// Bond not yet at expiry date.
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
				Weight::zero()
			}
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Place a bid for a bond.
		///
		/// Origin must be Signed, and account must have at least `amount` in free balance.
		///
		/// - `amount`: The amount of the bid; these funds will be reserved. If the bid is
		/// successfully elevated into a bond, then these funds will continue to be
		/// reserved until the bond thaws. Must be at least `MinFreeze`.
		/// - `duration`: The number of periods before which the bond may be thawed.
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
			let queue_index = duration.checked_sub(1).ok_or(Error::<T>::DurationTooSmall)? as usize;
			ensure!(queue_index < queue_count, Error::<T>::DurationTooBig);

			let net = Queues::<T>::try_mutate(
				duration,
				|q| -> Result<(u32, BalanceOf<T>), DispatchError> {
					let queue_full = q.len() == T::MaxQueueLen::get() as usize;
					// ensure!(have_reserved(q[0].amount));
					ensure!(!queue_full || q[0].amount < amount, Error::<T>::BidTooLow);
					T::Currency::transfer(&who, &Self::account_id(), amount, AllowDeath)?;

					// queue is <Ordered: Lowest ... Highest><Fifo: Last ... First>
					let mut bid = Bid { amount, who: who.clone() };
					let net = if queue_full {
						sp_std::mem::swap(&mut q[0], &mut bid);
						let _ = T::Currency::transfer(
							&Self::account_id(),
							&bid.who,
							bid.amount,
							AllowDeath,
						);
						(0, amount - bid.amount)
					} else {
						q.try_insert(0, bid).expect("verified queue was not full above. qed.");
						(1, amount)
					};

					let sorted_item_count = q.len().saturating_sub(T::FifoQueueLen::get() as usize);
					if sorted_item_count > 1 {
						q[0..sorted_item_count].sort_by_key(|x| x.amount);
					}

					Ok(net)
				},
			)?;
			QueueTotals::<T>::mutate(|qs| {
				qs.bounded_resize(queue_count, (0, Zero::zero()));
				qs[queue_index].0 += net.0;
				qs[queue_index].1 = qs[queue_index].1.saturating_add(net.1);
			});
			Self::deposit_event(Event::BidPlaced { who, amount, duration });

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
			let queue_index = duration.checked_sub(1).ok_or(Error::<T>::DurationTooSmall)? as usize;
			ensure!(queue_index < queue_count, Error::<T>::DurationTooBig);
			// TODO: ensure!(have_in_reserve(amount))

			let bid = Bid { amount, who };
			let new_len = Queues::<T>::try_mutate(duration, |q| -> Result<u32, DispatchError> {
				let pos = q.iter().position(|i| i == &bid).ok_or(Error::<T>::NotFound)?;
				q.remove(pos);
				Ok(q.len() as u32)
			})?;

			QueueTotals::<T>::mutate(|qs| {
				qs.bounded_resize(queue_count, (0, Zero::zero()));
				qs[queue_index].0 = new_len;
				qs[queue_index].1 = qs[queue_index].1.saturating_sub(bid.amount);
			});

			let _ = T::Currency::transfer(&Self::account_id(), &bid.who, bid.amount, AllowDeath);
			Self::deposit_event(Event::BidRetracted { who: bid.who, amount: bid.amount, duration });

			Ok(().into())
		}

		/// Set target proportion of bonded-funds.
		///
		/// Origin must be `AdminOrigin`.
		///
		/// - `target`: The target proportion of effective issued funds that should be in bonds
		/// at any one time.
		#[pallet::weight(T::WeightInfo::set_target())]
		pub fn set_target(
			origin: OriginFor<T>,
			#[pallet::compact] target: Perquintill,
		) -> DispatchResultWithPostInfo {
			T::AdminOrigin::ensure_origin(origin)?;
			Summary::<T>::mutate(|totals| totals.target = target);
			Ok(().into())
		}

		/// Remove an active but expired bond. Reserved funds under bond are freed and balance is
		/// adjusted to ensure that the newly freed amount is equivalent to the original amount in
		/// terms of the proportion of effective total issued funds.
		///
		/// Origin must be Signed and the account must be the owner of the bond of the given index.
		///
		/// - `index`: The index of the bond to be thawed.
		#[pallet::weight(T::WeightInfo::thaw())]
		pub fn thaw(
			origin: OriginFor<T>,
			#[pallet::compact] index: ActiveIndex,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			// Look for `index`
			let bond = Receipts::<T>::get(index).ok_or(Error::<T>::Unknown)?;
			// If found, check the owner is `who`.
			ensure!(bond.who == who, Error::<T>::NotOwner);
			let now = frame_system::Pallet::<T>::block_number();
			ensure!(now >= bond.expiry, Error::<T>::NotExpired);

			let fung_eq = T::CounterpartAmount::convert(bond.proportion);
			T::Counterpart::burn_from(&who, fung_eq)?;

			// Remove it
			Receipts::<T>::remove(index);

			// Multiply the proportion it is by the total issued.
			let total_issuance =
				T::Currency::total_issuance().saturating_sub(T::IgnoredIssuance::get());
			Summary::<T>::mutate(|totals| {
				let nonbond_issuance = total_issuance.saturating_sub(totals.frozen);
				let effective_issuance =
					totals.proportion.left_from_one().saturating_reciprocal_mul(nonbond_issuance);
				let bond_value = bond.proportion * effective_issuance;

				totals.frozen = totals.frozen.saturating_sub(bond.amount);
				totals.proportion = totals.proportion.saturating_sub(bond.proportion);

				// Remove or mint the additional to the amount using `Deficit`/`Surplus`.
				if bond_value > bond.amount {
					// Unreserve full amount.
					let _ = T::Currency::transfer(
						&Self::account_id(),
						&bond.who,
						bond.amount,
						AllowDeath,
					)
					.defensive();
					let amount = bond_value - bond.amount;
					let deficit = T::Currency::deposit_creating(&bond.who, amount);
					T::Deficit::on_unbalanced(deficit);
				} else {
					if bond_value < bond.amount {
						// We take anything reserved beyond the bond's final value.
						let rest = bond.amount - bond_value;
						// `slash` might seem a little aggressive, but it's the only way to do it
						// in case it's locked into the staking system.
						let surplus = T::Currency::slash(&Self::account_id(), rest).0;
						T::Surplus::on_unbalanced(surplus);
					}
					// Unreserve only its new value (less than the amount reserved). Everything
					// should add up, but (defensive) in case it doesn't, unreserve takes lower
					// priority over the funds.
					let _ = T::Currency::transfer(
						&Self::account_id(),
						&bond.who,
						bond_value,
						AllowDeath,
					)
					.defensive();
				}

				let e = Event::Thawed {
					index,
					who: bond.who,
					original_amount: bond.amount,
					additional_amount: bond_value,
				};
				Self::deposit_event(e);
			});

			Ok(().into())
		}
	}

	/// Issuance information returned by `issuance()`.
	pub struct IssuanceInfo<Balance> {
		/// The balance held in reserve over all active bonds.
		pub reserved: Balance,
		/// The issuance not held in reserve for active bonds. Together with `reserved` this sums
		/// to `Currency::total_issuance`.
		pub non_bond: Balance,
		/// The balance that `reserved` is effectively worth, at present. This is not issued funds
		/// and could be less than `reserved` (though in most cases should be greater).
		pub effective: Balance,
	}

	impl<T: Config> NonfungibleInspect<T::AccountId> for Pallet<T> {
		type ItemId = ActiveIndex;

		fn owner(item: &ActiveIndex) -> Option<T::AccountId> {
			Receipts::<T>::get(item).map(|r| r.who)
		}

		fn attribute(item: &Self::ItemId, key: &[u8]) -> Option<Vec<u8>> {
			let item = Receipts::<T>::get(item)?;
			match key {
				b"proportion" => Some(item.proportion.encode()),
				b"amount" => Some(item.amount.encode()),
				b"expiry" => Some(item.expiry.encode()),
				_ => None,
			}
		}
	}

	impl<T: Config> NonfungibleTransfer<T::AccountId> for Pallet<T> {
		fn transfer(index: &ActiveIndex, destination: &T::AccountId) -> DispatchResult {
			let mut item = Receipts::<T>::get(index).ok_or(TokenError::UnknownAsset)?;
			item.who = destination.clone();
			Receipts::<T>::insert(index, item);
			Ok(())
		}
	}

	impl<T: Config> Pallet<T> {
		/// Get the target amount of bonds that we're aiming for.
		pub fn target() -> Perquintill {
			Summary::<T>::get().target
		}

		/// The account ID of the reserves.
		///
		/// This actually does computation. If you need to keep using it, then make sure you cache
		/// the value and only call this once.
		pub fn account_id() -> T::AccountId {
			T::PalletId::get().into_account_truncating()
		}

		/// Returns information on the issuance of bonds.
		pub fn issuance() -> IssuanceInfo<BalanceOf<T>> {
			let totals = Summary::<T>::get();

			let total_issuance = T::Currency::total_issuance();
			let non_bond = total_issuance.saturating_sub(totals.frozen);
			let effective = totals.proportion.left_from_one().saturating_reciprocal_mul(non_bond);

			IssuanceInfo { reserved: totals.frozen, non_bond, effective }
		}

		/// Attempt to enlarge our bond-set from bids in order to satisfy our desired target amount
		/// of funds frozen into bonds.
		pub fn pursue_target(max_bids: u32) -> Weight {
			let totals = Summary::<T>::get();
			if totals.proportion < totals.target {
				let missing = totals.target.saturating_sub(totals.proportion);

				let total_issuance =
					T::Currency::total_issuance().saturating_sub(T::IgnoredIssuance::get());
				let nonbond_issuance = total_issuance.saturating_sub(totals.frozen);
				let effective_issuance =
					totals.proportion.left_from_one().saturating_reciprocal_mul(nonbond_issuance);
				let intake = missing * effective_issuance;

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
		pub fn enlarge(amount: BalanceOf<T>, max_bids: u32) -> (u32, u32) {
			let total_issuance =
				T::Currency::total_issuance().saturating_sub(T::IgnoredIssuance::get());
			let mut remaining = amount;
			let mut bids_taken = 0;
			let mut queues_hit = 0;
			let now = frame_system::Pallet::<T>::block_number();

			Summary::<T>::mutate(|totals| {
				QueueTotals::<T>::mutate(|qs| {
					for duration in (1..=T::QueueCount::get()).rev() {
						if qs[duration as usize - 1].0 == 0 {
							continue
						}
						let queue_index = duration as usize - 1;
						let expiry =
							now.saturating_add(T::Period::get().saturating_mul(duration.into()));
						Queues::<T>::mutate(duration, |q| {
							while let Some(mut bid) = q.pop() {
								if remaining < bid.amount {
									let overflow = bid.amount - remaining;
									bid.amount = remaining;
									q.try_push(Bid { amount: overflow, who: bid.who.clone() })
										.expect("just popped, so there must be space. qed");
								}
								let amount = bid.amount;

								// Can never overflow due to block above.
								remaining -= amount;
								// Should never underflow since it should track the total of the
								// bids exactly, but we'll be defensive.
								qs[queue_index].1 =
									qs[queue_index].1.defensive_saturating_sub(bid.amount);

								// Now to activate the bid...
								let nonbond_issuance =
									total_issuance.defensive_saturating_sub(totals.frozen);
								let effective_issuance = totals
									.proportion
									.left_from_one()
									.saturating_reciprocal_mul(nonbond_issuance);
								let n = amount;
								let d = effective_issuance;
								let proportion = Perquintill::from_rational(n, d);
								let who = bid.who;
								let index = totals.index;
								totals.frozen += bid.amount;
								totals.proportion =
									totals.proportion.defensive_saturating_add(proportion);
								totals.index += 1;
								let e = Event::Issued { index, expiry, who: who.clone(), amount };
								Self::deposit_event(e);
								let bond =
									ReceiptRecord { amount, proportion, who: who.clone(), expiry };
								Receipts::<T>::insert(index, bond);

								// issue the fungible counterpart
								let fung_eq = T::CounterpartAmount::convert(proportion);
								let _ = T::Counterpart::mint_into(&who, fung_eq).defensive();

								bids_taken += 1;

								if remaining.is_zero() || bids_taken == max_bids {
									break
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
