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
//! Queues for each of `1..QueueCount` periods, given in blocks (`Period`). Queues are limited in
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
//! Until your bid is consolidated and you receive a receipt, you can retract it instantly and the
//! funds are unreserved.
//!
//! There's a target proportion of effective total issuance (i.e. accounting for existing receipts)
//! which the pallet attempts to have frozen at any one time. It will likely be gradually increased
//! over time by governance.
//!
//! As the proportion of effective total issuance represented by outstanding receipts drops below
//! `FrozenFraction`, then bids are taken from queues and consolidated into receipts, with the queue
//! of the greatest period taking priority. If the item in the queue's locked amount is greater than
//! the amount remaining to achieve `FrozenFraction`, then it is split up into multiple bids and
//! becomes partially consolidated.
//!
//! With the consolidation of a bid, the bid amount is taken from the owner and a receipt is issued.
//! The receipt records the proportion of the bid compared to effective total issuance at the time
//! of consolidation. The receipt has two independent elements: a "main" non-fungible receipt and
//! a second set of fungible "counterpart" tokens. The accounting functionality of the latter must
//! be provided through the `Counterpart` trait item. The main non-fungible receipt may have its
//! owner transferred through the pallet's implementation of `nonfungible::Transfer`.
//!
//! A later `thaw` function may be called in order to reduce the recorded proportion or entirely
//! remove the receipt in return for the appropriate proportion of the effective total issuance.
//! This may happen no earlier than queue's period after the point at which the receipt was issued.
//! The call must be made by the owner of both the "main" non-fungible receipt and the appropriate
//! amount of counterpart tokens.
//!
//! `NoCounterpart` may be provided as an implementation for the counterpart token system in which
//! case they are completely disregarded from the thawing logic.
//!
//! ## Terms
//!
//! - *Effective total issuance*: The total issuance of balances in the system, including all claims
//!   of all outstanding receipts but excluding `IgnoredIssuance`.

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;
use sp_arithmetic::{traits::Unsigned, RationalArg};
use sp_core::TypedGet;
use sp_runtime::{
	traits::{Convert, ConvertBack},
	Perquintill,
};

mod benchmarking;
#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;
pub mod weights;

pub struct WithMaximumOf<A: TypedGet>(sp_std::marker::PhantomData<A>);
impl<A: TypedGet> Convert<Perquintill, A::Type> for WithMaximumOf<A>
where
	A::Type: Clone + Unsigned + From<u64>,
	u64: TryFrom<A::Type>,
{
	fn convert(a: Perquintill) -> A::Type {
		a * A::get()
	}
}
impl<A: TypedGet> ConvertBack<Perquintill, A::Type> for WithMaximumOf<A>
where
	A::Type: RationalArg + From<u64>,
	u64: TryFrom<A::Type>,
	u128: TryFrom<A::Type>,
{
	fn convert_back(a: A::Type) -> Perquintill {
		Perquintill::from_rational(a, A::get())
	}
}

//TODO: impl `ExchangeAsset`.

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
		traits::{AccountIdConversion, Convert, ConvertBack, Saturating, Zero},
		TokenError,
	};
	use sp_std::prelude::*;

	type BalanceOf<T> =
		<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
	type PositiveImbalanceOf<T> = <<T as Config>::Currency as Currency<
		<T as frame_system::Config>::AccountId,
	>>::PositiveImbalance;
	type ReceiptRecordOf<T> = ReceiptRecord<
		<T as frame_system::Config>::AccountId,
		<T as frame_system::Config>::BlockNumber,
	>;

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

		/// Origin required for auto-funding the deficit.
		type FundOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// The issuance to ignore. This is subtracted from the `Currency`'s `total_issuance` to get
		/// the issuance with which we determine the thawed value of a given proportion.
		type IgnoredIssuance: Get<BalanceOf<Self>>;

		type Counterpart: FungibleMutate<Self::AccountId>;

		type CounterpartAmount: ConvertBack<
			Perquintill,
			<Self::Counterpart as FungibleInspect<Self::AccountId>>::Balance,
		>;

		/// Unbalanced handler to account for funds created (in case of a higher total issuance over
		/// freezing period).
		type Deficit: OnUnbalanced<PositiveImbalanceOf<Self>>;

		/// The target sum of all receipts' proportions.
		type Target: Get<Perquintill>;

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

		/// The minimum amount of funds that may be placed in a bid. Note that this
		/// does not actually limit the amount which may be represented in a receipt since bids may
		/// be split up by the system.
		///
		/// It should be at least big enough to ensure that there is no possible storage spam attack
		/// or queue-filling attack.
		#[pallet::constant]
		type MinFreeze: Get<BalanceOf<Self>>;

		/// The number of blocks between consecutive attempts to dequeue bids and create receipts.
		///
		/// A larger value results in fewer storage hits each block, but a slower period to get to
		/// the target.
		#[pallet::constant]
		type IntakePeriod: Get<Self::BlockNumber>;

		/// The maximum amount of bids that can consolidated into receipts in a single intake. A
		/// larger value here means less of the block available for transactions should there be a
		/// glut of bids.
		#[pallet::constant]
		type MaxIntakeBids: Get<u32>;

		/// The treasury's pallet id, used for deriving its sovereign account ID.
		#[pallet::constant]
		type PalletId: Get<PalletId>;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	/// A single bid, an item of a *queue* in `Queues`.
	#[derive(
		Clone, Eq, PartialEq, Default, Encode, Decode, RuntimeDebug, TypeInfo, MaxEncodedLen,
	)]
	pub struct Bid<Balance, AccountId> {
		/// The amount bid.
		pub amount: Balance,
		/// The owner of the bid.
		pub who: AccountId,
	}

	/// Information representing a receipt.
	#[derive(
		Clone, Eq, PartialEq, Default, Encode, Decode, RuntimeDebug, TypeInfo, MaxEncodedLen,
	)]
	pub struct ReceiptRecord<AccountId, BlockNumber> {
		/// The proportion of the effective total issuance.
		pub proportion: Perquintill,
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
	pub struct SummaryRecord {
		/// The proportion of funds that the `frozen` balance represents to total issuance.
		pub proportion_owed: Perquintill,
		/// The total number of bonds issued so far.
		pub index: ActiveIndex,
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
	pub type Summary<T> = StorageValue<_, SummaryRecord, ValueQuery>;

	/// The currently active bonds, indexed according to the order of creation.
	#[pallet::storage]
	pub type Receipts<T> =
		StorageMap<_, Blake2_128Concat, ActiveIndex, ReceiptRecordOf<T>, OptionQuery>;

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
			/// The identity of the receipt.
			index: ActiveIndex,
			/// The block number at which the receipt may be thawed.
			expiry: T::BlockNumber,
			/// The owner of the receipt.
			who: T::AccountId,
			/// The proportion of the effective total issuance which the receipt represents.
			proportion: Perquintill,
			/// The amount of funds which were debited from the owner.
			amount: BalanceOf<T>,
		},
		/// An expired bond has been thawed.
		Thawed {
			/// The identity of the receipt.
			index: ActiveIndex,
			/// The owner.
			who: T::AccountId,
			/// The proportion of the effective total issuance by which the owner was debited.
			proportion: Perquintill,
			/// The amount by which the owner was credited.
			amount: BalanceOf<T>,
			/// If `true` then the receipt is done.
			dropped: bool,
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
		/// The portion supplied is beyond the value of the bond.
		TooMuch,
		/// Not enough funds are held to pay out.
		Unfunded,
		/// There are enough funds for what is required.
		Funded,
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
					T::Currency::reserve(&who, amount)?;

					// queue is <Ordered: Lowest ... Highest><Fifo: Last ... First>
					let mut bid = Bid { amount, who: who.clone() };
					let net = if queue_full {
						sp_std::mem::swap(&mut q[0], &mut bid);
						let _ = T::Currency::unreserve(&bid.who, bid.amount);
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

			let _ = T::Currency::unreserve(&bid.who, bid.amount);
			Self::deposit_event(Event::BidRetracted { who: bid.who, amount: bid.amount, duration });

			Ok(().into())
		}

		/// Ensure we have sufficient funding for all potential payouts.
		///
		/// - `origin`: Must be accepted by `FundOrigin`.
		#[pallet::weight(T::WeightInfo::fund_deficit())]
		pub fn fund_deficit(origin: OriginFor<T>) -> DispatchResult {
			T::FundOrigin::ensure_origin(origin)?;
			let summary: SummaryRecord = Summary::<T>::get();
			let our_account = Self::account_id();
			let issuance = Self::issuance_with(&our_account, &summary);
			let deficit = issuance.required.saturating_sub(issuance.holdings);
			ensure!(!deficit.is_zero(), Error::<T>::Funded);
			T::Deficit::on_unbalanced(T::Currency::deposit_creating(&our_account, deficit));
			Ok(())
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
			portion: Option<<T::Counterpart as FungibleInspect<T::AccountId>>::Balance>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			// Look for `index`
			let mut receipt: ReceiptRecordOf<T> =
				Receipts::<T>::get(index).ok_or(Error::<T>::Unknown)?;
			// If found, check the owner is `who`.
			ensure!(receipt.who == who, Error::<T>::NotOwner);
			let now = frame_system::Pallet::<T>::block_number();
			ensure!(now >= receipt.expiry, Error::<T>::NotExpired);

			let proportion = if let Some(counterpart) = portion {
				let proportion = T::CounterpartAmount::convert_back(counterpart);
				ensure!(proportion <= receipt.proportion, Error::<T>::TooMuch);
				// TODO: check if `proportion` is below a minimum bond size and if so then fail.
				proportion
			} else {
				let fung_eq = T::CounterpartAmount::convert(receipt.proportion);
				T::Counterpart::burn_from(&who, fung_eq)?;
				receipt.proportion
			};

			// Multiply the proportion it is by the total issued.
			let mut summary: SummaryRecord = Summary::<T>::get();
			let our_account = Self::account_id();
			let effective_issuance = Self::issuance_with(&our_account, &summary).effective;
			let amount = proportion * effective_issuance;

			receipt.proportion.saturating_reduce(proportion);
			summary.proportion_owed.saturating_reduce(proportion);

			T::Currency::transfer(&our_account, &who, amount, AllowDeath)
				.map_err(|_| Error::<T>::Unfunded)?;

			let dropped = receipt.proportion.is_zero();
			if dropped {
				Receipts::<T>::remove(index);
			} else {
				Receipts::<T>::insert(index, &receipt);
			}
			Summary::<T>::put(&summary);

			Self::deposit_event(Event::Thawed { index, who, amount, proportion, dropped });

			Ok(())
		}
	}

	/// Issuance information returned by `issuance()`.
	pub struct IssuanceInfo<Balance> {
		/// The balance held in reserve over all active bonds.
		pub holdings: Balance,
		/// The issuance not held in reserve for active bonds. Together with `reserved` this sums
		/// to `Currency::total_issuance`.
		pub other: Balance,
		/// The balance that `reserved` is effectively worth, at present. This is not issued funds
		/// and could be less than `reserved` (though in most cases should be greater).
		pub effective: Balance,
		/// The balance that `reserved` is effectively worth, at present. This is not issued funds
		/// and could be less than `reserved` (though in most cases should be greater).
		pub required: Balance,
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
		/// The account ID of the reserves.
		///
		/// This actually does computation. If you need to keep using it, then make sure you cache
		/// the value and only call this once.
		pub fn account_id() -> T::AccountId {
			T::PalletId::get().into_account_truncating()
		}

		/// Returns information on the issuance of bonds.
		///
		/// Also provides the summary and this pallet's account ID.
		pub fn issuance() -> IssuanceInfo<BalanceOf<T>> {
			Self::issuance_with(&Self::account_id(), &Summary::<T>::get())
		}

		/// Returns information on the issuance of bonds.
		///
		/// Also provides the summary and this pallet's account ID.
		pub fn issuance_with(
			our_account: &T::AccountId,
			summary: &SummaryRecord,
		) -> IssuanceInfo<BalanceOf<T>> {
			let total_issuance =
				T::Currency::total_issuance().saturating_sub(T::IgnoredIssuance::get());
			let holdings = T::Currency::free_balance(our_account);
			let other = total_issuance.saturating_sub(holdings);
			let effective =
				summary.proportion_owed.left_from_one().saturating_reciprocal_mul(other);
			let required = summary.proportion_owed * effective;
			IssuanceInfo { holdings, other, effective, required }
		}

		/// Attempt to enlarge our bond-set from bids in order to satisfy our desired target amount
		/// of funds frozen into bonds.
		pub fn pursue_target(max_bids: u32) -> Weight {
			let summary: SummaryRecord = Summary::<T>::get();
			let target = T::Target::get();
			if summary.proportion_owed < target {
				let missing = target.saturating_sub(summary.proportion_owed);
				let issuance = Self::issuance_with(&Self::account_id(), &summary);

				let intake = missing * issuance.effective;

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
			let mut remaining = amount;
			let mut bids_taken = 0;
			let mut queues_hit = 0;
			let now = frame_system::Pallet::<T>::block_number();

			let mut summary = Summary::<T>::get();
			let mut queue_totals = QueueTotals::<T>::get();
			let our_account = Self::account_id();
			let issuance = Self::issuance_with(&our_account, &summary);

			for duration in (1..=T::QueueCount::get()).rev() {
				if queue_totals[duration as usize - 1].0 == 0 {
					continue
				}
				let queue_index = duration as usize - 1;
				let expiry = now.saturating_add(T::Period::get().saturating_mul(duration.into()));
				let mut queue = Queues::<T>::get(&duration);
				while let Some(mut bid) = queue.pop() {
					if remaining < bid.amount {
						let overflow = bid.amount - remaining;
						bid.amount = remaining;
						queue
							.try_push(Bid { amount: overflow, who: bid.who.clone() })
							.expect("just popped, so there must be space. qed");
					}
					let amount =
						bid.amount.saturating_sub(T::Currency::unreserve(&bid.who, bid.amount));
					if T::Currency::transfer(&bid.who, &our_account, amount, AllowDeath).is_err() {
						continue
					}

					// Can never overflow due to block above.
					remaining.saturating_reduce(amount);
					// Should never underflow since it should track the total of the
					// bids exactly, but we'll be defensive.
					queue_totals[queue_index].1 =
						queue_totals[queue_index].1.defensive_saturating_sub(amount);

					// Now to activate the bid...
					let n = amount;
					let d = issuance.effective;
					let proportion = Perquintill::from_rational(n, d);
					let who = bid.who;
					let index = summary.index;
					summary.proportion_owed.defensive_saturating_accrue(proportion);
					summary.index += 1;

					let e = Event::Issued {
						index,
						expiry,
						who: who.clone(),
						amount,
						proportion: proportion.clone(),
					};
					Self::deposit_event(e);
					let receipt = ReceiptRecord { proportion, who: who.clone(), expiry };
					Receipts::<T>::insert(index, receipt);

					// issue the fungible counterpart
					let fung_eq = T::CounterpartAmount::convert(proportion);
					let _ = T::Counterpart::mint_into(&who, fung_eq).defensive();

					bids_taken += 1;

					if remaining.is_zero() || bids_taken == max_bids {
						break
					}
				}
				queues_hit += 1;
				queue_totals[queue_index].0 = queue.len() as u32;
				Queues::<T>::insert(&duration, &queue);
				if remaining.is_zero() || bids_taken == max_bids {
					break
				}
			}
			QueueTotals::<T>::put(&queue_totals);
			Summary::<T>::put(&summary);
			(bids_taken, queues_hit)
		}
	}
}
