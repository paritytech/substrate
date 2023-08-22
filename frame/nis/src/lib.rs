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
//! `QueueCount`. The balance gets reserved. There's a minimum of `MinBid` to avoid dust.
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
//! - *Effective total issuance*: The total issuance of balances in the system, equal to the active
//!   issuance plus the value of all outstanding receipts, less `IgnoredIssuance`.

#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::traits::{
	fungible::{self, Inspect as FunInspect, Mutate as FunMutate},
	tokens::{DepositConsequence, Fortitude, Preservation, Provenance, WithdrawConsequence},
};
pub use pallet::*;
use sp_arithmetic::{traits::Unsigned, RationalArg};
use sp_core::TypedGet;
use sp_runtime::{
	traits::{Convert, ConvertBack},
	DispatchError, Perquintill,
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

pub struct NoCounterpart<T>(sp_std::marker::PhantomData<T>);
impl<T> FunInspect<T> for NoCounterpart<T> {
	type Balance = u32;
	fn total_issuance() -> u32 {
		0
	}
	fn minimum_balance() -> u32 {
		0
	}
	fn balance(_: &T) -> u32 {
		0
	}
	fn total_balance(_: &T) -> u32 {
		0
	}
	fn reducible_balance(_: &T, _: Preservation, _: Fortitude) -> u32 {
		0
	}
	fn can_deposit(_: &T, _: u32, _: Provenance) -> DepositConsequence {
		DepositConsequence::Success
	}
	fn can_withdraw(_: &T, _: u32) -> WithdrawConsequence<u32> {
		WithdrawConsequence::Success
	}
}
impl<T> fungible::Unbalanced<T> for NoCounterpart<T> {
	fn handle_dust(_: fungible::Dust<T, Self>) {}
	fn write_balance(_: &T, _: Self::Balance) -> Result<Option<Self::Balance>, DispatchError> {
		Ok(None)
	}
	fn set_total_issuance(_: Self::Balance) {}
}
impl<T> FunMutate<T> for NoCounterpart<T> {}
impl<T> Convert<Perquintill, u32> for NoCounterpart<T> {
	fn convert(_: Perquintill) -> u32 {
		0
	}
}

#[frame_support::pallet]
pub mod pallet {
	use super::{FunInspect, FunMutate};
	pub use crate::weights::WeightInfo;
	use frame_support::{
		pallet_prelude::*,
		traits::{
			fungible::{self, hold::Mutate as FunHoldMutate, Balanced as FunBalanced},
			nonfungible::{Inspect as NftInspect, Transfer as NftTransfer},
			tokens::{
				Balance,
				Fortitude::Polite,
				Precision::{BestEffort, Exact},
				Preservation::Expendable,
				Restriction::{Free, OnHold},
			},
			Defensive, DefensiveSaturating, OnUnbalanced,
		},
		PalletId,
	};
	use frame_system::pallet_prelude::*;
	use sp_arithmetic::{PerThing, Perquintill};
	use sp_runtime::{
		traits::{AccountIdConversion, Bounded, Convert, ConvertBack, Saturating, Zero},
		Rounding, TokenError,
	};
	use sp_std::prelude::*;

	type BalanceOf<T> =
		<<T as Config>::Currency as FunInspect<<T as frame_system::Config>::AccountId>>::Balance;
	type DebtOf<T> =
		fungible::Debt<<T as frame_system::Config>::AccountId, <T as Config>::Currency>;
	type ReceiptRecordOf<T> =
		ReceiptRecord<<T as frame_system::Config>::AccountId, BlockNumberFor<T>, BalanceOf<T>>;
	type IssuanceInfoOf<T> = IssuanceInfo<BalanceOf<T>>;
	type SummaryRecordOf<T> = SummaryRecord<BlockNumberFor<T>, BalanceOf<T>>;
	type BidOf<T> = Bid<BalanceOf<T>, <T as frame_system::Config>::AccountId>;
	type QueueTotalsTypeOf<T> = BoundedVec<(u32, BalanceOf<T>), <T as Config>::QueueCount>;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// Information on runtime weights.
		type WeightInfo: WeightInfo;

		/// Overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// The treasury's pallet id, used for deriving its sovereign account ID.
		#[pallet::constant]
		type PalletId: Get<PalletId>;

		/// Currency type that this works on.
		type Currency: FunInspect<Self::AccountId, Balance = Self::CurrencyBalance>
			+ FunMutate<Self::AccountId>
			+ FunBalanced<Self::AccountId>
			+ FunHoldMutate<Self::AccountId, Reason = Self::RuntimeHoldReason>;

		/// Overarching hold reason.
		type RuntimeHoldReason: From<HoldReason>;

		/// Just the [`Balance`] type; we have this item to allow us to constrain it to
		/// [`From<u64>`].
		type CurrencyBalance: Balance + From<u64>;

		/// Origin required for auto-funding the deficit.
		type FundOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// The issuance to ignore. This is subtracted from the `Currency`'s `total_issuance` to get
		/// the issuance with which we determine the thawed value of a given proportion.
		type IgnoredIssuance: Get<BalanceOf<Self>>;

		/// The accounting system for the fungible counterpart tokens.
		type Counterpart: FunMutate<Self::AccountId>;

		/// The system to convert an overall proportion of issuance into a number of fungible
		/// counterpart tokens.
		///
		/// In general it's best to use `WithMaximumOf`.
		type CounterpartAmount: ConvertBack<
			Perquintill,
			<Self::Counterpart as FunInspect<Self::AccountId>>::Balance,
		>;

		/// Unbalanced handler to account for funds created (in case of a higher total issuance over
		/// freezing period).
		type Deficit: OnUnbalanced<DebtOf<Self>>;

		/// The target sum of all receipts' proportions.
		type Target: Get<Perquintill>;

		/// Number of duration queues in total. This sets the maximum duration supported, which is
		/// this value multiplied by `Period`.
		#[pallet::constant]
		type QueueCount: Get<u32>;

		/// Maximum number of items that may be in each duration queue.
		///
		/// Must be larger than zero.
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
		type BasePeriod: Get<BlockNumberFor<Self>>;

		/// The minimum amount of funds that may be placed in a bid. Note that this
		/// does not actually limit the amount which may be represented in a receipt since bids may
		/// be split up by the system.
		///
		/// It should be at least big enough to ensure that there is no possible storage spam attack
		/// or queue-filling attack.
		#[pallet::constant]
		type MinBid: Get<BalanceOf<Self>>;

		/// The minimum amount of funds which may intentionally be left remaining under a single
		/// receipt.
		#[pallet::constant]
		type MinReceipt: Get<Perquintill>;

		/// The number of blocks between consecutive attempts to dequeue bids and create receipts.
		///
		/// A larger value results in fewer storage hits each block, but a slower period to get to
		/// the target.
		#[pallet::constant]
		type IntakePeriod: Get<BlockNumberFor<Self>>;

		/// The maximum amount of bids that can consolidated into receipts in a single intake. A
		/// larger value here means less of the block available for transactions should there be a
		/// glut of bids.
		#[pallet::constant]
		type MaxIntakeWeight: Get<Weight>;

		/// The maximum proportion which may be thawed and the period over which it is reset.
		#[pallet::constant]
		type ThawThrottle: Get<(Perquintill, BlockNumberFor<Self>)>;
	}

	#[pallet::pallet]
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
	pub struct ReceiptRecord<AccountId, BlockNumber, Balance> {
		/// The proportion of the effective total issuance.
		pub proportion: Perquintill,
		/// The account to whom this receipt belongs and the amount of funds on hold in their
		/// account for servicing this receipt. If `None`, then it is a communal receipt and
		/// fungible counterparts have been issued.
		pub owner: Option<(AccountId, Balance)>,
		/// The time after which this receipt can be thawed.
		pub expiry: BlockNumber,
	}

	/// An index for a receipt.
	pub type ReceiptIndex = u32;

	/// Overall information package on the outstanding receipts.
	///
	/// The way of determining the net issuance (i.e. after factoring in all maturing frozen funds)
	/// is:
	///
	/// `issuance - frozen + proportion * issuance`
	///
	/// where `issuance = active_issuance - IgnoredIssuance`
	#[derive(
		Clone, Eq, PartialEq, Default, Encode, Decode, RuntimeDebug, TypeInfo, MaxEncodedLen,
	)]
	pub struct SummaryRecord<BlockNumber, Balance> {
		/// The total proportion over all outstanding receipts.
		pub proportion_owed: Perquintill,
		/// The total number of receipts created so far.
		pub index: ReceiptIndex,
		/// The amount (as a proportion of ETI) which has been thawed in this period so far.
		pub thawed: Perquintill,
		/// The current thaw period's beginning.
		pub last_period: BlockNumber,
		/// The total amount of funds on hold for receipts. This doesn't include the pot or funds
		/// on hold for bids.
		pub receipts_on_hold: Balance,
	}

	pub struct OnEmptyQueueTotals<T>(sp_std::marker::PhantomData<T>);
	impl<T: Config> Get<QueueTotalsTypeOf<T>> for OnEmptyQueueTotals<T> {
		fn get() -> QueueTotalsTypeOf<T> {
			BoundedVec::truncate_from(vec![
				(0, Zero::zero());
				<T as Config>::QueueCount::get() as usize
			])
		}
	}

	/// The totals of items and balances within each queue. Saves a lot of storage reads in the
	/// case of sparsely packed queues.
	///
	/// The vector is indexed by duration in `Period`s, offset by one, so information on the queue
	/// whose duration is one `Period` would be storage `0`.
	#[pallet::storage]
	pub type QueueTotals<T: Config> =
		StorageValue<_, QueueTotalsTypeOf<T>, ValueQuery, OnEmptyQueueTotals<T>>;

	/// The queues of bids. Indexed by duration (in `Period`s).
	#[pallet::storage]
	pub type Queues<T: Config> =
		StorageMap<_, Blake2_128Concat, u32, BoundedVec<BidOf<T>, T::MaxQueueLen>, ValueQuery>;

	/// Summary information over the general state.
	#[pallet::storage]
	pub type Summary<T> = StorageValue<_, SummaryRecordOf<T>, ValueQuery>;

	/// The currently outstanding receipts, indexed according to the order of creation.
	#[pallet::storage]
	pub type Receipts<T> =
		StorageMap<_, Blake2_128Concat, ReceiptIndex, ReceiptRecordOf<T>, OptionQuery>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A bid was successfully placed.
		BidPlaced { who: T::AccountId, amount: BalanceOf<T>, duration: u32 },
		/// A bid was successfully removed (before being accepted).
		BidRetracted { who: T::AccountId, amount: BalanceOf<T>, duration: u32 },
		/// A bid was dropped from a queue because of another, more substantial, bid was present.
		BidDropped { who: T::AccountId, amount: BalanceOf<T>, duration: u32 },
		/// A bid was accepted. The balance may not be released until expiry.
		Issued {
			/// The identity of the receipt.
			index: ReceiptIndex,
			/// The block number at which the receipt may be thawed.
			expiry: BlockNumberFor<T>,
			/// The owner of the receipt.
			who: T::AccountId,
			/// The proportion of the effective total issuance which the receipt represents.
			proportion: Perquintill,
			/// The amount of funds which were debited from the owner.
			amount: BalanceOf<T>,
		},
		/// An receipt has been (at least partially) thawed.
		Thawed {
			/// The identity of the receipt.
			index: ReceiptIndex,
			/// The owner.
			who: T::AccountId,
			/// The proportion of the effective total issuance by which the owner was debited.
			proportion: Perquintill,
			/// The amount by which the owner was credited.
			amount: BalanceOf<T>,
			/// If `true` then the receipt is done.
			dropped: bool,
		},
		/// An automatic funding of the deficit was made.
		Funded { deficit: BalanceOf<T> },
		/// A receipt was transfered.
		Transferred { from: T::AccountId, to: T::AccountId, index: ReceiptIndex },
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
		/// Receipt index is unknown.
		UnknownReceipt,
		/// Not the owner of the receipt.
		NotOwner,
		/// Bond not yet at expiry date.
		NotExpired,
		/// The given bid for retraction is not found.
		UnknownBid,
		/// The portion supplied is beyond the value of the receipt.
		PortionTooBig,
		/// Not enough funds are held to pay out.
		Unfunded,
		/// There are enough funds for what is required.
		AlreadyFunded,
		/// The thaw throttle has been reached for this period.
		Throttled,
		/// The operation would result in a receipt worth an insignficant value.
		MakesDust,
		/// The receipt is already communal.
		AlreadyCommunal,
		/// The receipt is already private.
		AlreadyPrivate,
	}

	/// A reason for the NIS pallet placing a hold on funds.
	#[pallet::composite_enum]
	pub enum HoldReason {
		/// The NIS Pallet has reserved it for a non-fungible receipt.
		#[codec(index = 0)]
		NftReceipt,
	}

	pub(crate) struct WeightCounter {
		pub(crate) used: Weight,
		pub(crate) limit: Weight,
	}
	impl WeightCounter {
		#[allow(dead_code)]
		pub(crate) fn unlimited() -> Self {
			WeightCounter { used: Weight::zero(), limit: Weight::max_value() }
		}
		fn check_accrue(&mut self, w: Weight) -> bool {
			let test = self.used.saturating_add(w);
			if test.any_gt(self.limit) {
				false
			} else {
				self.used = test;
				true
			}
		}
		fn can_accrue(&mut self, w: Weight) -> bool {
			self.used.saturating_add(w).all_lte(self.limit)
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(n: BlockNumberFor<T>) -> Weight {
			let mut weight_counter =
				WeightCounter { used: Weight::zero(), limit: T::MaxIntakeWeight::get() };
			if T::IntakePeriod::get().is_zero() || (n % T::IntakePeriod::get()).is_zero() {
				if weight_counter.check_accrue(T::WeightInfo::process_queues()) {
					Self::process_queues(
						T::Target::get(),
						T::QueueCount::get(),
						u32::max_value(),
						&mut weight_counter,
					)
				}
			}
			weight_counter.used
		}

		fn integrity_test() {
			assert!(!T::IntakePeriod::get().is_zero());
			assert!(!T::MaxQueueLen::get().is_zero());
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Place a bid.
		///
		/// Origin must be Signed, and account must have at least `amount` in free balance.
		///
		/// - `amount`: The amount of the bid; these funds will be reserved, and if/when
		///   consolidated, removed. Must be at least `MinBid`.
		/// - `duration`: The number of periods before which the newly consolidated bid may be
		///   thawed. Must be greater than 1 and no more than `QueueCount`.
		///
		/// Complexities:
		/// - `Queues[duration].len()` (just take max).
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::place_bid_max())]
		pub fn place_bid(
			origin: OriginFor<T>,
			#[pallet::compact] amount: BalanceOf<T>,
			duration: u32,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			ensure!(amount >= T::MinBid::get(), Error::<T>::AmountTooSmall);
			let queue_count = T::QueueCount::get() as usize;
			let queue_index = duration.checked_sub(1).ok_or(Error::<T>::DurationTooSmall)? as usize;
			ensure!(queue_index < queue_count, Error::<T>::DurationTooBig);

			let net = Queues::<T>::try_mutate(
				duration,
				|q| -> Result<(u32, BalanceOf<T>), DispatchError> {
					let queue_full = q.len() == T::MaxQueueLen::get() as usize;
					ensure!(!queue_full || q[0].amount < amount, Error::<T>::BidTooLow);
					T::Currency::hold(&HoldReason::NftReceipt.into(), &who, amount)?;

					// queue is <Ordered: Lowest ... Highest><Fifo: Last ... First>
					let mut bid = Bid { amount, who: who.clone() };
					let net = if queue_full {
						sp_std::mem::swap(&mut q[0], &mut bid);
						let _ = T::Currency::release(
							&HoldReason::NftReceipt.into(),
							&bid.who,
							bid.amount,
							BestEffort,
						);
						Self::deposit_event(Event::<T>::BidDropped {
							who: bid.who,
							amount: bid.amount,
							duration,
						});
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
				qs[queue_index].1.saturating_accrue(net.1);
			});
			Self::deposit_event(Event::BidPlaced { who, amount, duration });

			Ok(())
		}

		/// Retract a previously placed bid.
		///
		/// Origin must be Signed, and the account should have previously issued a still-active bid
		/// of `amount` for `duration`.
		///
		/// - `amount`: The amount of the previous bid.
		/// - `duration`: The duration of the previous bid.
		#[pallet::call_index(1)]
		#[pallet::weight(T::WeightInfo::retract_bid(T::MaxQueueLen::get()))]
		pub fn retract_bid(
			origin: OriginFor<T>,
			#[pallet::compact] amount: BalanceOf<T>,
			duration: u32,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			let queue_count = T::QueueCount::get() as usize;
			let queue_index = duration.checked_sub(1).ok_or(Error::<T>::DurationTooSmall)? as usize;
			ensure!(queue_index < queue_count, Error::<T>::DurationTooBig);

			let bid = Bid { amount, who };

			let mut queue = Queues::<T>::get(duration);
			let pos = queue.iter().position(|i| i == &bid).ok_or(Error::<T>::UnknownBid)?;
			queue.remove(pos);
			let new_len = queue.len() as u32;

			T::Currency::release(&HoldReason::NftReceipt.into(), &bid.who, bid.amount, BestEffort)?;

			Queues::<T>::insert(duration, queue);
			QueueTotals::<T>::mutate(|qs| {
				qs.bounded_resize(queue_count, (0, Zero::zero()));
				qs[queue_index].0 = new_len;
				qs[queue_index].1.saturating_reduce(bid.amount);
			});

			Self::deposit_event(Event::BidRetracted { who: bid.who, amount: bid.amount, duration });

			Ok(())
		}

		/// Ensure we have sufficient funding for all potential payouts.
		///
		/// - `origin`: Must be accepted by `FundOrigin`.
		#[pallet::call_index(2)]
		#[pallet::weight(T::WeightInfo::fund_deficit())]
		pub fn fund_deficit(origin: OriginFor<T>) -> DispatchResult {
			T::FundOrigin::ensure_origin(origin)?;
			let summary: SummaryRecordOf<T> = Summary::<T>::get();
			let our_account = Self::account_id();
			let issuance = Self::issuance_with(&our_account, &summary);
			let deficit = issuance.required.saturating_sub(issuance.holdings);
			ensure!(!deficit.is_zero(), Error::<T>::AlreadyFunded);
			T::Deficit::on_unbalanced(T::Currency::deposit(&our_account, deficit, Exact)?);
			Self::deposit_event(Event::<T>::Funded { deficit });
			Ok(())
		}

		/// Reduce or remove an outstanding receipt, placing the according proportion of funds into
		/// the account of the owner.
		///
		/// - `origin`: Must be Signed and the account must be the owner of the receipt `index` as
		///   well as any fungible counterpart.
		/// - `index`: The index of the receipt.
		/// - `portion`: If `Some`, then only the given portion of the receipt should be thawed. If
		///   `None`, then all of it should be.
		#[pallet::call_index(3)]
		#[pallet::weight(T::WeightInfo::thaw_private())]
		pub fn thaw_private(
			origin: OriginFor<T>,
			#[pallet::compact] index: ReceiptIndex,
			maybe_proportion: Option<Perquintill>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			// Look for `index`
			let mut receipt: ReceiptRecordOf<T> =
				Receipts::<T>::get(index).ok_or(Error::<T>::UnknownReceipt)?;
			// If found, check the owner is `who`.
			let (owner, mut on_hold) = receipt.owner.ok_or(Error::<T>::AlreadyCommunal)?;
			ensure!(owner == who, Error::<T>::NotOwner);

			let now = frame_system::Pallet::<T>::block_number();
			ensure!(now >= receipt.expiry, Error::<T>::NotExpired);

			let mut summary: SummaryRecordOf<T> = Summary::<T>::get();

			let proportion = if let Some(proportion) = maybe_proportion {
				ensure!(proportion <= receipt.proportion, Error::<T>::PortionTooBig);
				let remaining = receipt.proportion.saturating_sub(proportion);
				ensure!(
					remaining.is_zero() || remaining >= T::MinReceipt::get(),
					Error::<T>::MakesDust
				);
				proportion
			} else {
				receipt.proportion
			};

			let (throttle, throttle_period) = T::ThawThrottle::get();
			if now.saturating_sub(summary.last_period) >= throttle_period {
				summary.thawed = Zero::zero();
				summary.last_period = now;
			}
			summary.thawed.saturating_accrue(proportion);
			ensure!(summary.thawed <= throttle, Error::<T>::Throttled);

			// Multiply the proportion it is by the total issued.
			let our_account = Self::account_id();
			let effective_issuance = Self::issuance_with(&our_account, &summary).effective;
			//			let amount = proportion.mul_ceil(effective_issuance);
			let amount = proportion * effective_issuance;

			receipt.proportion.saturating_reduce(proportion);
			summary.proportion_owed.saturating_reduce(proportion);

			let dropped = receipt.proportion.is_zero();

			if amount > on_hold {
				T::Currency::release(&HoldReason::NftReceipt.into(), &who, on_hold, Exact)?;
				let deficit = amount - on_hold;
				// Try to transfer deficit from pot to receipt owner.
				summary.receipts_on_hold.saturating_reduce(on_hold);
				on_hold = Zero::zero();
				T::Currency::transfer(&our_account, &who, deficit, Expendable)
					.map_err(|_| Error::<T>::Unfunded)?;
			} else {
				on_hold.saturating_reduce(amount);
				summary.receipts_on_hold.saturating_reduce(amount);
				if dropped && !on_hold.is_zero() {
					// Reclaim any remainder:
					// Transfer excess of `on_hold` to the pot if we have now fully compensated for
					// the receipt.
					T::Currency::transfer_on_hold(
						&HoldReason::NftReceipt.into(),
						&who,
						&our_account,
						on_hold,
						Exact,
						Free,
						Polite,
					)
					.map(|_| ())
					// We ignore this error as it just means the amount we're trying to deposit is
					// dust and the beneficiary account doesn't exist.
					.or_else(
						|e| if e == TokenError::CannotCreate.into() { Ok(()) } else { Err(e) },
					)?;
					summary.receipts_on_hold.saturating_reduce(on_hold);
				}
				T::Currency::release(&HoldReason::NftReceipt.into(), &who, amount, Exact)?;
			}

			if dropped {
				Receipts::<T>::remove(index);
			} else {
				receipt.owner = Some((owner, on_hold));
				Receipts::<T>::insert(index, &receipt);
			}
			Summary::<T>::put(&summary);

			Self::deposit_event(Event::Thawed { index, who, amount, proportion, dropped });

			Ok(())
		}

		/// Reduce or remove an outstanding receipt, placing the according proportion of funds into
		/// the account of the owner.
		///
		/// - `origin`: Must be Signed and the account must be the owner of the fungible counterpart
		///   for receipt `index`.
		/// - `index`: The index of the receipt.
		#[pallet::call_index(4)]
		#[pallet::weight(T::WeightInfo::thaw_communal())]
		pub fn thaw_communal(
			origin: OriginFor<T>,
			#[pallet::compact] index: ReceiptIndex,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			// Look for `index`
			let receipt: ReceiptRecordOf<T> =
				Receipts::<T>::get(index).ok_or(Error::<T>::UnknownReceipt)?;
			// If found, check it is actually communal.
			ensure!(receipt.owner.is_none(), Error::<T>::NotOwner);
			let now = frame_system::Pallet::<T>::block_number();
			ensure!(now >= receipt.expiry, Error::<T>::NotExpired);

			let mut summary: SummaryRecordOf<T> = Summary::<T>::get();

			let (throttle, throttle_period) = T::ThawThrottle::get();
			if now.saturating_sub(summary.last_period) >= throttle_period {
				summary.thawed = Zero::zero();
				summary.last_period = now;
			}
			summary.thawed.saturating_accrue(receipt.proportion);
			ensure!(summary.thawed <= throttle, Error::<T>::Throttled);

			let cp_amount = T::CounterpartAmount::convert(receipt.proportion);
			T::Counterpart::burn_from(&who, cp_amount, Exact, Polite)?;

			// Multiply the proportion it is by the total issued.
			let our_account = Self::account_id();
			let effective_issuance = Self::issuance_with(&our_account, &summary).effective;
			let amount = receipt.proportion * effective_issuance;

			summary.proportion_owed.saturating_reduce(receipt.proportion);

			// Try to transfer amount owed from pot to receipt owner.
			T::Currency::transfer(&our_account, &who, amount, Expendable)
				.map_err(|_| Error::<T>::Unfunded)?;

			Receipts::<T>::remove(index);
			Summary::<T>::put(&summary);

			let e =
				Event::Thawed { index, who, amount, proportion: receipt.proportion, dropped: true };
			Self::deposit_event(e);

			Ok(())
		}

		/// Make a private receipt communal and create fungible counterparts for its owner.
		#[pallet::call_index(5)]
		#[pallet::weight(T::WeightInfo::communify())]
		pub fn communify(
			origin: OriginFor<T>,
			#[pallet::compact] index: ReceiptIndex,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			// Look for `index`
			let mut receipt: ReceiptRecordOf<T> =
				Receipts::<T>::get(index).ok_or(Error::<T>::UnknownReceipt)?;

			// Check it's not already communal and make it so.
			let (owner, on_hold) = receipt.owner.take().ok_or(Error::<T>::AlreadyCommunal)?;

			// If found, check the owner is `who`.
			ensure!(owner == who, Error::<T>::NotOwner);

			// Unreserve and transfer the funds to the pot.
			let reason = HoldReason::NftReceipt.into();
			let us = Self::account_id();
			T::Currency::transfer_on_hold(&reason, &who, &us, on_hold, Exact, Free, Polite)
				.map_err(|_| Error::<T>::Unfunded)?;

			// Record that we've moved the amount reserved.
			let mut summary: SummaryRecordOf<T> = Summary::<T>::get();
			summary.receipts_on_hold.saturating_reduce(on_hold);
			Summary::<T>::put(&summary);
			Receipts::<T>::insert(index, &receipt);

			// Mint fungibles.
			let fung_eq = T::CounterpartAmount::convert(receipt.proportion);
			let _ = T::Counterpart::mint_into(&who, fung_eq).defensive();

			Ok(())
		}

		/// Make a communal receipt private and burn fungible counterparts from its owner.
		#[pallet::call_index(6)]
		#[pallet::weight(T::WeightInfo::privatize())]
		pub fn privatize(
			origin: OriginFor<T>,
			#[pallet::compact] index: ReceiptIndex,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			// Look for `index`
			let mut receipt: ReceiptRecordOf<T> =
				Receipts::<T>::get(index).ok_or(Error::<T>::UnknownReceipt)?;

			// If found, check there is no owner.
			ensure!(receipt.owner.is_none(), Error::<T>::AlreadyPrivate);

			// Multiply the proportion it is by the total issued.
			let mut summary: SummaryRecordOf<T> = Summary::<T>::get();
			let our_account = Self::account_id();
			let effective_issuance = Self::issuance_with(&our_account, &summary).effective;
			let max_amount = receipt.proportion * effective_issuance;
			// Avoid trying to place more in the account's reserve than we have available in the pot
			let amount = max_amount.min(T::Currency::balance(&our_account));

			// Burn fungible counterparts.
			T::Counterpart::burn_from(
				&who,
				T::CounterpartAmount::convert(receipt.proportion),
				Exact,
				Polite,
			)?;

			// Transfer the funds from the pot to the owner and reserve
			let reason = HoldReason::NftReceipt.into();
			let us = Self::account_id();
			T::Currency::transfer_and_hold(&reason, &us, &who, amount, Exact, Expendable, Polite)?;

			// Record that we've moved the amount reserved.
			summary.receipts_on_hold.saturating_accrue(amount);

			receipt.owner = Some((who, amount));

			Summary::<T>::put(&summary);
			Receipts::<T>::insert(index, &receipt);

			Ok(())
		}
	}

	/// Issuance information returned by `issuance()`.
	#[derive(Debug)]
	pub struct IssuanceInfo<Balance> {
		/// The balance held by this pallet instance together with the balances on hold across
		/// all receipt-owning accounts.
		pub holdings: Balance,
		/// The (non-ignored) issuance in the system, not including this pallet's account.
		pub other: Balance,
		/// The effective total issuance, hypothetically if all outstanding receipts were thawed at
		/// present.
		pub effective: Balance,
		/// The amount needed to be accessible to this pallet in case all outstanding receipts were
		/// thawed at present. If it is more than `holdings`, then the pallet will need funding.
		pub required: Balance,
	}

	impl<T: Config> NftInspect<T::AccountId> for Pallet<T> {
		type ItemId = ReceiptIndex;

		fn owner(item: &ReceiptIndex) -> Option<T::AccountId> {
			Receipts::<T>::get(item).and_then(|r| r.owner).map(|(who, _)| who)
		}

		fn attribute(item: &Self::ItemId, key: &[u8]) -> Option<Vec<u8>> {
			let item = Receipts::<T>::get(item)?;
			match key {
				b"proportion" => Some(item.proportion.encode()),
				b"expiry" => Some(item.expiry.encode()),
				b"owner" => item.owner.as_ref().map(|x| x.0.encode()),
				b"on_hold" => item.owner.as_ref().map(|x| x.1.encode()),
				_ => None,
			}
		}
	}

	impl<T: Config> NftTransfer<T::AccountId> for Pallet<T> {
		fn transfer(index: &ReceiptIndex, dest: &T::AccountId) -> DispatchResult {
			let mut item = Receipts::<T>::get(index).ok_or(TokenError::UnknownAsset)?;
			let (owner, on_hold) = item.owner.take().ok_or(Error::<T>::AlreadyCommunal)?;

			let reason = HoldReason::NftReceipt.into();
			T::Currency::transfer_on_hold(&reason, &owner, dest, on_hold, Exact, OnHold, Polite)?;

			item.owner = Some((dest.clone(), on_hold));
			Receipts::<T>::insert(&index, &item);
			Pallet::<T>::deposit_event(Event::<T>::Transferred {
				from: owner,
				to: dest.clone(),
				index: *index,
			});
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

		/// Returns information on the issuance within the system.
		pub fn issuance() -> IssuanceInfo<BalanceOf<T>> {
			Self::issuance_with(&Self::account_id(), &Summary::<T>::get())
		}

		/// Returns information on the issuance within the system
		///
		/// This function is equivalent to `issuance`, except that it accepts arguments rather than
		/// queries state. If the arguments are already known, then this may be slightly more
		/// performant.
		///
		/// - `our_account`: The value returned by `Self::account_id()`.
		/// - `summary`: The value returned by `Summary::<T>::get()`.
		pub fn issuance_with(
			our_account: &T::AccountId,
			summary: &SummaryRecordOf<T>,
		) -> IssuanceInfo<BalanceOf<T>> {
			let total_issuance =
				T::Currency::active_issuance().saturating_sub(T::IgnoredIssuance::get());
			let holdings =
				T::Currency::balance(our_account).saturating_add(summary.receipts_on_hold);
			let other = total_issuance.saturating_sub(holdings);
			let effective =
				summary.proportion_owed.left_from_one().saturating_reciprocal_mul(other);
			let required = summary.proportion_owed * effective;
			IssuanceInfo { holdings, other, effective, required }
		}

		/// Process some bids into receipts up to a `target` total of all receipts.
		///
		/// Touch at most `max_queues`.
		///
		/// Return the weight used.
		pub(crate) fn process_queues(
			target: Perquintill,
			max_queues: u32,
			max_bids: u32,
			weight: &mut WeightCounter,
		) {
			let mut summary: SummaryRecordOf<T> = Summary::<T>::get();
			if summary.proportion_owed >= target {
				return
			}

			let now = frame_system::Pallet::<T>::block_number();
			let our_account = Self::account_id();
			let issuance: IssuanceInfoOf<T> = Self::issuance_with(&our_account, &summary);
			let mut remaining = target.saturating_sub(summary.proportion_owed) * issuance.effective;

			let mut queues_hit = 0;
			let mut bids_hit = 0;
			let mut totals = QueueTotals::<T>::get();
			let queue_count = T::QueueCount::get();
			totals.bounded_resize(queue_count as usize, (0, Zero::zero()));
			for duration in (1..=queue_count).rev() {
				if totals[duration as usize - 1].0.is_zero() {
					continue
				}
				if remaining.is_zero() || queues_hit >= max_queues
					|| !weight.check_accrue(T::WeightInfo::process_queue())
					// No point trying to process a queue if we can't process a single bid.
					|| !weight.can_accrue(T::WeightInfo::process_bid())
				{
					break
				}

				let b = Self::process_queue(
					duration,
					now,
					&our_account,
					&issuance,
					max_bids.saturating_sub(bids_hit),
					&mut remaining,
					&mut totals[duration as usize - 1],
					&mut summary,
					weight,
				);

				bids_hit.saturating_accrue(b);
				queues_hit.saturating_inc();
			}
			QueueTotals::<T>::put(&totals);
			Summary::<T>::put(&summary);
		}

		pub(crate) fn process_queue(
			duration: u32,
			now: BlockNumberFor<T>,
			our_account: &T::AccountId,
			issuance: &IssuanceInfo<BalanceOf<T>>,
			max_bids: u32,
			remaining: &mut BalanceOf<T>,
			queue_total: &mut (u32, BalanceOf<T>),
			summary: &mut SummaryRecordOf<T>,
			weight: &mut WeightCounter,
		) -> u32 {
			let mut queue: BoundedVec<BidOf<T>, _> = Queues::<T>::get(&duration);
			let expiry = now.saturating_add(T::BasePeriod::get().saturating_mul(duration.into()));
			let mut count = 0;

			while count < max_bids &&
				!queue.is_empty() &&
				!remaining.is_zero() &&
				weight.check_accrue(T::WeightInfo::process_bid())
			{
				let bid = match queue.pop() {
					Some(b) => b,
					None => break,
				};
				if let Some(bid) = Self::process_bid(
					bid,
					expiry,
					our_account,
					issuance,
					remaining,
					&mut queue_total.1,
					summary,
				) {
					queue.try_push(bid).expect("just popped, so there must be space. qed");
					// This should exit at the next iteration (though nothing will break if it
					// doesn't).
				}
				count.saturating_inc();
			}
			queue_total.0 = queue.len() as u32;
			Queues::<T>::insert(&duration, &queue);
			count
		}

		pub(crate) fn process_bid(
			mut bid: BidOf<T>,
			expiry: BlockNumberFor<T>,
			_our_account: &T::AccountId,
			issuance: &IssuanceInfo<BalanceOf<T>>,
			remaining: &mut BalanceOf<T>,
			queue_amount: &mut BalanceOf<T>,
			summary: &mut SummaryRecordOf<T>,
		) -> Option<BidOf<T>> {
			let result = if *remaining < bid.amount {
				let overflow = bid.amount - *remaining;
				bid.amount = *remaining;
				Some(Bid { amount: overflow, who: bid.who.clone() })
			} else {
				None
			};
			let amount = bid.amount;
			summary.receipts_on_hold.saturating_accrue(amount);

			// Can never overflow due to block above.
			remaining.saturating_reduce(amount);
			// Should never underflow since it should track the total of the
			// bids exactly, but we'll be defensive.
			queue_amount.defensive_saturating_reduce(amount);

			// Now to activate the bid...
			let n = amount;
			let d = issuance.effective;
			let proportion = Perquintill::from_rational_with_rounding(n, d, Rounding::Down)
				.defensive_unwrap_or_default();
			let who = bid.who;
			let index = summary.index;
			summary.proportion_owed.defensive_saturating_accrue(proportion);
			summary.index += 1;

			let e = Event::Issued { index, expiry, who: who.clone(), amount, proportion };
			Self::deposit_event(e);
			let receipt = ReceiptRecord { proportion, owner: Some((who, amount)), expiry };
			Receipts::<T>::insert(index, receipt);

			result
		}
	}
}
