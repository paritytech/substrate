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

//! # Tipping Pallet ( pallet-tips )
//!
//! > NOTE: This pallet is tightly coupled with pallet-treasury.
//!
//! A subsystem to allow for an agile "tipping" process, whereby a reward may be given without first
//! having a pre-determined stakeholder group come to consensus on how much should be paid.
//!
//! A group of `Tippers` is determined through the config `Config`. After half of these have
//! declared some amount that they believe a particular reported reason deserves, then a countdown
//! period is entered where any remaining members can declare their tip amounts also. After the
//! close of the countdown period, the median of all declared tips is paid to the reported
//! beneficiary, along with any finders fee, in case of a public (and bonded) original report.
//!
//!
//! ### Terminology
//!
//! Tipping protocol:
//! - **Tipping:** The process of gathering declarations of amounts to tip and taking the median
//!   amount to be transferred from the treasury to a beneficiary account.
//! - **Tip Reason:** The reason for a tip; generally a URL which embodies or explains why a
//!   particular individual (identified by an account ID) is worthy of a recognition by the
//!   treasury.
//! - **Finder:** The original public reporter of some reason for tipping.
//! - **Finders Fee:** Some proportion of the tip amount that is paid to the reporter of the tip,
//!   rather than the main beneficiary.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! Tipping protocol:
//! - `report_awesome` - Report something worthy of a tip and register for a finders fee.
//! - `retract_tip` - Retract a previous (finders fee registered) report.
//! - `tip_new` - Report an item worthy of a tip and declare a specific amount to tip.
//! - `tip` - Declare or redeclare an amount to tip for a particular reason.
//! - `close_tip` - Close and pay out a tip.

#![cfg_attr(not(feature = "std"), no_std)]

mod benchmarking;
mod tests;

pub mod migrations;
pub mod weights;

use sp_runtime::{
	traits::{AccountIdConversion, BadOrigin, Hash, StaticLookup, TrailingZeroInput, Zero},
	Percent, RuntimeDebug,
};
use sp_std::prelude::*;

use codec::{Decode, Encode};
use frame_support::{
	traits::{
		ContainsLengthBound, Currency, EnsureOrigin, ExistenceRequirement::KeepAlive, Get,
		OnUnbalanced, ReservableCurrency, SortedMembers,
	},
	Parameter,
};

pub use pallet::*;
pub use weights::WeightInfo;

const LOG_TARGET: &str = "runtime::tips";

pub type BalanceOf<T, I = ()> = pallet_treasury::BalanceOf<T, I>;
pub type NegativeImbalanceOf<T, I = ()> = pallet_treasury::NegativeImbalanceOf<T, I>;
type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;

/// An open tipping "motion". Retains all details of a tip including information on the finder
/// and the members who have voted.
#[derive(Clone, Eq, PartialEq, Encode, Decode, RuntimeDebug, scale_info::TypeInfo)]
pub struct OpenTip<
	AccountId: Parameter,
	Balance: Parameter,
	BlockNumber: Parameter,
	Hash: Parameter,
> {
	/// The hash of the reason for the tip. The reason should be a human-readable UTF-8 encoded
	/// string. A URL would be sensible.
	reason: Hash,
	/// The account to be tipped.
	who: AccountId,
	/// The account who began this tip.
	finder: AccountId,
	/// The amount held on deposit for this tip.
	deposit: Balance,
	/// The block number at which this tip will close if `Some`. If `None`, then no closing is
	/// scheduled.
	closes: Option<BlockNumber>,
	/// The members who have voted for this tip. Sorted by AccountId.
	tips: Vec<(AccountId, Balance)>,
	/// Whether this tip should result in the finder taking a fee.
	finders_fee: bool,
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	/// The current storage version.
	const STORAGE_VERSION: StorageVersion = StorageVersion::new(4);

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	#[pallet::storage_version(STORAGE_VERSION)]
	#[pallet::without_storage_info]
	pub struct Pallet<T, I = ()>(_);

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config + pallet_treasury::Config<I> {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self, I>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Maximum acceptable reason length.
		///
		/// Benchmarks depend on this value, be sure to update weights file when changing this value
		#[pallet::constant]
		type MaximumReasonLength: Get<u32>;

		/// The amount held on deposit per byte within the tip report reason or bounty description.
		#[pallet::constant]
		type DataDepositPerByte: Get<BalanceOf<Self, I>>;

		/// The period for which a tip remains open after is has achieved threshold tippers.
		#[pallet::constant]
		type TipCountdown: Get<Self::BlockNumber>;

		/// The percent of the final tip which goes to the original reporter of the tip.
		#[pallet::constant]
		type TipFindersFee: Get<Percent>;

		/// The amount held on deposit for placing a tip report.
		#[pallet::constant]
		type TipReportDepositBase: Get<BalanceOf<Self, I>>;

		/// Origin from which tippers must come.
		///
		/// `ContainsLengthBound::max_len` must be cost free (i.e. no storage read or heavy
		/// operation). Benchmarks depend on the value of `ContainsLengthBound::max_len` be sure to
		/// update weights file when altering this method.
		type Tippers: SortedMembers<Self::AccountId> + ContainsLengthBound;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
	}

	/// TipsMap that are not yet completed. Keyed by the hash of `(reason, who)` from the value.
	/// This has the insecure enumerable hash function since the key itself is already
	/// guaranteed to be a secure hash.
	#[pallet::storage]
	#[pallet::getter(fn tips)]
	pub type Tips<T: Config<I>, I: 'static = ()> = StorageMap<
		_,
		Twox64Concat,
		T::Hash,
		OpenTip<T::AccountId, BalanceOf<T, I>, T::BlockNumber, T::Hash>,
		OptionQuery,
	>;

	/// Simple preimage lookup from the reason's hash to the original data. Again, has an
	/// insecure enumerable hash since the key is guaranteed to be the result of a secure hash.
	#[pallet::storage]
	#[pallet::getter(fn reasons)]
	pub type Reasons<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Identity, T::Hash, Vec<u8>, OptionQuery>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// A new tip suggestion has been opened.
		NewTip { tip_hash: T::Hash },
		/// A tip suggestion has reached threshold and is closing.
		TipClosing { tip_hash: T::Hash },
		/// A tip suggestion has been closed.
		TipClosed { tip_hash: T::Hash, who: T::AccountId, payout: BalanceOf<T, I> },
		/// A tip suggestion has been retracted.
		TipRetracted { tip_hash: T::Hash },
		/// A tip suggestion has been slashed.
		TipSlashed { tip_hash: T::Hash, finder: T::AccountId, deposit: BalanceOf<T, I> },
	}

	#[pallet::error]
	pub enum Error<T, I = ()> {
		/// The reason given is just too big.
		ReasonTooBig,
		/// The tip was already found/started.
		AlreadyKnown,
		/// The tip hash is unknown.
		UnknownTip,
		/// The account attempting to retract the tip is not the finder of the tip.
		NotFinder,
		/// The tip cannot be claimed/closed because there are not enough tippers yet.
		StillOpen,
		/// The tip cannot be claimed/closed because it's still in the countdown period.
		Premature,
	}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Report something `reason` that deserves a tip and claim any eventual the finder's fee.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// Payment: `TipReportDepositBase` will be reserved from the origin account, as well as
		/// `DataDepositPerByte` for each byte in `reason`.
		///
		/// - `reason`: The reason for, or the thing that deserves, the tip; generally this will be
		///   a UTF-8-encoded URL.
		/// - `who`: The account which should be credited for the tip.
		///
		/// Emits `NewTip` if successful.
		///
		/// # <weight>
		/// - Complexity: `O(R)` where `R` length of `reason`.
		///   - encoding and hashing of 'reason'
		/// - DbReads: `Reasons`, `Tips`
		/// - DbWrites: `Reasons`, `Tips`
		/// # </weight>
		#[pallet::call_index(0)]
		#[pallet::weight(<T as Config<I>>::WeightInfo::report_awesome(reason.len() as u32))]
		pub fn report_awesome(
			origin: OriginFor<T>,
			reason: Vec<u8>,
			who: AccountIdLookupOf<T>,
		) -> DispatchResult {
			let finder = ensure_signed(origin)?;
			let who = T::Lookup::lookup(who)?;

			ensure!(
				reason.len() <= T::MaximumReasonLength::get() as usize,
				Error::<T, I>::ReasonTooBig
			);

			let reason_hash = T::Hashing::hash(&reason[..]);
			ensure!(!Reasons::<T, I>::contains_key(&reason_hash), Error::<T, I>::AlreadyKnown);
			let hash = T::Hashing::hash_of(&(&reason_hash, &who));
			ensure!(!Tips::<T, I>::contains_key(&hash), Error::<T, I>::AlreadyKnown);

			let deposit = T::TipReportDepositBase::get() +
				T::DataDepositPerByte::get() * (reason.len() as u32).into();
			T::Currency::reserve(&finder, deposit)?;

			Reasons::<T, I>::insert(&reason_hash, &reason);
			let tip = OpenTip {
				reason: reason_hash,
				who,
				finder,
				deposit,
				closes: None,
				tips: vec![],
				finders_fee: true,
			};
			Tips::<T, I>::insert(&hash, tip);
			Self::deposit_event(Event::NewTip { tip_hash: hash });
			Ok(())
		}

		/// Retract a prior tip-report from `report_awesome`, and cancel the process of tipping.
		///
		/// If successful, the original deposit will be unreserved.
		///
		/// The dispatch origin for this call must be _Signed_ and the tip identified by `hash`
		/// must have been reported by the signing account through `report_awesome` (and not
		/// through `tip_new`).
		///
		/// - `hash`: The identity of the open tip for which a tip value is declared. This is formed
		///   as the hash of the tuple of the original tip `reason` and the beneficiary account ID.
		///
		/// Emits `TipRetracted` if successful.
		///
		/// # <weight>
		/// - Complexity: `O(1)`
		///   - Depends on the length of `T::Hash` which is fixed.
		/// - DbReads: `Tips`, `origin account`
		/// - DbWrites: `Reasons`, `Tips`, `origin account`
		/// # </weight>
		#[pallet::call_index(1)]
		#[pallet::weight(<T as Config<I>>::WeightInfo::retract_tip())]
		pub fn retract_tip(origin: OriginFor<T>, hash: T::Hash) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let tip = Tips::<T, I>::get(&hash).ok_or(Error::<T, I>::UnknownTip)?;
			ensure!(tip.finder == who, Error::<T, I>::NotFinder);

			Reasons::<T, I>::remove(&tip.reason);
			Tips::<T, I>::remove(&hash);
			if !tip.deposit.is_zero() {
				let err_amount = T::Currency::unreserve(&who, tip.deposit);
				debug_assert!(err_amount.is_zero());
			}
			Self::deposit_event(Event::TipRetracted { tip_hash: hash });
			Ok(())
		}

		/// Give a tip for something new; no finder's fee will be taken.
		///
		/// The dispatch origin for this call must be _Signed_ and the signing account must be a
		/// member of the `Tippers` set.
		///
		/// - `reason`: The reason for, or the thing that deserves, the tip; generally this will be
		///   a UTF-8-encoded URL.
		/// - `who`: The account which should be credited for the tip.
		/// - `tip_value`: The amount of tip that the sender would like to give. The median tip
		///   value of active tippers will be given to the `who`.
		///
		/// Emits `NewTip` if successful.
		///
		/// # <weight>
		/// - Complexity: `O(R + T)` where `R` length of `reason`, `T` is the number of tippers.
		///   - `O(T)`: decoding `Tipper` vec of length `T`. `T` is charged as upper bound given by
		///     `ContainsLengthBound`. The actual cost depends on the implementation of
		///     `T::Tippers`.
		///   - `O(R)`: hashing and encoding of reason of length `R`
		/// - DbReads: `Tippers`, `Reasons`
		/// - DbWrites: `Reasons`, `Tips`
		/// # </weight>
		#[pallet::call_index(2)]
		#[pallet::weight(<T as Config<I>>::WeightInfo::tip_new(reason.len() as u32, T::Tippers::max_len() as u32))]
		pub fn tip_new(
			origin: OriginFor<T>,
			reason: Vec<u8>,
			who: AccountIdLookupOf<T>,
			#[pallet::compact] tip_value: BalanceOf<T, I>,
		) -> DispatchResult {
			let tipper = ensure_signed(origin)?;
			let who = T::Lookup::lookup(who)?;
			ensure!(T::Tippers::contains(&tipper), BadOrigin);
			let reason_hash = T::Hashing::hash(&reason[..]);
			ensure!(!Reasons::<T, I>::contains_key(&reason_hash), Error::<T, I>::AlreadyKnown);
			let hash = T::Hashing::hash_of(&(&reason_hash, &who));

			Reasons::<T, I>::insert(&reason_hash, &reason);
			Self::deposit_event(Event::NewTip { tip_hash: hash });
			let tips = vec![(tipper.clone(), tip_value)];
			let tip = OpenTip {
				reason: reason_hash,
				who,
				finder: tipper,
				deposit: Zero::zero(),
				closes: None,
				tips,
				finders_fee: false,
			};
			Tips::<T, I>::insert(&hash, tip);
			Ok(())
		}

		/// Declare a tip value for an already-open tip.
		///
		/// The dispatch origin for this call must be _Signed_ and the signing account must be a
		/// member of the `Tippers` set.
		///
		/// - `hash`: The identity of the open tip for which a tip value is declared. This is formed
		///   as the hash of the tuple of the hash of the original tip `reason` and the beneficiary
		///   account ID.
		/// - `tip_value`: The amount of tip that the sender would like to give. The median tip
		///   value of active tippers will be given to the `who`.
		///
		/// Emits `TipClosing` if the threshold of tippers has been reached and the countdown period
		/// has started.
		///
		/// # <weight>
		/// - Complexity: `O(T)` where `T` is the number of tippers. decoding `Tipper` vec of length
		///   `T`, insert tip and check closing, `T` is charged as upper bound given by
		///   `ContainsLengthBound`. The actual cost depends on the implementation of `T::Tippers`.
		///
		///   Actually weight could be lower as it depends on how many tips are in `OpenTip` but it
		///   is weighted as if almost full i.e of length `T-1`.
		/// - DbReads: `Tippers`, `Tips`
		/// - DbWrites: `Tips`
		/// # </weight>
		#[pallet::call_index(3)]
		#[pallet::weight(<T as Config<I>>::WeightInfo::tip(T::Tippers::max_len() as u32))]
		pub fn tip(
			origin: OriginFor<T>,
			hash: T::Hash,
			#[pallet::compact] tip_value: BalanceOf<T, I>,
		) -> DispatchResult {
			let tipper = ensure_signed(origin)?;
			ensure!(T::Tippers::contains(&tipper), BadOrigin);

			let mut tip = Tips::<T, I>::get(hash).ok_or(Error::<T, I>::UnknownTip)?;
			if Self::insert_tip_and_check_closing(&mut tip, tipper, tip_value) {
				Self::deposit_event(Event::TipClosing { tip_hash: hash });
			}
			Tips::<T, I>::insert(&hash, tip);
			Ok(())
		}

		/// Close and payout a tip.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// The tip identified by `hash` must have finished its countdown period.
		///
		/// - `hash`: The identity of the open tip for which a tip value is declared. This is formed
		///   as the hash of the tuple of the original tip `reason` and the beneficiary account ID.
		///
		/// # <weight>
		/// - Complexity: `O(T)` where `T` is the number of tippers. decoding `Tipper` vec of length
		///   `T`. `T` is charged as upper bound given by `ContainsLengthBound`. The actual cost
		///   depends on the implementation of `T::Tippers`.
		/// - DbReads: `Tips`, `Tippers`, `tip finder`
		/// - DbWrites: `Reasons`, `Tips`, `Tippers`, `tip finder`
		/// # </weight>
		#[pallet::call_index(4)]
		#[pallet::weight(<T as Config<I>>::WeightInfo::close_tip(T::Tippers::max_len() as u32))]
		pub fn close_tip(origin: OriginFor<T>, hash: T::Hash) -> DispatchResult {
			ensure_signed(origin)?;

			let tip = Tips::<T, I>::get(hash).ok_or(Error::<T, I>::UnknownTip)?;
			let n = tip.closes.as_ref().ok_or(Error::<T, I>::StillOpen)?;
			ensure!(frame_system::Pallet::<T>::block_number() >= *n, Error::<T, I>::Premature);
			// closed.
			Reasons::<T, I>::remove(&tip.reason);
			Tips::<T, I>::remove(hash);
			Self::payout_tip(hash, tip);
			Ok(())
		}

		/// Remove and slash an already-open tip.
		///
		/// May only be called from `T::RejectOrigin`.
		///
		/// As a result, the finder is slashed and the deposits are lost.
		///
		/// Emits `TipSlashed` if successful.
		///
		/// # <weight>
		///   `T` is charged as upper bound given by `ContainsLengthBound`.
		///   The actual cost depends on the implementation of `T::Tippers`.
		/// # </weight>
		#[pallet::call_index(5)]
		#[pallet::weight(<T as Config<I>>::WeightInfo::slash_tip(T::Tippers::max_len() as u32))]
		pub fn slash_tip(origin: OriginFor<T>, hash: T::Hash) -> DispatchResult {
			T::RejectOrigin::ensure_origin(origin)?;

			let tip = Tips::<T, I>::take(hash).ok_or(Error::<T, I>::UnknownTip)?;

			if !tip.deposit.is_zero() {
				let imbalance = T::Currency::slash_reserved(&tip.finder, tip.deposit).0;
				T::OnSlash::on_unbalanced(imbalance);
			}
			Reasons::<T, I>::remove(&tip.reason);
			Self::deposit_event(Event::TipSlashed {
				tip_hash: hash,
				finder: tip.finder,
				deposit: tip.deposit,
			});
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

	/// Given a mutable reference to an `OpenTip`, insert the tip into it and check whether it
	/// closes, if so, then deposit the relevant event and set closing accordingly.
	///
	/// `O(T)` and one storage access.
	fn insert_tip_and_check_closing(
		tip: &mut OpenTip<T::AccountId, BalanceOf<T, I>, T::BlockNumber, T::Hash>,
		tipper: T::AccountId,
		tip_value: BalanceOf<T, I>,
	) -> bool {
		match tip.tips.binary_search_by_key(&&tipper, |x| &x.0) {
			Ok(pos) => tip.tips[pos] = (tipper, tip_value),
			Err(pos) => tip.tips.insert(pos, (tipper, tip_value)),
		}
		Self::retain_active_tips(&mut tip.tips);
		let threshold = (T::Tippers::count() + 1) / 2;
		if tip.tips.len() >= threshold && tip.closes.is_none() {
			tip.closes = Some(frame_system::Pallet::<T>::block_number() + T::TipCountdown::get());
			true
		} else {
			false
		}
	}

	/// Remove any non-members of `Tippers` from a `tips` vector. `O(T)`.
	fn retain_active_tips(tips: &mut Vec<(T::AccountId, BalanceOf<T, I>)>) {
		let members = T::Tippers::sorted_members();
		let mut members_iter = members.iter();
		let mut member = members_iter.next();
		tips.retain(|(ref a, _)| loop {
			match member {
				None => break false,
				Some(m) if m > a => break false,
				Some(m) => {
					member = members_iter.next();
					if m < a {
						continue
					} else {
						break true
					}
				},
			}
		});
	}

	/// Execute the payout of a tip.
	///
	/// Up to three balance operations.
	/// Plus `O(T)` (`T` is Tippers length).
	fn payout_tip(
		hash: T::Hash,
		tip: OpenTip<T::AccountId, BalanceOf<T, I>, T::BlockNumber, T::Hash>,
	) {
		let mut tips = tip.tips;
		Self::retain_active_tips(&mut tips);
		tips.sort_by_key(|i| i.1);

		let treasury = Self::account_id();
		let max_payout = pallet_treasury::Pallet::<T, I>::pot();

		let mut payout = tips[tips.len() / 2].1.min(max_payout);
		if !tip.deposit.is_zero() {
			let err_amount = T::Currency::unreserve(&tip.finder, tip.deposit);
			debug_assert!(err_amount.is_zero());
		}

		if tip.finders_fee && tip.finder != tip.who {
			// pay out the finder's fee.
			let finders_fee = T::TipFindersFee::get() * payout;
			payout -= finders_fee;
			// this should go through given we checked it's at most the free balance, but still
			// we only make a best-effort.
			let res = T::Currency::transfer(&treasury, &tip.finder, finders_fee, KeepAlive);
			debug_assert!(res.is_ok());
		}

		// same as above: best-effort only.
		let res = T::Currency::transfer(&treasury, &tip.who, payout, KeepAlive);
		debug_assert!(res.is_ok());
		Self::deposit_event(Event::TipClosed { tip_hash: hash, who: tip.who, payout });
	}

	pub fn migrate_retract_tip_for_tip_new(module: &[u8], item: &[u8]) {
		/// An open tipping "motion". Retains all details of a tip including information on the
		/// finder and the members who have voted.
		#[derive(Clone, Eq, PartialEq, Encode, Decode, RuntimeDebug)]
		pub struct OldOpenTip<
			AccountId: Parameter,
			Balance: Parameter,
			BlockNumber: Parameter,
			Hash: Parameter,
		> {
			/// The hash of the reason for the tip. The reason should be a human-readable UTF-8
			/// encoded string. A URL would be sensible.
			reason: Hash,
			/// The account to be tipped.
			who: AccountId,
			/// The account who began this tip and the amount held on deposit.
			finder: Option<(AccountId, Balance)>,
			/// The block number at which this tip will close if `Some`. If `None`, then no closing
			/// is scheduled.
			closes: Option<BlockNumber>,
			/// The members who have voted for this tip. Sorted by AccountId.
			tips: Vec<(AccountId, Balance)>,
		}

		use frame_support::{migration::storage_key_iter, Twox64Concat};

		let zero_account = T::AccountId::decode(&mut TrailingZeroInput::new(&[][..]))
			.expect("infinite input; qed");

		for (hash, old_tip) in storage_key_iter::<
			T::Hash,
			OldOpenTip<T::AccountId, BalanceOf<T, I>, T::BlockNumber, T::Hash>,
			Twox64Concat,
		>(module, item)
		.drain()
		{
			let (finder, deposit, finders_fee) = match old_tip.finder {
				Some((finder, deposit)) => (finder, deposit, true),
				None => (zero_account.clone(), Zero::zero(), false),
			};
			let new_tip = OpenTip {
				reason: old_tip.reason,
				who: old_tip.who,
				finder,
				deposit,
				closes: old_tip.closes,
				tips: old_tip.tips,
				finders_fee,
			};
			Tips::<T, I>::insert(hash, new_tip)
		}
	}
}
