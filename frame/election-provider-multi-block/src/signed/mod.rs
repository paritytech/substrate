// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! The signed phase of the multi-block election system.
//!
//! Signed submissions work on the basis of keeping a queue of submissions from random signed
//! accounts, and sorting them based on the best claimed score to the worse.
//!
//! Once the time to evaluate the signed phase comes, the solutions are checked from best-to-worse
//! claim, and they end up in either of the 3 buckets:
//!
//! 1. If they are the first, correct solution (and consequently the best one, since we start
//!    evaluating from the best claim), they are rewarded.
//! 2. Any solution after the first correct solution is refunded in an unbiased way.
//! 3. Any invalid solution that wasted valuable blockchain time gets slashed for their deposit.

use codec::{Decode, Encode, MaxEncodedLen};
use frame_election_provider_support::PageIndex;
use frame_support::{
	ensure,
	traits::{Currency, DefensiveOption, Get, ReservableCurrency},
	BoundedVec,
};
use scale_info::TypeInfo;
use sp_npos_elections::ElectionScore;
use sp_runtime::traits::Zero;

/// Exports of this pallet
pub use pallet::*;

use crate::verifier::{
	AsynchronousVerifier, SolutionDataProvider, Status, VerificationResult, Verifier,
};

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;

#[cfg(test)]
mod tests;

type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, Default)]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct SubmissionMetadata<T: Config> {
	deposit: BalanceOf<T>,
	fee: BalanceOf<T>,
	reward: BalanceOf<T>,
	claimed_score: ElectionScore,
	pages: BoundedVec<bool, T::Pages>,
}

impl<T: Config> SolutionDataProvider for Pallet<T> {
	type Solution = T::Solution;
	fn get_page(page: PageIndex) -> Option<Self::Solution> {
		// note: a non-existing page will still be treated as merely an empty page. This could be
		// re-considered.
		Submissions::<T>::leader()
			.map(|(who, _score)| Submissions::<T>::get_page_of(&who, page).unwrap_or_default())
	}

	fn get_score() -> Option<ElectionScore> {
		Submissions::<T>::leader().map(|(_who, score)| score)
	}

	fn report_result(result: crate::verifier::VerificationResult) {
		// assumption of the trait.
		debug_assert_eq!(<T::Verifier as AsynchronousVerifier>::status(), Status::Nothing);

		match result {
			VerificationResult::Queued => {
				// defensive: if there is a result to be reported, then we must have had some
				// leader.
				if let Some(winner) = Submissions::<T>::leader().defensive_map(|(x, _)| x) {
					let metadata = Submissions::<T>::metadata(&winner).unwrap();

					// first, let's give them their reward.
					let reward = metadata.reward + metadata.fee;
					let imbalance = T::Currency::deposit_creating(&winner, reward);
					Self::deposit_event(Event::<T>::Rewarded(winner.clone(), reward));

					// then, unreserve their deposit
					let _remaining = T::Currency::unreserve(&winner, metadata.deposit);
					debug_assert!(_remaining.is_zero());

					// remove the winning data of the winner, we don't need it anymore.
					Submissions::<T>::remove_data(&winner);

					// For now, I will wipe everything on the spot, but in ideal case, we would do
					// it over time.
					// TODO: what we need a generic "StateGarbageCollector", to which you give a
					// bunch of storage keys, and it will clean them for you on_idle. It should just
					// be able to accept one job at a time, and report back to you if it is done
					// doing what it was doing, or not.
					for discarded in Submissions::<T>::sorted_submitters().into_iter().skip(1) {
						let discarded_metadata = Submissions::<T>::metadata(&discarded).unwrap();
						let _remaining =
							T::Currency::unreserve(&discarded, discarded_metadata.deposit);
						debug_assert!(_remaining.is_zero());
						Submissions::<T>::remove_data(&discarded);
						Self::deposit_event(Event::<T>::Discarded(discarded));
					}

					// finally, kill the overall sorted list as well.
					Submissions::<T>::clear_list();

					// everything should have been clean.
					debug_assert_eq!(Submissions::<T>::submissions_iter().count(), 0);
					debug_assert_eq!(Submissions::<T>::metadata_iter().count(), 0);
					debug_assert!(Submissions::<T>::sorted_submitters().is_empty());
				}
			},
			VerificationResult::Rejected => {
				// defensive: if there is a result to be reported, then we must have had some
				// leader.
				if let Some(loser) = Submissions::<T>::take_leader().defensive_map(|(x, _)| x) {
					let metadata = Submissions::<T>::metadata(&loser).unwrap();

					// first, let's slash their deposit.
					let slash = metadata.deposit;
					let (imbalance, _remainder) = T::Currency::slash_reserved(&loser, slash);
					debug_assert!(_remainder.is_zero());
					Self::deposit_event(Event::<T>::Slashed(loser.clone(), slash));

					// they are already removed from the sorted list, next remove their submission
					// data as well.
					Submissions::<T>::remove_data(&loser);
					debug_assert!(!Submissions::<T>::sorted_submitters().contains(&loser));

					// inform the verifier that they can now try again, if we're still in the signed
					// validation phase.
					if crate::Pallet::<T>::current_phase().is_signed_validation() {
						<T::Verifier as AsynchronousVerifier>::start();
					}
				}
			},
			VerificationResult::DataUnavailable => {
				unreachable!("TODO")
			},
		}
	}
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use crate::verifier::AsynchronousVerifier;
	use frame_support::{
		dispatch::DispatchResultWithPostInfo,
		pallet_prelude::{StorageDoubleMap, ValueQuery, *},
		traits::{Defensive, EstimateCallFee, TryCollect},
	};
	use frame_system::{ensure_signed, pallet_prelude::*};
	use sp_runtime::traits::Zero;

	pub trait WeightInfo {}
	impl WeightInfo for () {}

	#[pallet::config]
	#[pallet::disable_frame_system_supertrait_check]
	pub trait Config: crate::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		type Currency: ReservableCurrency<Self::AccountId>;

		type DepositBase: Get<BalanceOf<Self>>;
		type DepositPerPage: Get<BalanceOf<Self>>;

		type RewardBase: Get<BalanceOf<Self>>;

		type MaxSubmissions: Get<u32>;

		type EstimateCallFee: EstimateCallFee<Call<Self>, BalanceOf<Self>>;

		type WeightInfo: WeightInfo;
	}

	pub(crate) struct Submissions<T: Config>(sp_std::marker::PhantomData<T>);
	impl<T: Config> Submissions<T> {
		// -- mutating functions

		/// Remove all data associated with this submitter, namely the metadata and all submission
		/// pages.
		///
		/// NOTE: this does not remove
		pub(crate) fn remove_data(who: &T::AccountId) {
			SubmissionMetadataStorage::<T>::remove(who);
			SubmissionStorage::<T>::remove_prefix(who, None);
		}

		pub(crate) fn clear_list() {
			SortedScores::<T>::kill()
		}

		pub(crate) fn take_leader() -> Option<(T::AccountId, ElectionScore)> {
			SortedScores::<T>::mutate(|sorted| sorted.pop())
		}

		// TODO: there's too much logic here, consider re-organizing it a bit better.
		pub(crate) fn try_insert(
			who: &T::AccountId,
			metadata: SubmissionMetadata<T>,
		) -> DispatchResultWithPostInfo {
			// update our ranking, if suitable. This is sorted based on score, but we want to first
			// check by account-id.
			let mut sorted_scores = SortedScores::<T>::get();
			if let Some(pos) = sorted_scores.iter().position(|(x, _)| x == who) {
				// must have already existed, just update their claim.
				debug_assert!(SubmissionMetadataStorage::<T>::contains_key(who));
				// Note: due to the limited API of BoundedVec, using IndexMut is our only way.
				sorted_scores[pos].1 = metadata.claimed_score;
			} else {
				// must be new.
				debug_assert!(!SubmissionMetadataStorage::<T>::contains_key(who));
				let pos = match sorted_scores
					.binary_search_by_key(&metadata.claimed_score, |(_, y)| *y)
				{
					// an equal score exists, unlikely, but could very well happen. We just put them
					// next to each other.
					Ok(pos) => pos,
					// new score, should be inserted in this pos.
					Err(pos) => pos,
				};
				// NOTE: we can check this a bit earlier.
				sorted_scores
					.try_insert(pos, (who.clone(), metadata.claimed_score))
					.map_err::<DispatchError, _>(|_| "too many submissions".into())?;
			}

			// must contain no dupe account keys.
			debug_assert_eq!(
				sorted_scores
					.clone()
					.into_iter()
					.map(|(x, _)| x)
					.collect::<sp_std::collections::btree_set::BTreeSet<_>>()
					.len(),
				sorted_scores.len()
			);

			SortedScores::<T>::put(sorted_scores);
			SubmissionMetadataStorage::<T>::insert(who, metadata);
			Ok(().into())
		}

		/// Submit a page of `solution` to the `page` index of `who`'s submission.
		///
		/// Updates the deposit in the metadata accordingly.
		///
		/// - If `maybe_solution` is `None`, then the given page is deleted.
		/// - `who` must have already registered their submission.
		/// - If the page is duplicate, it will replaced.
		pub(crate) fn try_mutate_page(
			who: &T::AccountId,
			page: PageIndex,
			maybe_solution: Option<T::Solution>,
		) -> DispatchResultWithPostInfo {
			let mut metadata = SubmissionMetadataStorage::<T>::get(who).ok_or("not registered")?;
			ensure!(page < T::Pages::get(), "bad page index");

			// defensive only: we resize `meta.pages` once to be `T::Pages` elements once, and never
			// resize it again; `page` is checked here to be in bound; element must exist; qed.
			if let Some(page_bit) = metadata.pages.get_mut(page as usize).defensive() {
				*page_bit = maybe_solution.is_some();
			}

			// update deposit.
			let new_pages: BalanceOf<T> =
				(metadata.pages.iter().filter(|x| **x).count() as u32).into();
			let new_deposit = T::DepositBase::get() + T::DepositPerPage::get() * new_pages;
			let old_deposit = metadata.deposit;
			if new_deposit > old_deposit {
				let to_reserve = new_deposit - old_deposit;
				T::Currency::reserve(who, to_reserve)?;
			} else {
				let to_unreserve = old_deposit - new_deposit;
				let _ = T::Currency::unreserve(who, to_unreserve);
			};
			metadata.deposit = new_deposit;

			SubmissionStorage::<T>::mutate_exists(who, page, |maybe_old_solution| {
				*maybe_old_solution = maybe_solution
			});
			SubmissionMetadataStorage::<T>::insert(who, metadata);
			Ok(().into())
		}

		// -- getter functions

		pub(crate) fn metadata(who: &T::AccountId) -> Option<SubmissionMetadata<T>> {
			SubmissionMetadataStorage::<T>::get(who)
		}

		pub(crate) fn leader() -> Option<(T::AccountId, ElectionScore)> {
			SortedScores::<T>::get().last().cloned()
		}

		pub(crate) fn sorted_submitters() -> BoundedVec<T::AccountId, T::MaxSubmissions> {
			SortedScores::<T>::get().into_iter().map(|(x, _)| x).try_collect().unwrap()
		}

		pub(crate) fn get_page_of(who: &T::AccountId, page: PageIndex) -> Option<T::Solution> {
			SubmissionStorage::<T>::get(who, &page)
		}

		#[cfg(any(test, debug_assertions))]
		pub(crate) fn submissions_iter(
		) -> impl Iterator<Item = (T::AccountId, PageIndex, T::Solution)> {
			SubmissionStorage::<T>::iter()
		}

		#[cfg(any(test, debug_assertions))]
		pub(crate) fn metadata_iter() -> impl Iterator<Item = (T::AccountId, SubmissionMetadata<T>)>
		{
			SubmissionMetadataStorage::<T>::iter()
		}

		/// Ensure that all the storage items managed by this struct are in `killed` state, meaning
		/// that in the expect state after an election is OVER.
		#[cfg(any(test, debug_assertions))]
		pub(crate) fn ensure_killed() {
			assert_eq!(Self::metadata_iter().count(), 0);
			assert_eq!(Self::submissions_iter().count(), 0);
			assert_eq!(Self::sorted_submitters().len(), 0);
		}
	}

	#[pallet::storage]
	type SortedScores<T: Config> =
		StorageValue<_, BoundedVec<(T::AccountId, ElectionScore), T::MaxSubmissions>, ValueQuery>;

	/// Double map from (account, page) to a solution page.
	#[pallet::storage]
	type SubmissionStorage<T: Config> =
		StorageDoubleMap<_, Twox64Concat, T::AccountId, Twox64Concat, PageIndex, T::Solution>;

	/// Map from account to the metadata of their submission.
	///
	/// invariant: for any Key1 of type `AccountId` in [`Submissions`], this storage map also has a
	/// value.
	#[pallet::storage]
	type SubmissionMetadataStorage<T: Config> =
		StorageMap<_, Twox64Concat, T::AccountId, SubmissionMetadata<T>>;

	#[pallet::pallet]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Upcoming submission has been registered for the given account, with the given score.
		Registered(T::AccountId, ElectionScore),
		/// A page of solution solution with the given index has been stored for the given account.
		Stored(T::AccountId, PageIndex),
		Rewarded(T::AccountId, BalanceOf<T>),
		Slashed(T::AccountId, BalanceOf<T>),
		Discarded(T::AccountId),
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Submit an upcoming solution for registration.
		///
		/// If `who` already registered, it updates it. Else, a new a entry is added, if the bound
		/// (`T::MaxSubmissions`) is not met yet.
		#[pallet::weight(0)]
		pub fn register(
			origin: OriginFor<T>,
			claimed_score: ElectionScore,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			ensure!(crate::Pallet::<T>::current_phase().is_signed(), "phase not signed");

			let deposit = T::DepositBase::get();
			let reward = T::RewardBase::get();
			let fee = Zero::zero();
			let mut pages = BoundedVec::<_, _>::with_bounded_capacity(T::Pages::get() as usize);
			pages.bounded_resize(T::Pages::get() as usize, false);

			let new_metadata = SubmissionMetadata { claimed_score, deposit, reward, fee, pages };

			T::Currency::reserve(&who, deposit).map_err(|_| "insufficient funds")?;

			let _ = Submissions::<T>::try_insert(&who, new_metadata)?;
			Self::deposit_event(Event::<T>::Registered(who, claimed_score));
			Ok(().into())
		}

		/// Retract a submission.
		///
		/// Needs to pay for the removal of all associated storage items, but no string attached
		/// henceforth.
		///
		/// This should lessen the grief, but it should still be fairly expensive, because we don't
		/// want users to register empty slots and all retract at the very end.
		///
		/// Useful for when a submitted realized they have made a mistake.
		#[pallet::weight(0)]
		pub fn retract(
			origin: OriginFor<T>,
			claimed_score: ElectionScore,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			ensure!(crate::Pallet::<T>::current_phase().is_signed(), "phase not signed");
			todo!()
		}

		#[pallet::weight(0)]
		pub fn submit_page(
			origin: OriginFor<T>,
			page: PageIndex,
			maybe_solution: Option<T::Solution>,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			ensure!(crate::Pallet::<T>::current_phase().is_signed(), "phase not signed");

			Submissions::<T>::try_mutate_page(&who, page, maybe_solution)?;
			Self::deposit_event(Event::<T>::Stored(who, page));

			Ok(().into())
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(now: T::BlockNumber) -> Weight {
			// TODO: we could rely on an explicit notification system instead of this.. but anyways.
			if crate::Pallet::<T>::current_phase().is_signed_validation_open_at(now) {
				sublog!(
					info,
					"signed",
					"signed validation started, sending validation start signal? {:?}",
					Submissions::<T>::leader().is_some()
				);
				// start an attempt to verify our best thing.
				if Submissions::<T>::leader().is_some() {
					<T::Verifier as AsynchronousVerifier>::start();
				}
			}

			if crate::Pallet::<T>::current_phase().is_unsigned_open_at(now) {
				// signed validation phase just ended, make sure you stop any ongoing operation.
				sublog!(info, "signed", "signed validation ended, sending validation stop signal",);
				<T::Verifier as AsynchronousVerifier>::stop();
			}

			0
		}
	}
}

impl<T: Config> Pallet<T> {}
