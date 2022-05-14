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

//! Miscellaneous additional datatypes.

use super::*;
use codec::{Decode, Encode, EncodeLike, MaxEncodedLen};
use frame_support::{traits::schedule::Anon, Parameter};
use scale_info::TypeInfo;
use sp_runtime::RuntimeDebug;
use sp_std::fmt::Debug;

pub type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
pub type NegativeImbalanceOf<T> = <<T as Config>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::NegativeImbalance;
pub type CallOf<T> = <T as Config>::Call;
pub type VotesOf<T> = <T as Config>::Votes;
pub type TallyOf<T> = <T as Config>::Tally;
pub type PalletsOriginOf<T> = <<T as frame_system::Config>::Origin as OriginTrait>::PalletsOrigin;
pub type ReferendumInfoOf<T> = ReferendumInfo<
	TrackIdOf<T>,
	PalletsOriginOf<T>,
	<T as frame_system::Config>::BlockNumber,
	<T as frame_system::Config>::Hash,
	BalanceOf<T>,
	TallyOf<T>,
	<T as frame_system::Config>::AccountId,
	ScheduleAddressOf<T>,
>;
pub type ReferendumStatusOf<T> = ReferendumStatus<
	TrackIdOf<T>,
	PalletsOriginOf<T>,
	<T as frame_system::Config>::BlockNumber,
	<T as frame_system::Config>::Hash,
	BalanceOf<T>,
	TallyOf<T>,
	<T as frame_system::Config>::AccountId,
	ScheduleAddressOf<T>,
>;
pub type DecidingStatusOf<T> = DecidingStatus<<T as frame_system::Config>::BlockNumber>;
pub type TrackInfoOf<T> = TrackInfo<BalanceOf<T>, <T as frame_system::Config>::BlockNumber>;
pub type TrackIdOf<T> = <<T as Config>::Tracks as TracksInfo<
	BalanceOf<T>,
	<T as frame_system::Config>::BlockNumber,
>>::Id;
pub type ScheduleAddressOf<T> = <<T as Config>::Scheduler as Anon<
	<T as frame_system::Config>::BlockNumber,
	CallOf<T>,
	PalletsOriginOf<T>,
>>::Address;

/// A referendum index.
pub type ReferendumIndex = u32;

pub trait InsertSorted<T> {
	/// Inserts an item into a sorted series.
	///
	/// Returns `true` if it was inserted, `false` if it would belong beyond the bound of the
	/// series.
	fn insert_sorted_by_key<F: FnMut(&T) -> K, K: PartialOrd<K> + Ord>(
		&mut self,
		t: T,
		f: F,
	) -> bool;
}
impl<T: Ord, S: Get<u32>> InsertSorted<T> for BoundedVec<T, S> {
	fn insert_sorted_by_key<F: FnMut(&T) -> K, K: PartialOrd<K> + Ord>(
		&mut self,
		t: T,
		mut f: F,
	) -> bool {
		let index = self.binary_search_by_key::<K, F>(&f(&t), f).unwrap_or_else(|x| x);
		self.force_insert_keep_right(index, t)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use frame_support::traits::ConstU32;

	#[test]
	fn insert_sorted_works() {
		let mut b: BoundedVec<u32, ConstU32<6>> = vec![20, 30, 40].try_into().unwrap();
		assert!(b.insert_sorted_by_key(10, |&x| x));
		assert_eq!(&b[..], &[10, 20, 30, 40][..]);

		assert!(b.insert_sorted_by_key(60, |&x| x));
		assert_eq!(&b[..], &[10, 20, 30, 40, 60][..]);

		assert!(b.insert_sorted_by_key(50, |&x| x));
		assert_eq!(&b[..], &[10, 20, 30, 40, 50, 60][..]);

		assert!(!b.insert_sorted_by_key(9, |&x| x));
		assert_eq!(&b[..], &[10, 20, 30, 40, 50, 60][..]);

		assert!(b.insert_sorted_by_key(11, |&x| x));
		assert_eq!(&b[..], &[11, 20, 30, 40, 50, 60][..]);

		assert!(b.insert_sorted_by_key(21, |&x| x));
		assert_eq!(&b[..], &[20, 21, 30, 40, 50, 60][..]);

		assert!(b.insert_sorted_by_key(61, |&x| x));
		assert_eq!(&b[..], &[21, 30, 40, 50, 60, 61][..]);

		assert!(b.insert_sorted_by_key(51, |&x| x));
		assert_eq!(&b[..], &[30, 40, 50, 51, 60, 61][..]);
	}
}

#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub struct DecidingStatus<BlockNumber> {
	/// When this referendum began being "decided". If confirming, then the
	/// end will actually be delayed until the end of the confirmation period.
	pub(crate) since: BlockNumber,
	/// If `Some`, then the referendum has entered confirmation stage and will end at
	/// the block number as long as it doesn't lose its approval in the meantime.
	pub(crate) confirming: Option<BlockNumber>,
}

#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub struct Deposit<AccountId, Balance> {
	pub(crate) who: AccountId,
	pub(crate) amount: Balance,
}

#[derive(Clone, Encode, TypeInfo)]
pub struct TrackInfo<Balance, Moment> {
	/// Name of this track. TODO was &'static str
	pub name: &'static str,
	/// A limit for the number of referenda on this track that can be being decided at once.
	/// For Root origin this should generally be just one.
	pub max_deciding: u32,
	/// Amount that must be placed on deposit before a decision can be made.
	pub decision_deposit: Balance,
	/// Amount of time this must be submitted for before a decision can be made.
	pub prepare_period: Moment,
	/// Amount of time that a decision may take to be approved prior to cancellation.
	pub decision_period: Moment,
	/// Amount of time that the approval criteria must hold before it can be approved.
	pub confirm_period: Moment,
	/// Minimum amount of time that an approved proposal must be in the dispatch queue.
	pub min_enactment_period: Moment,
	/// Minimum aye votes as percentage of overall conviction-weighted votes needed for
	/// approval as a function of time into decision period.
	pub min_approval: Curve,
	/// Minimum turnout as percentage of overall population that is needed for
	/// approval as a function of time into decision period.
	pub min_turnout: Curve,
}

/// Information on the voting tracks.
pub trait TracksInfo<Balance, Moment> {
	/// The identifier for a track.
	type Id: Copy + Parameter + Ord + PartialOrd + Send + Sync + 'static;

	/// The origin type from which a track is implied.
	type Origin;

	/// Return the array of known tracks and their information.
	fn tracks() -> &'static [(Self::Id, TrackInfo<Balance, Moment>)];

	/// Determine the voting track for the given `origin`.
	fn track_for(origin: &Self::Origin) -> Result<Self::Id, ()>;

	/// Return the track info for track `id`, by default this just looks it up in `Self::tracks()`.
	fn info(id: Self::Id) -> Option<&'static TrackInfo<Balance, Moment>> {
		Self::tracks().iter().find(|x| &x.0 == &id).map(|x| &x.1)
	}
}

/// Indication of either a specific moment or a delay from a implicitly defined moment.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub enum AtOrAfter<Moment: Parameter> {
	/// Indiciates that the event should occur at the moment given.
	At(Moment),
	/// Indiciates that the event should occur some period of time (defined by the parameter) after
	/// a prior event. The prior event is defined by the context, but for the purposes of
	/// referendum proposals, the "prior event" is the passing of the referendum.
	After(Moment),
}

impl<Moment: AtLeast32BitUnsigned + Copy + Parameter> AtOrAfter<Moment> {
	pub fn evaluate(&self, since: Moment) -> Moment {
		match &self {
			Self::At(m) => *m,
			Self::After(m) => m.saturating_add(since),
		}
	}
}

/// Info regarding an ongoing referendum.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub struct ReferendumStatus<
	TrackId: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
	Origin: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
	Moment: Parameter + Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone + EncodeLike,
	Hash: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
	Balance: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
	Tally: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
	AccountId: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
	ScheduleAddress: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
> {
	/// The track of this referendum.
	pub(crate) track: TrackId,
	/// The origin for this referendum.
	pub(crate) origin: Origin,
	/// The hash of the proposal up for referendum.
	pub(crate) proposal_hash: Hash,
	/// The time the proposal should be scheduled for enactment.
	pub(crate) enactment: AtOrAfter<Moment>,
	/// The time of submission. Once `UndecidingTimeout` passes, it may be closed by anyone if it
	/// `deciding` is `None`.
	pub(crate) submitted: Moment,
	/// The deposit reserved for the submission of this referendum.
	pub(crate) submission_deposit: Deposit<AccountId, Balance>,
	/// The deposit reserved for this referendum to be decided.
	pub(crate) decision_deposit: Option<Deposit<AccountId, Balance>>,
	/// The status of a decision being made. If `None`, it has not entered the deciding period.
	pub(crate) deciding: Option<DecidingStatus<Moment>>,
	/// The current tally of votes in this referendum.
	pub(crate) tally: Tally,
	/// Whether we have been placed in the queue for being decided or not.
	pub(crate) in_queue: bool,
	/// The next scheduled wake-up, if `Some`.
	pub(crate) alarm: Option<(Moment, ScheduleAddress)>,
}

/// Info regarding a referendum, present or past.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub enum ReferendumInfo<
	TrackId: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
	Origin: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
	Moment: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone + EncodeLike,
	Hash: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
	Balance: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
	Tally: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
	AccountId: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
	ScheduleAddress: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
> {
	/// Referendum has been submitted and is being voted on.
	Ongoing(
		ReferendumStatus<TrackId, Origin, Moment, Hash, Balance, Tally, AccountId, ScheduleAddress>,
	),
	/// Referendum finished with approval. Submission deposit is held.
	Approved(Moment, Deposit<AccountId, Balance>, Option<Deposit<AccountId, Balance>>),
	/// Referendum finished with rejection. Submission deposit is held.
	Rejected(Moment, Deposit<AccountId, Balance>, Option<Deposit<AccountId, Balance>>),
	/// Referendum finished with cancelation. Submission deposit is held.
	Cancelled(Moment, Deposit<AccountId, Balance>, Option<Deposit<AccountId, Balance>>),
	/// Referendum finished and was never decided. Submission deposit is held.
	TimedOut(Moment, Deposit<AccountId, Balance>, Option<Deposit<AccountId, Balance>>),
	/// Referendum finished with a kill.
	Killed(Moment),
}

impl<
		TrackId: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
		Origin: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
		Moment: Parameter + Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone + EncodeLike,
		Hash: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
		Balance: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
		Tally: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
		AccountId: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
		ScheduleAddress: Eq + PartialEq + Debug + Encode + Decode + TypeInfo + Clone,
	> ReferendumInfo<TrackId, Origin, Moment, Hash, Balance, Tally, AccountId, ScheduleAddress>
{
	/// Take the Decision Deposit from `self`, if there is one. Returns an `Err` if `self` is not
	/// in a valid state for the Decision Deposit to be refunded.
	pub fn take_decision_deposit(&mut self) -> Result<Option<Deposit<AccountId, Balance>>, ()> {
		use ReferendumInfo::*;
		match self {
			Ongoing(x) if x.decision_deposit.is_none() => Ok(None),
			// Cannot refund deposit if Ongoing as this breaks assumptions.
			Ongoing(_) => Err(()),
			Approved(_, _, d) | Rejected(_, _, d) | TimedOut(_, _, d) | Cancelled(_, _, d) =>
				Ok(d.take()),
			Killed(_) => Ok(None),
		}
	}
}

/// Type for describing a curve over the 2-dimensional space of axes between 0-1, as represented
/// by `(Perbill, Perbill)`.
#[derive(Clone, Eq, PartialEq, Encode, Decode, TypeInfo, MaxEncodedLen)]
#[cfg_attr(not(feature = "std"), derive(RuntimeDebug))]
pub enum Curve {
	/// Linear curve starting at `(0, begin)`, ending at `(period, begin - delta)`.
	LinearDecreasing { begin: Perbill, delta: Perbill },
}

impl Curve {
	/// Determine the `y` value for the given `x` value.
	pub(crate) fn threshold(&self, x: Perbill) -> Perbill {
		match self {
			Self::LinearDecreasing { begin, delta } => *begin - (*delta * x).min(*begin),
		}
	}

	/// Determine the smallest `x` value such that `passing` returns `true` when passed along with
	/// the given `y` value.
	///
	/// ```nocompile
	/// let c = Curve::LinearDecreasing { begin: Perbill::one(), delta: Perbill::one() };
	/// //      ^^^ Can be any curve.
	/// let y = Perbill::from_percent(50);
	/// //      ^^^ Can be any value.
	/// let x = c.delay(y);
	/// assert!(c.passing(x, y));
	/// ```
	pub fn delay(&self, y: Perbill) -> Perbill {
		match self {
			Self::LinearDecreasing { begin, delta } =>
				if delta.is_zero() {
					return *delta
				} else {
					return (*begin - y.min(*begin)).min(*delta) / *delta
				},
		}
	}

	/// Return `true` iff the `y` value is greater than the curve at the `x`.
	pub fn passing(&self, x: Perbill, y: Perbill) -> bool {
		y >= self.threshold(x)
	}
}

#[cfg(feature = "std")]
impl Debug for Curve {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
		match self {
			Self::LinearDecreasing { begin, delta } => {
				write!(
					f,
					"Linear[(0%, {}%) -> (100%, {}%)]",
					*begin * 100u32,
					(*begin - *delta) * 100u32,
				)
			},
		}
	}
}
