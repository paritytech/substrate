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
use sp_runtime::{RuntimeDebug, PerThing};
use sp_std::fmt::Debug;

pub type BalanceOf<T, I = ()> =
	<<T as Config<I>>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
pub type NegativeImbalanceOf<T, I> = <<T as Config<I>>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::NegativeImbalance;
pub type CallOf<T, I> = <T as Config<I>>::Call;
pub type VotesOf<T, I> = <T as Config<I>>::Votes;
pub type TallyOf<T, I> = <T as Config<I>>::Tally;
pub type PalletsOriginOf<T> = <<T as frame_system::Config>::Origin as OriginTrait>::PalletsOrigin;
pub type ReferendumInfoOf<T, I> = ReferendumInfo<
	TrackIdOf<T, I>,
	PalletsOriginOf<T>,
	<T as frame_system::Config>::BlockNumber,
	<T as frame_system::Config>::Hash,
	BalanceOf<T, I>,
	TallyOf<T, I>,
	<T as frame_system::Config>::AccountId,
	ScheduleAddressOf<T, I>,
>;
pub type ReferendumStatusOf<T, I> = ReferendumStatus<
	TrackIdOf<T, I>,
	PalletsOriginOf<T>,
	<T as frame_system::Config>::BlockNumber,
	<T as frame_system::Config>::Hash,
	BalanceOf<T, I>,
	TallyOf<T, I>,
	<T as frame_system::Config>::AccountId,
	ScheduleAddressOf<T, I>,
>;
pub type DecidingStatusOf<T> = DecidingStatus<<T as frame_system::Config>::BlockNumber>;
pub type TrackInfoOf<T, I = ()> =
	TrackInfo<BalanceOf<T, I>, <T as frame_system::Config>::BlockNumber>;
pub type TrackIdOf<T, I> = <<T as Config<I>>::Tracks as TracksInfo<
	BalanceOf<T, I>,
	<T as frame_system::Config>::BlockNumber,
>>::Id;
pub type ScheduleAddressOf<T, I> = <<T as Config<I>>::Scheduler as Anon<
	<T as frame_system::Config>::BlockNumber,
	CallOf<T, I>,
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
		self.force_insert_keep_right(index, t).is_ok()
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
	pub(crate) enactment: DispatchTime<Moment>,
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
	/// Stepped curve, beginning at `(0, begin)`, then remaining constant for `period`, at which
	/// point it steps down to `(period, begin - step)`. It then remains constant for another
	/// `period` before stepping down to `(period * 2, begin - step * 2)`. This pattern continues
	/// but the `y` component has a lower limit of `end`.
	SteppedDecreasing { begin: Perbill, end: Perbill, step: Perbill, period: Perbill },
	/// A simple recipocal (`K/x + O`) curve: `factor` is `K` and `offset` is `O`.
	Reciprocal { factor: Perbill, offset: Perbill },
}

impl Curve {
	/// Determine the `y` value for the given `x` value.
	pub(crate) fn threshold(&self, x: Perbill) -> Perbill {
		match self {
			Self::LinearDecreasing { begin, delta } => *begin - (*delta * x).min(*begin),
			Self::SteppedDecreasing { begin, end, step, period } =>
				(*begin - (step.int_mul(x.int_div(*period))).min(*begin)).max(*end),
			Self::Reciprocal { factor, offset } => {
				let x_offset = factor.saturating_div(offset.left_from_one());
				// Actual curve is y = factor / (x + x_offset) + offset
				// we want to avoid saturating prior to the division.
				Perbill::from_rational(factor.deconstruct(), x.deconstruct() + x_offset.deconstruct()).saturating_add(*offset)
			}
		}
	}

	/// Determine the smallest `x` value such that `passing` returns `true` when passed along with
	/// the given `y` value.
	///
	/// If `passing` never returns `true` for any value of `x` when paired with `y`, then
	/// `Perbill::one` may be returned.
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
					*delta
				} else {
					(*begin - y.min(*begin)).min(*delta) / *delta
				},
			Self::SteppedDecreasing { begin, end, step, period } =>
				if y < *end {
					Perbill::one()
				} else {
					period.int_mul((*begin - y.min(*begin) + step.less_epsilon().unwrap_or(Zero::zero())).int_div(*step))
				},
			Self::Reciprocal { factor, offset } => {
				let x_offset = factor.saturating_div(offset.left_from_one());
				// Actual curve is y = factor / (x + x_offset) + offset
				// Ergo curve is x = factor / (y - offset) - x_offset
				// To avoid pre-saturation problems, we move the x_offset term to happen prior to
				// the division.
				// So:
				// yo := y - offset
				// x = (factor - x_offset * yo) / yo
				if y < *offset {
					Perbill::one()
				} else {
					let yo = y - *offset;
					factor.saturating_sub(x_offset * yo).saturating_div(yo)
				}
			}
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
			Self::SteppedDecreasing { begin, end, step, period } => {
				write!(
					f,
					"Stepped[(0, {}%) -> (1, {}%) by ({}%, {}%)]",
					*begin * 100u32,
					*end * 100u32,
					*period * 100u32,
					*step * 100u32,
				)
			},
			Self::Reciprocal { factor, offset } => {
				write!(
					f,
					"Reciprocal[factor of {}%, offset of {}%]",
					*factor * 100u32,
					*offset * 100u32,
				)
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_runtime::PerThing;
	use frame_support::traits::ConstU32;

	fn percent(x: u32) -> Perbill {
		Perbill::from_percent(x)
	}

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

	#[test]
	fn basic_reciprocal_works() {
		let c: Curve = Curve::Reciprocal {
			factor: percent(5),
			offset: percent(0),
		};

		for i in 0..1000u32 {
			let x = Perbill::from_rational(i, 1000u32);

			let threshold_at_x = c.threshold(x);
			let min_delay_for_threshold = c.delay(threshold_at_x);
			assert!(min_delay_for_threshold >= x);

			let delay_for_x = c.delay(x);
			let min_threshold_for_delay = c.threshold(delay_for_x);
			assert!(min_threshold_for_delay >= x);
		}

		assert_eq!(c.threshold(percent(0)) * 100u32, 100);
		assert_eq!(c.threshold(percent(1)) * 100u32, 83);
		assert_eq!(c.threshold(percent(2)) * 100u32, 71);
		assert_eq!(c.threshold(percent(3)) * 100u32, 62);
		assert_eq!(c.threshold(percent(4)) * 100u32, 56);
		assert_eq!(c.threshold(percent(5)) * 100u32, 50);
		assert_eq!(c.threshold(percent(6)) * 100u32, 45);
		assert_eq!(c.threshold(percent(7)) * 100u32, 42);
		assert_eq!(c.threshold(percent(8)) * 100u32, 38);
		assert_eq!(c.threshold(percent(9)) * 100u32, 36);
		assert_eq!(c.threshold(percent(10)) * 100u32, 33);
		assert_eq!(c.threshold(percent(15)) * 100u32, 25);
		assert_eq!(c.threshold(percent(20)) * 100u32, 20);
		assert_eq!(c.threshold(percent(25)) * 100u32, 17);
		assert_eq!(c.threshold(percent(30)) * 100u32, 14);
		assert_eq!(c.threshold(percent(35)) * 100u32, 12);
		assert_eq!(c.threshold(percent(40)) * 100u32, 11);
		assert_eq!(c.threshold(percent(45)) * 100u32, 10);
		assert_eq!(c.threshold(percent(50)) * 100u32, 9);
		assert_eq!(c.threshold(percent(55)) * 100u32, 8);
		assert_eq!(c.threshold(percent(60)) * 100u32, 8);
		assert_eq!(c.threshold(percent(65)) * 100u32, 7);
		assert_eq!(c.threshold(percent(70)) * 100u32, 7);
		assert_eq!(c.threshold(percent(75)) * 100u32, 6);
		assert_eq!(c.threshold(percent(80)) * 100u32, 6);
		assert_eq!(c.threshold(percent(85)) * 100u32, 6);
		assert_eq!(c.threshold(percent(90)) * 100u32, 5);
		assert_eq!(c.threshold(percent(95)) * 100u32, 5);
		assert_eq!(c.threshold(percent(100)) * 100u32, 5);

		assert_eq!(c.delay(percent(0)) * 100u32, 100);
		assert_eq!(c.delay(percent(1)) * 100u32, 100);
		assert_eq!(c.delay(percent(2)) * 100u32, 100);
		assert_eq!(c.delay(percent(3)) * 100u32, 100);
		assert_eq!(c.delay(percent(4)) * 100u32, 100);
		assert_eq!(c.delay(percent(5)) * 100u32, 95);
		assert_eq!(c.delay(percent(6)) * 100u32, 78);
		assert_eq!(c.delay(percent(7)) * 100u32, 66);
		assert_eq!(c.delay(percent(8)) * 100u32, 57);
		assert_eq!(c.delay(percent(9)) * 100u32, 51);
		assert_eq!(c.delay(percent(10)) * 100u32, 45);
		assert_eq!(c.delay(percent(15)) * 100u32, 28);
		assert_eq!(c.delay(percent(20)) * 100u32, 20);
		assert_eq!(c.delay(percent(25)) * 100u32, 15);
		assert_eq!(c.delay(percent(30)) * 100u32, 12);
		assert_eq!(c.delay(percent(35)) * 100u32, 9);
		assert_eq!(c.delay(percent(40)) * 100u32, 7);
		assert_eq!(c.delay(percent(45)) * 100u32, 6);
		assert_eq!(c.delay(percent(50)) * 100u32, 5);
		assert_eq!(c.delay(percent(55)) * 100u32, 4);
		assert_eq!(c.delay(percent(60)) * 100u32, 3);
		assert_eq!(c.delay(percent(65)) * 100u32, 3);
		assert_eq!(c.delay(percent(70)) * 100u32, 2);
		assert_eq!(c.delay(percent(75)) * 100u32, 2);
		assert_eq!(c.delay(percent(80)) * 100u32, 1);
		assert_eq!(c.delay(percent(85)) * 100u32, 1);
		assert_eq!(c.delay(percent(90)) * 100u32, 1);
		assert_eq!(c.delay(percent(95)) * 100u32, 0);
		assert_eq!(c.delay(percent(100)) * 100u32, 0);
	}

	#[test]
	fn offset_reciprocal_works() {
		let c: Curve = Curve::Reciprocal {
			factor: percent(10),
			offset: percent(50),
		};

		for i in 0..1000u32 {
			let x = Perbill::from_rational(i, 1000u32);

			let threshold_at_x = c.threshold(x);
			let min_delay_for_threshold = c.delay(threshold_at_x);
			assert!(min_delay_for_threshold >= x);

			let delay_for_x = c.delay(x);
			let min_threshold_for_delay = c.threshold(delay_for_x);
			assert!(min_threshold_for_delay >= x);
		}

		assert_eq!(c.threshold(percent(0)) * 100u32, 100);
		assert_eq!(c.threshold(percent(10)) * 100u32, 83);
		assert_eq!(c.threshold(percent(20)) * 100u32, 75);
		assert_eq!(c.threshold(percent(30)) * 100u32, 70);
		assert_eq!(c.threshold(percent(40)) * 100u32, 67);
		assert_eq!(c.threshold(percent(50)) * 100u32, 64);
		assert_eq!(c.threshold(percent(60)) * 100u32, 62);
		assert_eq!(c.threshold(percent(70)) * 100u32, 61);
		assert_eq!(c.threshold(percent(80)) * 100u32, 60);
		assert_eq!(c.threshold(percent(90)) * 100u32, 59);
		assert_eq!(c.threshold(percent(100)) * 100u32, 58);

		assert_eq!(c.delay(percent(0)) * 100u32, 100);
		assert_eq!(c.delay(percent(10)) * 100u32, 100);
		assert_eq!(c.delay(percent(20)) * 100u32, 100);
		assert_eq!(c.delay(percent(30)) * 100u32, 100);
		assert_eq!(c.delay(percent(40)) * 100u32, 100);
		assert_eq!(c.delay(percent(50)) * 100u32, 100);
		assert_eq!(c.delay(percent(60)) * 100u32, 80);
		assert_eq!(c.delay(percent(70)) * 100u32, 30);
		assert_eq!(c.delay(percent(80)) * 100u32, 13);
		assert_eq!(c.delay(percent(90)) * 100u32, 5);
		assert_eq!(c.delay(percent(100)) * 100u32, 0);
	}

	#[test]
	fn stepped_decreasing_works() {
		let c = Curve::SteppedDecreasing {
			begin: percent(80),
			end: percent(30),
			step: percent(10),
			period: percent(15),
		};
		assert_eq!(c.threshold(percent(0)), percent(80));
		assert_eq!(c.threshold(percent(15).less_epsilon().unwrap()), percent(80));
		assert_eq!(c.threshold(percent(15)), percent(70));
		assert_eq!(c.threshold(percent(30).less_epsilon().unwrap()), percent(70));
		assert_eq!(c.threshold(percent(30)), percent(60));
		assert_eq!(c.threshold(percent(45).less_epsilon().unwrap()), percent(60));
		assert_eq!(c.threshold(percent(45)), percent(50));
		assert_eq!(c.threshold(percent(60).less_epsilon().unwrap()), percent(50));
		assert_eq!(c.threshold(percent(60)), percent(40));
		assert_eq!(c.threshold(percent(75).less_epsilon().unwrap()), percent(40));
		assert_eq!(c.threshold(percent(75)), percent(30));
		assert_eq!(c.threshold(percent(100)), percent(30));

		assert_eq!(c.delay(percent(100)), percent(0));
		assert_eq!(c.delay(percent(80)), percent(0));
		assert_eq!(c.delay(percent(80).less_epsilon().unwrap()), percent(15));
		assert_eq!(c.delay(percent(70)), percent(15));
		assert_eq!(c.delay(percent(70).less_epsilon().unwrap()), percent(30));
		assert_eq!(c.delay(percent(60)), percent(30));
		assert_eq!(c.delay(percent(60).less_epsilon().unwrap()), percent(45));
		assert_eq!(c.delay(percent(50)), percent(45));
		assert_eq!(c.delay(percent(50).less_epsilon().unwrap()), percent(60));
		assert_eq!(c.delay(percent(40)), percent(60));
		assert_eq!(c.delay(percent(40).less_epsilon().unwrap()), percent(75));
		assert_eq!(c.delay(percent(30)), percent(75));
		assert_eq!(c.delay(percent(30).less_epsilon().unwrap()), percent(100));
		assert_eq!(c.delay(percent(0)), percent(100));
	}
}