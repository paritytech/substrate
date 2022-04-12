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
use sp_runtime::{RuntimeDebug, PerThing, FixedI64, FixedPointNumber};
use sp_arithmetic::Rounding::*;
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
	/// A simple reciprocal (`K/x + O`) curve: `factor` is `K` and `offset` is `O`.
	SimpleReciprocal { factor: Perbill, offset: Perbill },
	/// A reciprocal (`K/(x + K/(1-O)) + O`) curve: `factor` is `K` and `offset` is `O`. This
	/// guarantees the point (0, 1) without resorting to truncation.
	Reciprocal { factor: Perbill, offset: Perbill },
	/// A recipocal (`K/(x+S)-T`) curve: `factor` is `K` and `x_offset` is `S`, `y_offset` is `T`.
	TranslatedReciprocal { factor: FixedI64, x_offset: FixedI64, y_offset: FixedI64 },
}

fn pos_quad_solution(a: FixedI64, b: FixedI64, c: FixedI64) -> FixedI64 {
	let two = FixedI64::saturating_from_integer(2);
	let four = FixedI64::saturating_from_integer(4);
	(-b + (b*b - four*a*c).sqrt().unwrap_or(two)) / (two*a)
}

impl Curve {
	#[cfg(feature = "std")]
	pub fn basic_reciprocal_from_point<N: AtLeast32BitUnsigned>(
		delay: N,
		period: N,
		level: Perbill,
	) -> Curve {
		Self::basic_reciprocal_from_point_and_floor(delay, period, level, Perbill::zero())
	}

	#[cfg(feature = "std")]
	pub fn basic_reciprocal_from_point_and_floor<N: AtLeast32BitUnsigned>(
		delay: N,
		period: N,
		level: Perbill,
		floor: Perbill,
	) -> Curve {
		let delay = Perbill::from_rational(delay, period);
		let offset = floor;
		let ymo = level.saturating_sub(offset);
		let bottom = ymo.saturating_div(offset.left_from_one(), Down).left_from_one();
		let factor = (delay * ymo).saturating_div(bottom, Down);
		Curve::Reciprocal { factor, offset }
	}
	#[cfg(feature = "std")]
	pub fn reciprocal_from_point<N: AtLeast32BitUnsigned>(
		delay: N,
		period: N,
		level: Perbill,
	) -> Curve {
		Self::reciprocal_from_point_and_floor(delay, period, level, Perbill::zero())
	}

	#[cfg(feature = "std")]
	pub fn reciprocal_from_point_and_floor<N: AtLeast32BitUnsigned>(
		delay: N,
		period: N,
		level: Perbill,
		floor: Perbill,
	) -> Curve {
		let delay = Perbill::from_rational(delay, period);
		let floor_fixed = FixedI64::from(floor);
		let mut bounds = (FixedI64::zero(), FixedI64::one());
		let two = FixedI64::saturating_from_integer(2);
		let epsilon = FixedI64::from_inner(1);
		while bounds.1 - bounds.0 > epsilon {
			let factor = (bounds.0 + bounds.1) / two;
			let c = Self::reciprocal_from_factor_and_floor(factor, floor_fixed);
			if c.threshold(delay) > level {
				bounds = (bounds.0, factor)
			} else {
				bounds = (factor, bounds.1)
			}
		}
		let c0 = Self::reciprocal_from_factor_and_floor(bounds.0, floor_fixed);
		let c1 = Self::reciprocal_from_factor_and_floor(bounds.1, floor_fixed);
		let c0_level = c0.threshold(delay);
		let c1_level = c1.threshold(delay);
		if c0_level.max(level) - c0_level.min(level) < c1_level.max(level) - c1_level.min(level) {
			c0
		} else {
			c1
		}
	}

	#[cfg(feature = "std")]
	fn reciprocal_from_factor_and_floor(factor: FixedI64, floor: FixedI64) -> Self {
		let x_offset = pos_quad_solution(FixedI64::one() - floor, FixedI64::one() - floor, -factor);
		let y_offset = floor - factor / (FixedI64::one() + x_offset);
		Curve::TranslatedReciprocal { factor, x_offset, y_offset }
	}

	/// Print some info on the curve.
	#[cfg(feature = "std")]
	pub fn info(&self, days: u32, name: impl std::fmt::Display) {
		let hours = days * 24;
		println!("Curve {name} := {:?}:", self);
		println!("   t + 0h:   {:?}", self.threshold(Perbill::zero()));
		println!("   t + 1h:   {:?}", self.threshold(Perbill::from_rational(1, hours)));
		println!("   t + 2h:   {:?}", self.threshold(Perbill::from_rational(2, hours)));
		println!("   t + 3h:   {:?}", self.threshold(Perbill::from_rational(3, hours)));
		println!("   t + 6h:   {:?}", self.threshold(Perbill::from_rational(6, hours)));
		println!("   t + 12h:  {:?}", self.threshold(Perbill::from_rational(12, hours)));
		println!("   t + 24h:  {:?}", self.threshold(Perbill::from_rational(24, hours)));
		let mut l = 0;
		for &(n, d) in [(1, 12), (1, 8), (1, 4), (1, 2), (3, 4), (1, 1)].iter() {
			let t = days * n / d;
			if t != l {
				println!("   t + {t}d:   {:?}", self.threshold(Perbill::from_rational(t, days)));
				l = t;
			}
		}
		let t = |p: Perbill| -> std::string::String {
			if p.is_one() {
				"never".into()
			} else {
				let minutes = p * (hours * 60);
				if minutes < 60 {
					format!("{} minutes", minutes)
				} else if minutes < 8 * 60 && minutes % 60 != 0 {
					format!("{} hours {} minutes", minutes / 60, minutes % 60)
				} else if minutes < 72 * 60 {
					format!("{} hours", minutes / 60)
				} else if minutes / 60 % 24 == 0 {
					format!("{} days", minutes / 60 / 24)
				} else {
					format!("{} days {} hours", minutes / 60 / 24, minutes / 60 % 24)
				}
			}
		};
		if self.delay(Perbill::from_percent(49)) < Perbill::one() {
			println!("   30% threshold:   {}", t(self.delay(Perbill::from_percent(30))));
			println!("   10% threshold:   {}", t(self.delay(Perbill::from_percent(10))));
			println!("   3% threshold:    {}", t(self.delay(Perbill::from_percent(3))));
			println!("   1% threshold:    {}", t(self.delay(Perbill::from_percent(1))));
			println!("   0.1% threshold:  {}", t(self.delay(Perbill::from_rational(1u32, 1_000))));
			println!("   0.01% threshold: {}", t(self.delay(Perbill::from_rational(1u32, 10_000))));
		} else {
			println!("   99.9% threshold: {}", t(self.delay(Perbill::from_rational(999u32, 1_000))));
			println!("   99% threshold:   {}", t(self.delay(Perbill::from_percent(99))));
			println!("   95% threshold:   {}", t(self.delay(Perbill::from_percent(95))));
			println!("   90% threshold:   {}", t(self.delay(Perbill::from_percent(90))));
			println!("   75% threshold:   {}", t(self.delay(Perbill::from_percent(75))));
			println!("   60% threshold:   {}", t(self.delay(Perbill::from_percent(60))));
		}
	}

	/// Determine the `y` value for the given `x` value.
	pub(crate) fn threshold(&self, x: Perbill) -> Perbill {
		match self {
			Self::LinearDecreasing { begin, delta } => *begin - (*delta * x).min(*begin),
			Self::SteppedDecreasing { begin, end, step, period } =>
				(*begin - (step.int_mul(x.int_div(*period))).min(*begin)).max(*end),
			Self::SimpleReciprocal { factor, offset } => {
				// Actual curve is y = factor / (x + x_offset) + offset
				// we want to avoid saturating prior to the division.
				Perbill::from_rational(factor.deconstruct(), x.deconstruct()).saturating_add(*offset)
			}
			Self::Reciprocal { factor, offset } => {
				let x_offset = factor.saturating_div(offset.left_from_one(), Down);
				// Actual curve is y = factor / (x + x_offset) + offset
				// we want to avoid saturating prior to the division.
				Perbill::from_rational(factor.deconstruct(), x.deconstruct() + x_offset.deconstruct())
					.saturating_add(*offset)
			}
			Self::TranslatedReciprocal { factor, x_offset, y_offset } => {
				factor.checked_rounding_div(FixedI64::from(x) + *x_offset, Down)
					.map(|yp| (yp + *y_offset).into_clamped_perthing())
					.unwrap_or_else(Perbill::one)
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
					period.int_mul((*begin - y.min(*begin) + step.less_epsilon()).int_div(*step))
				},
			Self::SimpleReciprocal { factor, offset } => {
				// Actual curve is y = factor / x + offset
				// Ergo curve is x = factor / (y - offset)
				if y < *offset {
					Perbill::one()
				} else {
					factor.saturating_div(y - *offset, Up)
				}
			},
			Self::Reciprocal { factor, offset } => {
				let x_offset = factor.saturating_div(offset.left_from_one(), Down);
				// Actual curve is y = factor / (x + x_offset) + y_offset
				// Ergo curve is x = factor / (y - offset) - x_offset
				// To avoid pre-saturation problems, we move the `x_offset` term to happen prior to
				// the division.
				// So:
				// yo := y - offset
				// x = (factor - x_offset * yo) / yo
				if y < *offset {
					Perbill::one()
				} else {
					let yo = y - *offset;
					factor.saturating_sub(x_offset * yo).saturating_div(yo, Up)
				}
			},
			Self::TranslatedReciprocal { factor, x_offset, y_offset } => {
				let y = FixedI64::from(y);
				let maybe_term = factor.checked_rounding_div(y - *y_offset, Up);
				maybe_term.and_then(|term| (term - *x_offset).try_into_perthing().ok())
					.unwrap_or_else(Perbill::one)
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
					"Linear[(0%, {:?}) -> (100%, {:?})]",
					begin,
					*begin - *delta,
				)
			},
			Self::SteppedDecreasing { begin, end, step, period } => {
				write!(
					f,
					"Stepped[(0%, {:?}) -> (100%, {:?}) by ({:?}, {:?})]",
					begin,
					end,
					period,
					step,
				)
			},
			Self::SimpleReciprocal { factor, offset } => {
				write!(
					f,
					"SimpleReciprocal[factor of {:?}, offset of {:?}]",
					factor,
					offset,
				)
			},
			Self::Reciprocal { factor, offset } => {
				write!(
					f,
					"Reciprocal[factor of {:?}, offset of {:?}]",
					factor,
					offset,
				)
			},
			Self::TranslatedReciprocal { factor, x_offset, y_offset } => {
				write!(
					f,
					"TranslatedReciprocal[factor of {:?}, x_offset of {:?}, y_offset of {:?}]",
					factor,
					x_offset,
					y_offset,
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
	#[should_panic]
	fn check_curves() {
//		Curve::reciprocal_from_point(7, 28u32, 0.1).info(28u32, "Tip");
		Curve::reciprocal_from_point_and_floor(1u32, 28, percent(65), percent(50)).info(28u32, "Tip");
		assert!(false);
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
	fn translated_reciprocal_works() {
		let c: Curve = Curve::TranslatedReciprocal {
			factor: FixedI64::from_float(0.03125),
			x_offset: FixedI64::from_float(0.0363306838226),
			y_offset: FixedI64::from_float(0.139845532427),
		};
		c.info(28u32, "Test");

		for i in 0..9_696_969u32 {
			let query = Perbill::from_rational(i, 9_696_969);
			// Determine the nearest point in time when the query will be above threshold.
			let delay_needed = c.delay(query);
			// Ensure that it actually does pass at that time, or that it will never pass.
			assert!(delay_needed.is_one() || c.passing(delay_needed, query));
		}
	}

	#[test]
	fn basic_reciprocal_works() {
		let c: Curve = Curve::Reciprocal {
			factor: percent(5),
			offset: percent(0),
		};

		for i in 0..9_696_969u32 {
			let query = Perbill::from_rational(i, 9_696_969);
			// Determine the nearest point in time when the query will be above threshold.
			let delay_needed = c.delay(query);
			// Ensure that it actually does pass at that time, or that it will never pass.
			assert!(delay_needed.is_one() || c.passing(delay_needed, query));
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

		for i in 0..9_696_969u32 {
			let query = Perbill::from_rational(i, 9_696_969);
			// Determine the nearest point in time when the query will be above threshold.
			let delay_needed = c.delay(query);
			// Ensure that it actually does pass at that time, or that it will never pass.
			assert!(delay_needed.is_one() || c.passing(delay_needed, query));
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
	fn realistic_offset_reciprocal_works() {
		let c: Curve = Curve::Reciprocal {
			factor: Perbill::from_rational(35u32, 10_000u32),
			offset: percent(10),
		};

		for i in 0..9_696_969u32 {
			let query = Perbill::from_rational(i, 9_696_969);
			// Determine the nearest point in time when the query will be above threshold.
			let delay_needed = c.delay(query);
			// Ensure that it actually does pass at that time, or that it will never pass.
			assert!(delay_needed.is_one() || c.passing(delay_needed, query));
		}
	}

	#[test]
	fn stepped_decreasing_works() {
		let c = Curve::SteppedDecreasing {
			begin: percent(80),
			end: percent(30),
			step: percent(10),
			period: percent(15),
		};

		for i in 0..9_696_969u32 {
			let query = Perbill::from_rational(i, 9_696_969);
			// Determine the nearest point in time when the query will be above threshold.
			let delay_needed = c.delay(query);
			// Ensure that it actually does pass at that time, or that it will never pass.
			assert!(delay_needed.is_one() || c.passing(delay_needed, query));
		}

		assert_eq!(c.threshold(percent(0)), percent(80));
		assert_eq!(c.threshold(percent(15).less_epsilon()), percent(80));
		assert_eq!(c.threshold(percent(15)), percent(70));
		assert_eq!(c.threshold(percent(30).less_epsilon()), percent(70));
		assert_eq!(c.threshold(percent(30)), percent(60));
		assert_eq!(c.threshold(percent(45).less_epsilon()), percent(60));
		assert_eq!(c.threshold(percent(45)), percent(50));
		assert_eq!(c.threshold(percent(60).less_epsilon()), percent(50));
		assert_eq!(c.threshold(percent(60)), percent(40));
		assert_eq!(c.threshold(percent(75).less_epsilon()), percent(40));
		assert_eq!(c.threshold(percent(75)), percent(30));
		assert_eq!(c.threshold(percent(100)), percent(30));

		assert_eq!(c.delay(percent(100)), percent(0));
		assert_eq!(c.delay(percent(80)), percent(0));
		assert_eq!(c.delay(percent(80).less_epsilon()), percent(15));
		assert_eq!(c.delay(percent(70)), percent(15));
		assert_eq!(c.delay(percent(70).less_epsilon()), percent(30));
		assert_eq!(c.delay(percent(60)), percent(30));
		assert_eq!(c.delay(percent(60).less_epsilon()), percent(45));
		assert_eq!(c.delay(percent(50)), percent(45));
		assert_eq!(c.delay(percent(50).less_epsilon()), percent(60));
		assert_eq!(c.delay(percent(40)), percent(60));
		assert_eq!(c.delay(percent(40).less_epsilon()), percent(75));
		assert_eq!(c.delay(percent(30)), percent(75));
		assert_eq!(c.delay(percent(30).less_epsilon()), percent(100));
		assert_eq!(c.delay(percent(0)), percent(100));
	}
}