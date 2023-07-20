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

//! Traits and associated data structures concerned with voting, and moving between tokens and
//! votes.

use crate::dispatch::{DispatchError, Parameter};
use codec::{HasCompact, MaxEncodedLen};
use sp_arithmetic::Perbill;
use sp_runtime::traits::Member;
use sp_std::prelude::*;

pub trait VoteTally<Votes, Class> {
	fn new(_: Class) -> Self;
	fn ayes(&self, class: Class) -> Votes;
	fn support(&self, class: Class) -> Perbill;
	fn approval(&self, class: Class) -> Perbill;
	#[cfg(feature = "runtime-benchmarks")]
	fn unanimity(class: Class) -> Self;
	#[cfg(feature = "runtime-benchmarks")]
	fn rejection(class: Class) -> Self;
	#[cfg(feature = "runtime-benchmarks")]
	fn from_requirements(support: Perbill, approval: Perbill, class: Class) -> Self;
	#[cfg(feature = "runtime-benchmarks")]
	/// A function that should be called before any use of the `runtime-benchmarks` gated functions
	/// of the `VoteTally` trait.
	///
	/// Should be used to set up any needed state in a Pallet which implements `VoteTally` so that
	/// benchmarks that execute will complete successfully. `class` can be used to set up a
	/// particular class of voters, and `granularity` is used to determine the weight of one vote
	/// relative to total unanimity.
	///
	/// For example, in the case where there are a number of unique voters, and each voter has equal
	/// voting weight, a granularity of `Perbill::from_rational(1, 1000)` should create `1_000`
	/// users.
	fn setup(class: Class, granularity: Perbill);
}
pub enum PollStatus<Tally, Moment, Class> {
	None,
	Ongoing(Tally, Class),
	Completed(Moment, bool),
}

impl<Tally, Moment, Class> PollStatus<Tally, Moment, Class> {
	pub fn ensure_ongoing(self) -> Option<(Tally, Class)> {
		match self {
			Self::Ongoing(t, c) => Some((t, c)),
			_ => None,
		}
	}
}

pub struct ClassCountOf<P, T>(sp_std::marker::PhantomData<(P, T)>);
impl<T, P: Polling<T>> sp_runtime::traits::Get<u32> for ClassCountOf<P, T> {
	fn get() -> u32 {
		P::classes().len() as u32
	}
}

pub trait Polling<Tally> {
	type Index: Parameter + Member + Ord + PartialOrd + Copy + HasCompact + MaxEncodedLen;
	type Votes: Parameter + Member + Ord + PartialOrd + Copy + HasCompact + MaxEncodedLen;
	type Class: Parameter + Member + Ord + PartialOrd + MaxEncodedLen;
	type Moment;

	/// Provides a vec of values that `T` may take.
	fn classes() -> Vec<Self::Class>;

	/// `Some` if the referendum `index` can be voted on, along with the tally and class of
	/// referendum.
	///
	/// Don't use this if you might mutate - use `try_access_poll` instead.
	fn as_ongoing(index: Self::Index) -> Option<(Tally, Self::Class)>;

	fn access_poll<R>(
		index: Self::Index,
		f: impl FnOnce(PollStatus<&mut Tally, Self::Moment, Self::Class>) -> R,
	) -> R;

	fn try_access_poll<R>(
		index: Self::Index,
		f: impl FnOnce(PollStatus<&mut Tally, Self::Moment, Self::Class>) -> Result<R, DispatchError>,
	) -> Result<R, DispatchError>;

	/// Create an ongoing majority-carries poll of given class lasting given period for the purpose
	/// of benchmarking.
	///
	/// May return `Err` if it is impossible.
	#[cfg(feature = "runtime-benchmarks")]
	fn create_ongoing(class: Self::Class) -> Result<Self::Index, ()>;

	/// End the given ongoing poll and return the result.
	///
	/// Returns `Err` if `index` is not an ongoing poll.
	#[cfg(feature = "runtime-benchmarks")]
	fn end_ongoing(index: Self::Index, approved: bool) -> Result<(), ()>;

	/// The maximum amount of ongoing polls within any single class. By default it practically
	/// unlimited (`u32::max_value()`).
	#[cfg(feature = "runtime-benchmarks")]
	fn max_ongoing() -> (Self::Class, u32) {
		(Self::classes().into_iter().next().expect("Always one class"), u32::max_value())
	}
}
