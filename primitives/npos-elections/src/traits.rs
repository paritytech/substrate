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
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// distributed under the License is distributed on an "AS IS" BASIS,
// See the License for the specific language governing permissions and
// limitations under the License.

//! Traits for the npos-election operations.

use crate::{
	Assignment, ElectionScore, Error, EvaluateSupport, ExtendedBalance, IndexAssignmentOf,
	VoteWeight,
};
use codec::Encode;
use scale_info::TypeInfo;
use sp_arithmetic::{
	traits::{Bounded, UniqueSaturatedInto},
	PerThing,
};
use sp_std::{
	convert::{TryFrom, TryInto},
	fmt::Debug,
	ops::Mul,
	prelude::*,
};

/// an aggregator trait for a generic type of a voter/target identifier. This usually maps to
/// substrate's account id.
pub trait IdentifierT: Clone + Eq + Default + Ord + Debug + codec::Codec {}
impl<T: Clone + Eq + Default + Ord + Debug + codec::Codec> IdentifierT for T {}

/// Aggregator trait for a PerThing that can be multiplied by u128 (ExtendedBalance).
pub trait PerThing128: PerThing + Mul<ExtendedBalance, Output = ExtendedBalance> {}
impl<T: PerThing + Mul<ExtendedBalance, Output = ExtendedBalance>> PerThing128 for T {}

/// Simple Extension trait to easily convert `None` from index closures to `Err`.
///
/// This is only generated and re-exported for the solution code to use.
#[doc(hidden)]
pub trait __OrInvalidIndex<T> {
	fn or_invalid_index(self) -> Result<T, Error>;
}

impl<T> __OrInvalidIndex<T> for Option<T> {
	fn or_invalid_index(self) -> Result<T, Error> {
		self.ok_or(Error::SolutionInvalidIndex)
	}
}

/// An opaque index-based, NPoS solution type.
pub trait NposSolution
where
	Self: Sized + for<'a> sp_std::convert::TryFrom<&'a [IndexAssignmentOf<Self>], Error = Error>,
{
	/// The maximum number of votes that are allowed.
	const LIMIT: usize;

	/// The voter type. Needs to be an index (convert to usize).
	type VoterIndex: UniqueSaturatedInto<usize>
		+ TryInto<usize>
		+ TryFrom<usize>
		+ Debug
		+ Copy
		+ Clone
		+ Bounded
		+ Encode
		+ TypeInfo;

	/// The target type. Needs to be an index (convert to usize).
	type TargetIndex: UniqueSaturatedInto<usize>
		+ TryInto<usize>
		+ TryFrom<usize>
		+ Debug
		+ Copy
		+ Clone
		+ Bounded
		+ Encode
		+ TypeInfo;

	/// The weight/accuracy type of each vote.
	type Accuracy: PerThing128;

	/// Get the length of all the voters that this type is encoding.
	///
	/// This is basically the same as the number of assignments, or number of active voters.
	fn voter_count(&self) -> usize;

	/// Get the total count of edges.
	///
	/// This is effectively in the range of {[`Self::voter_count`], [`Self::voter_count`] *
	/// [`Self::LIMIT`]}.
	fn edge_count(&self) -> usize;

	/// Get the number of unique targets in the whole struct.
	///
	/// Once presented with a list of winners, this set and the set of winners must be
	/// equal.
	fn unique_targets(&self) -> Vec<Self::TargetIndex>;

	/// Get the average edge count.
	fn average_edge_count(&self) -> usize {
		self.edge_count().checked_div(self.voter_count()).unwrap_or(0)
	}

	/// Compute the score of this solution type.
	fn score<A, FS>(
		self,
		stake_of: FS,
		voter_at: impl Fn(Self::VoterIndex) -> Option<A>,
		target_at: impl Fn(Self::TargetIndex) -> Option<A>,
	) -> Result<ElectionScore, Error>
	where
		for<'r> FS: Fn(&'r A) -> VoteWeight,
		A: IdentifierT,
	{
		let ratio = self.into_assignment(voter_at, target_at)?;
		let staked = crate::helpers::assignment_ratio_to_staked_normalized(ratio, stake_of)?;
		let supports = crate::to_supports(&staked);
		Ok(supports.evaluate())
	}

	/// Remove a certain voter.
	///
	/// This will only search until the first instance of `to_remove`, and return true. If
	/// no instance is found (no-op), then it returns false.
	///
	/// In other words, if this return true, exactly **one** element must have been removed self.
	fn remove_voter(&mut self, to_remove: Self::VoterIndex) -> bool;

	/// Build self from a list of assignments.
	fn from_assignment<FV, FT, A>(
		assignments: &[Assignment<A, Self::Accuracy>],
		voter_index: FV,
		target_index: FT,
	) -> Result<Self, Error>
	where
		A: IdentifierT,
		for<'r> FV: Fn(&'r A) -> Option<Self::VoterIndex>,
		for<'r> FT: Fn(&'r A) -> Option<Self::TargetIndex>;

	/// Convert self into a `Vec<Assignment<A, Self::Accuracy>>`
	fn into_assignment<A: IdentifierT>(
		self,
		voter_at: impl Fn(Self::VoterIndex) -> Option<A>,
		target_at: impl Fn(Self::TargetIndex) -> Option<A>,
	) -> Result<Vec<Assignment<A, Self::Accuracy>>, Error>;
}
