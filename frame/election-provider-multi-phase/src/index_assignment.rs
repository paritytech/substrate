// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! The [`IndexAssignment`] type is an intermediate between the assignments list
//! ([`&[Assignment<T>]`][Assignment]) and [`CompactOf<T>`][crate::CompactOf].

use crate::{CompactAccuracyOf, CompactVoterIndexOf, CompactTargetIndexOf};
use codec::{Encode, Decode};
use sp_arithmetic::PerThing;
use sp_core::RuntimeDebug;
use sp_npos_elections::{Error, IdentifierT};

/// A voter's fundamental data: their ID, their stake, and the list of candidates for whom they voted.
pub type Voter<T> = (
	<T as frame_system::Config>::AccountId,
	sp_npos_elections::VoteWeight,
	Vec<<T as frame_system::Config>::AccountId>,
);

/// The relative distribution of a voter's stake among the winning targets.
pub type Assignment<T> = sp_npos_elections::Assignment<
	<T as frame_system::Config>::AccountId,
	CompactAccuracyOf<T>,
>;

// The [`IndexAssignment`] type specialized for a particular runtime `T`.
pub type IndexAssignmentOf<T> = IndexAssignment<
	CompactVoterIndexOf<T>,
	CompactTargetIndexOf<T>,
	CompactAccuracyOf<T>,
>;

/// The [`IndexAssignment`] type is an intermediate between the assignments list
/// ([`&[Assignment<T>]`][Assignment]) and [`CompactOf<T>`][crate::CompactOf].
///
/// The voter and target identifiers have already been replaced with appropriate indices,
/// making it fast to repeatedly encode into a `CompactOf<T>`. This property turns out
/// to be important when trimming for compact length.
#[derive(RuntimeDebug, Clone, Default)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Encode, Decode))]
pub struct IndexAssignment<VoterIndex, TargetIndex, P: PerThing> {
	/// Index of the voter among the voters list.
	pub who: VoterIndex,
	/// The distribution of the voter's stake among winning targets.
	///
	/// Targets are identified by their index in the canonical list.
	pub distribution: Vec<(TargetIndex, P)>,
}

impl<VoterIndex, TargetIndex, P: PerThing> IndexAssignment<VoterIndex, TargetIndex, P> {
	pub fn new<AccountId: IdentifierT>(
		assignment: &sp_npos_elections::Assignment<AccountId, P>,
		voter_index: impl Fn(&AccountId) -> Option<VoterIndex>,
		target_index: impl Fn(&AccountId) -> Option<TargetIndex>,
	) -> Result<Self, Error> {
		use sp_npos_elections::__OrInvalidIndex as _;
		Ok(Self {
			who: voter_index(&assignment.who).or_invalid_index()?,
			distribution: assignment
				.distribution
				.iter()
				.map(|(target, proportion)| Some((target_index(target)?, proportion.clone())))
				.collect::<Option<Vec<_>>>()
				.or_invalid_index()?,
		})
	}
}
