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

//! Implement a data structure designed for the properties that:
//!
//! - It's efficient to insert or remove a voter
//! - It's efficient to iterate over the top* N voters by stake, where the precise ordering of
//!   voters doesn't particularly matter.

use crate::{
	slashing::SlashingSpans, AccountIdOf, Config, Nominations, Pallet, VotingDataOf, VoteWeight,
};
use codec::{Encode, Decode};
use frame_support::{DefaultNoBound, StorageMap, StorageValue, StorageDoubleMap};
use sp_runtime::SaturatedConversion;
use sp_std::marker::PhantomData;

/// Index type for a bag.
pub type BagIdx = u8;

/// Given a certain vote weight, which bag should this voter contain?
fn bag_for(weight: VoteWeight) -> BagIdx {
	todo!("geometric series of some description; ask alfonso")
}

/// Type of voter.
///
/// Similar to [`crate::StakerStatus`], but somewhat more limited.
#[derive(Clone, Copy, Encode, Decode, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum VoterType {
	Validator,
	Nominator,
}

/// Fundamental information about a voter.
#[derive(Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Voter<AccountId> {
	/// Account Id of this voter
	pub id: AccountId,
	/// Whether the voter is a validator or nominator
	pub voter_type: VoterType,
}

pub type VoterOf<T> = Voter<AccountIdOf<T>>;

/// Data structure providing efficient mostly-accurate selection of the top N voters by stake.
///
/// It's implemented as a set of linked lists. Each linked list comprises a bag of voters of
/// arbitrary and unbounded length, all having a vote weight within a particular constant range.
/// This structure means that voters can be added and removed in `O(1)` time.
///
/// Iteration is accomplished by chaining the iteration of each bag, from greatest to least.
/// While the users within any particular bag are sorted in an entirely arbitrary order, the overall
/// stake decreases as successive bags are reached. This means that it is valid to truncate
/// iteration at any desired point; only those voters in the lowest bag (who are known to have
/// relatively little power to affect the outcome) can be excluded. This satisfies both the desire
/// for fairness and the requirement for efficiency.
pub struct VoterList<AccountId>(PhantomData<AccountId>);

pub type VoterListOf<T> = VoterList<AccountIdOf<T>>;

/// A Bag contains a singly-linked list of voters.
///
/// Note that we maintain both head and tail pointers. While it would be possible to get away
/// with maintaining only a head pointer and cons-ing elements onto the front of the list, it's
/// more desirable to ensure that there is some element of first-come, first-serve to the list's
/// iteration so that there's no incentive to churn voter positioning to improve the chances of
/// appearing within the voter set.
#[derive(Default, Encode, Decode)]
pub struct Bag<AccountId> {
	head: Option<AccountId>,
	tail: Option<AccountId>,
}

pub type BagOf<T> = Bag<AccountIdOf<T>>;

/// A Node is the fundamental element comprising the singly-linked lists which for each bag.
#[derive(Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Node<AccountId> {
	voter: Voter<AccountId>,
	next: Option<AccountId>,
}

pub type NodeOf<T> = Node<AccountIdOf<T>>;
