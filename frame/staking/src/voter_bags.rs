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
	slashing::SlashingSpans, AccountIdOf, Config, Nominations, Pallet, VoterBagFor, VotingDataOf, VoteWeight,
};
use codec::{Encode, Decode};
use frame_support::{DefaultNoBound, StorageMap, StorageValue, StorageDoubleMap};
use sp_runtime::SaturatedConversion;
use sp_std::marker::PhantomData;

/// Index type for a bag.
pub type BagIdx = u8;

/// Given a certain vote weight, which bag should this voter contain?
fn notional_bag_for(weight: VoteWeight) -> BagIdx {
	todo!("geometric series of some description; ask alfonso")
}

/// Find the actual bag containing the current voter.
fn current_bag_for<T: Config>(id: &AccountIdOf<T>) -> Option<BagIdx> {
	VoterBagFor::<T>::try_get(id).ok()
}

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
pub struct VoterList<T: Config>(PhantomData<T>);

impl<T: Config> VoterList<T> {
	pub fn decode_len() -> Option<usize> {
		crate::VoterCount::try_get().ok().map(|n| n.saturated_into())
	}

	/// Iterate over all nodes in all bags in the voter list.
	///
	/// Note that this exhaustively attempts to try all possible bag indices. Full iteration can be
	/// expensive; it's recommended to limit the number of items with `.take(n)`.
	pub fn iter() -> impl Iterator<Item = Node<T>> {
		(0..=BagIdx::MAX).filter_map(|bag_idx| Bag::get(bag_idx)).flat_map(|bag| bag.iter())
	}
}

/// A Bag contains a singly-linked list of voters.
///
/// Note that we maintain both head and tail pointers. While it would be possible to get away
/// with maintaining only a head pointer and cons-ing elements onto the front of the list, it's
/// more desirable to ensure that there is some element of first-come, first-serve to the list's
/// iteration so that there's no incentive to churn voter positioning to improve the chances of
/// appearing within the voter set.
#[derive(Default, Encode, Decode)]
pub struct Bag<T: Config> {
	head: Option<AccountIdOf<T>>,
	tail: Option<AccountIdOf<T>>,

	#[codec(skip)]
	bag_idx: BagIdx,
}

impl<T: Config> Bag<T> {
	/// Get a bag by idx.
	pub fn get(bag_idx: BagIdx) -> Option<Bag<T>> {
		crate::VoterBags::<T>::try_get(bag_idx).ok().map(|mut bag| {
			bag.bag_idx = bag_idx;
			bag
		})
	}

	/// Put the bag back into storage.
	pub fn put(self) {
		crate::VoterBags::<T>::insert(self.bag_idx, self);
	}

	/// Get the head node in this bag.
	pub fn head(&self) -> Option<Node<T>> {
		self.head.as_ref().and_then(|id| Node::get(self.bag_idx, id))
	}

	/// Get the tail node in this bag.
	pub fn tail(&self) -> Option<Node<T>> {
		self.tail.as_ref().and_then(|id| Node::get(self.bag_idx, id))
	}

	/// Iterate over the nodes in this bag.
	pub fn iter(&self) -> impl Iterator<Item = Node<T>> {
		sp_std::iter::successors(self.head(), |prev| prev.next())
	}
}

/// A Node is the fundamental element comprising the singly-linked lists which for each bag.
#[derive(Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Node<T: Config> {
	voter: Voter<AccountIdOf<T>>,
	next: Option<AccountIdOf<T>>,

	#[codec(skip)]
	bag_idx: BagIdx,
}

impl<T: Config> Node<T> {
	/// Get a node by bag idx and account id.
	pub fn get(bag_idx: BagIdx, account_id: &AccountIdOf<T>) -> Option<Node<T>> {
		crate::VoterNodes::<T>::try_get(&bag_idx, account_id).ok().map(|mut node| {
			node.bag_idx = bag_idx;
			node
		})
	}

	/// Get a node by account id.
	///
	/// Note that this must perform two storage lookups: one to identify which bag is appropriate,
	/// and another to actually fetch the node.
	pub fn from_id(account_id: &AccountIdOf<T>) -> Option<Node<T>> {
		let bag = current_bag_for::<T>(account_id)?;
		Self::get(bag, account_id)
	}

	/// Get a node by account id, assuming it's in the same bag as this node.
	pub fn in_bag(&self, account_id: &AccountIdOf<T>) -> Option<Node<T>> {
		Self::get(self.bag_idx, account_id)
	}

	/// Put the node back into storage.
	pub fn put(self) {
		crate::VoterNodes::<T>::insert(self.bag_idx, self.voter.id.clone(), self);
	}

	/// Get the next node in the bag.
	pub fn next(&self) -> Option<Node<T>> {
		self.next.as_ref().and_then(|id| self.in_bag(id))
	}
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

/// Type of voter.
///
/// Similar to [`crate::StakerStatus`], but somewhat more limited.
#[derive(Clone, Copy, Encode, Decode, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum VoterType {
	Validator,
	Nominator,
}
