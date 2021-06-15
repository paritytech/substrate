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
	AccountIdOf, Config, Nominations, Nominators, Pallet, VoteWeight, VoterBagFor, VotingDataOf,
	slashing::SlashingSpans,
};
use codec::{Encode, Decode};
use frame_support::DefaultNoBound;
use sp_runtime::SaturatedConversion;
use sp_std::{collections::btree_map::BTreeMap, marker::PhantomData};

/// Index type for a bag.
pub type BagIdx = u8;

/// How many bags there are
const N_BAGS: BagIdx = 200;

/// Given a certain vote weight, which bag should this voter contain?
///
/// Bags are separated by fixed thresholds. The formula for a threshold is, for `t` in `0..=N_BAGS`:
///
///   10 ^ ((t / 10) - 10)
///
/// Given `N_BAGS == 200`, this means that the lowest threshold is `10^-10`, and the highest is
/// `10^10`. A given vote weight always fits into the bag `t` such that `threshold(t-1) <= weight <
/// threshold(t)`. We can determine an appropriate value for `t` by binary search.
///
/// It is important for the correctness of the iteration algorithm that the bags of highest value
/// have the lowest threshold. Therefore, the appropriate `BagIdx` for a given value `T` is
/// `N_BAGS - t`.
fn notional_bag_for(weight: VoteWeight) -> BagIdx {
	// the input to this threshold function is _not_ reversed; `threshold(0) == 0`
	let threshold = |bag: BagIdx| -> u64 {
		// The goal is to segment the full range of `u64` into `N_BAGS`, such that `threshold(0) != 0`,
		// `threshold(N_BAGS) == u64::MAX`, and for all `t` in `0..N_BAGS`,
		// `threshold(t + 1) as f64 / threshold(t) as f64 == CONSTANT_RATIO`. For `N_BAGS == 200`,
		// `CONSTANT_RATIO ~= 1.25`.
		//
		// The natural, simple implementation here is
		//
		// ```rust
		// // float exp and ln are not constant functions, unfortunately
		// let CONSTANT_RATIO = ((u64::MAX as f64).ln() / (N_BAGS as f64)).exp();
		// CONSTANT_RATIO.powi(bag.into()).into()
		// ```
		//
		// Unfortunately, that doesn't quite work, for two reasons:
		//
		// - floats are nondeterministic and not allowed on the blockchain
		// - f64 has insufficient capacity to completely and accurately compute f64
		//
		// Perhaps the answer is going to end up being to bring in a fixed-point bignum implementation.
		// See: https://docs.rs/fixed/1.9.0/fixed/struct.FixedU128.html
		todo!()
	};

	// `want_bag` is the highest bag for which `threshold(want_bag) >= weight`
	let want_bag = {
		// TODO: use a binary search instead
		let mut t = N_BAGS;
		while t > 0 {
			if threshold(t) >= weight {
				break;
			}
			t -= 1;
		}
		t
	};

	debug_assert!(
		(0..=N_BAGS).contains(&want_bag),
		"must have computed a valid want_bag"
	);

	// reverse the index so that iteration works properly
	N_BAGS - want_bag
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
	/// Decode the length of the voter list.
	pub fn decode_len() -> Option<usize> {
		crate::VoterCount::<T>::try_get().ok().map(|n| n.saturated_into())
	}

	/// Iterate over all nodes in all bags in the voter list.
	///
	/// Note that this exhaustively attempts to try all possible bag indices. Full iteration can be
	/// expensive; it's recommended to limit the number of items with `.take(n)`.
	pub fn iter() -> impl Iterator<Item = Node<T>> {
		(0..=BagIdx::MAX).filter_map(|bag_idx| Bag::get(bag_idx)).flat_map(|bag| bag.iter())
	}

	/// Insert a new voter into the appropriate bag in the voter list.
	///
	/// If the voter is already present in the list, their type will be updated.
	/// That case is cheaper than inserting a new voter.
	pub fn insert_as(account_id: &AccountIdOf<T>, voter_type: VoterType) {
		// if this is an update operation we can complete this easily and cheaply
		if !Node::<T>::update_voter_type_for(account_id, voter_type) {
			// otherwise, we need to insert from scratch
			let weight_of = Pallet::<T>::slashable_balance_of_fn();
			let voter = Voter { id: account_id.clone(), voter_type };
			Self::insert(voter, weight_of);
		}
	}

	/// Insert a new voter into the appropriate bag in the voter list.
	pub fn insert(voter: VoterOf<T>, weight_of: impl Fn(&T::AccountId) -> VoteWeight) {
		Self::insert_many(sp_std::iter::once(voter), weight_of)
	}

	/// Insert several voters into the appropriate bags in the voter list.
	///
	/// This is more efficient than repeated calls to `Self::insert`.
	pub fn insert_many(
		voters: impl IntoIterator<Item = VoterOf<T>>,
		weight_of: impl Fn(&T::AccountId) -> VoteWeight,
	) {
		let mut bags = BTreeMap::new();
		let mut count = 0;

		for voter in voters.into_iter() {
			let weight = weight_of(&voter.id);
			let bag = notional_bag_for(weight);
			bags.entry(bag).or_insert_with(|| Bag::<T>::get_or_make(bag)).insert(voter);
			count += 1;
		}

		for (_, bag) in bags {
			bag.put();
		}

		crate::VoterCount::<T>::mutate(|prev_count| *prev_count = prev_count.saturating_add(count));
	}

	/// Remove a voter (by id) from the voter list.
	pub fn remove(voter: &AccountIdOf<T>) {
		Self::remove_many(sp_std::iter::once(voter))
	}

	/// Remove many voters (by id) from the voter list.
	///
	/// This is more efficient than repeated calls to `Self::remove`.
	pub fn remove_many<'a>(voters: impl IntoIterator<Item = &'a AccountIdOf<T>>) {
		let mut bags = BTreeMap::new();
		let mut count = 0;

		for voter_id in voters.into_iter() {
			let node = match Node::<T>::from_id(voter_id) {
				Some(node) => node,
				None => continue,
			};
			count += 1;

			// clear the bag head/tail pointers as necessary
			let bag = bags.entry(node.bag_idx).or_insert_with(|| Bag::<T>::get_or_make(node.bag_idx));
			bag.remove_node(&node);

			// now get rid of the node itself
			crate::VoterNodes::<T>::remove(node.bag_idx, voter_id);
			crate::VoterBagFor::<T>::remove(voter_id);
		}

		for (_, bag) in bags {
			bag.put();
		}

		crate::VoterCount::<T>::mutate(|prev_count| *prev_count = prev_count.saturating_sub(count));
	}

	/// Update a voter's position in the voter list.
	///
	/// If the voter was in the correct bag, no effect. If the voter was in the incorrect bag, they
	/// are moved into the correct bag.
	///
	/// Returns `true` if the voter moved.
	///
	/// This operation is somewhat more efficient than simply calling [`self.remove`] followed by
	/// [`self.insert`]. However, given large quantities of voters to move, it may be more efficient
	/// to call [`self.remove_many`] followed by [`self.insert_many`].
	pub fn update_position_for(
		mut node: Node<T>,
		weight_of: impl Fn(&AccountIdOf<T>) -> VoteWeight,
	) -> bool {
		let was_misplaced = node.is_misplaced(&weight_of);
		if was_misplaced {
			// clear the old bag head/tail pointers as necessary
			if let Some(mut bag) = Bag::<T>::get(node.bag_idx) {
				bag.remove_node(&node);
				bag.put();
			}

			// put the voter into the appropriate new bag
			node.bag_idx = notional_bag_for(weight_of(&node.voter.id));
			let mut bag = Bag::<T>::get_or_make(node.bag_idx);
			bag.insert_node(node);
			bag.put();
		}
		was_misplaced
	}
}

/// A Bag is a doubly-linked list of voters.
///
/// Note that we maintain both head and tail pointers. While it would be possible to get away
/// with maintaining only a head pointer and cons-ing elements onto the front of the list, it's
/// more desirable to ensure that there is some element of first-come, first-serve to the list's
/// iteration so that there's no incentive to churn voter positioning to improve the chances of
/// appearing within the voter set.
#[derive(DefaultNoBound, Encode, Decode)]
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

	/// Get a bag by idx or make it, appropriately initialized.
	pub fn get_or_make(bag_idx: BagIdx) -> Bag<T> {
		Self::get(bag_idx).unwrap_or(Bag { bag_idx, ..Default::default() })
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

	/// Insert a new voter into this bag.
	///
	/// This is private on purpose because it's naive: it doesn't check whether this is the
	/// appropriate bag for this voter at all. Generally, use [`VoterList::insert`] instead.
	///
	/// Storage note: this modifies storage, but only for the nodes. You still need to call
	/// `self.put()` after use.
	fn insert(&mut self, voter: VoterOf<T>) {
		self.insert_node(Node::<T> {
			voter,
			prev: None,
			next: None,
			bag_idx: self.bag_idx,
		});
	}

	/// Insert a voter node into this bag.
	///
	/// This is private on purpose because it's naive; it doesn't check whether this is the
	/// appropriate bag for this voter at all. Generally, use [`VoterList::insert`] instead.
	///
	/// Storage note: this modifies storage, but only for the node. You still need to call
	/// `self.put()` after use.
	fn insert_node(&mut self, mut node: Node<T>) {
		let id = node.voter.id.clone();

		node.prev = self.tail.clone();
		node.next = None;
		node.put();

		// update the previous tail
		if let Some(mut tail) = self.tail() {
			tail.next = Some(id.clone());
			tail.put();
		}

		// update the internal bag links
		if self.head.is_none() {
			self.head = Some(id.clone());
		}
		self.tail = Some(id.clone());

		crate::VoterBagFor::<T>::insert(id, self.bag_idx);
	}

	/// Remove a voter node from this bag.
	///
	/// This is private on purpose because it doesn't check whether this bag contains the voter in
	/// the first place. Generally, use [`VoterList::remove`] instead.
	///
	/// Storage note: this modifies storage, but only for adjacent nodes. You still need to call
	/// `self.put()` and `node.put()` after use.
	fn remove_node(&mut self, node: &Node<T>) {
		node.excise();

		// clear the bag head/tail pointers as necessary
		if self.head.as_ref() == Some(&node.voter.id) {
			self.head = node.next.clone();
		}
		if self.tail.as_ref() == Some(&node.voter.id) {
			self.tail = node.prev.clone();
		}
	}
}

/// A Node is the fundamental element comprising the doubly-linked lists which for each bag.
#[derive(Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Node<T: Config> {
	voter: Voter<AccountIdOf<T>>,
	prev: Option<AccountIdOf<T>>,
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

	/// Get the previous node in the bag.
	pub fn prev(&self) -> Option<Node<T>> {
		self.prev.as_ref().and_then(|id| self.in_bag(id))
	}

	/// Get the next node in the bag.
	pub fn next(&self) -> Option<Node<T>> {
		self.next.as_ref().and_then(|id| self.in_bag(id))
	}

	/// Get this voter's voting data.
	pub fn voting_data(
		&self,
		weight_of: impl Fn(&T::AccountId) -> VoteWeight,
		slashing_spans: &BTreeMap<AccountIdOf<T>, SlashingSpans>,
	) -> Option<VotingDataOf<T>> {
		match self.voter.voter_type {
			VoterType::Validator => Some((
				self.voter.id.clone(),
				weight_of(&self.voter.id),
				vec![self.voter.id.clone()],
			)),
			VoterType::Nominator => {
				let Nominations { submitted_in, mut targets, .. } =
					Nominators::<T>::get(self.voter.id.clone())?;
				// Filter out nomination targets which were nominated before the most recent
				// slashing span.
				targets.retain(|stash| {
					slashing_spans
						.get(stash)
						.map_or(true, |spans| submitted_in >= spans.last_nonzero_slash())
				});

				(!targets.is_empty())
					.then(move || (self.voter.id.clone(), weight_of(&self.voter.id), targets))
			}
		}
	}

	/// Remove this node from the linked list.
	///
	/// Modifies storage, but only modifies the adjacent nodes. Does not modify `self` or any bag.
	fn excise(&self) {
		if let Some(mut prev) = self.prev() {
			prev.next = self.next.clone();
			prev.put();
		}
		if let Some(mut next) = self.next() {
			next.prev = self.prev.clone();
			next.put();
		}
	}

	/// `true` when this voter is in the wrong bag.
	pub fn is_misplaced(&self, weight_of: impl Fn(&T::AccountId) -> VoteWeight) -> bool {
		notional_bag_for(weight_of(&self.voter.id)) != self.bag_idx
	}

	/// Update the voter type associated with a particular node by id.
	///
	/// This updates storage immediately.
	///
	/// Returns whether the voter existed and was successfully updated.
	pub fn update_voter_type_for(account_id: &AccountIdOf<T>, voter_type: VoterType) -> bool {
		let node = Self::from_id(account_id);
		let existed = node.is_some();
		if let Some(mut node) = node {
			node.voter.voter_type = voter_type;
			node.put();
		}
		existed
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
