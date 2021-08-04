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

//! Basic implementation of a doubly-linked list

use crate::Config;
use codec::{Decode, Encode};
use frame_election_provider_support::{VoteWeight, VoteWeightProvider};
use frame_support::{traits::Get, DefaultNoBound};
use sp_std::{
	boxed::Box,
	collections::{btree_map::BTreeMap, btree_set::BTreeSet},
	iter,
	marker::PhantomData,
};

#[cfg(test)]
mod tests;

/// Given a certain vote weight, which bag should contain this voter?
///
/// Bags are identified by their upper threshold; the value returned by this function is guaranteed
/// to be a member of `T::BagThresholds`.
///
/// This is used instead of a simpler scheme, such as the index within `T::BagThresholds`,
/// because in the event that bags are inserted or deleted, the number of affected voters which need
/// to be migrated is smaller.
///
/// Note that even if the thresholds list does not have `VoteWeight::MAX` as its final member, this
/// function behaves as if it does.
fn notional_bag_for<T: Config>(weight: VoteWeight) -> VoteWeight {
	let thresholds = T::BagThresholds::get();
	let idx = thresholds.partition_point(|&threshold| weight > threshold);
	thresholds.get(idx).copied().unwrap_or(VoteWeight::MAX)
}

/// Find the upper threshold of the actual bag containing the current voter.
fn current_bag_for<T: Config>(id: &T::AccountId) -> Option<VoteWeight> {
	crate::VoterBagFor::<T>::try_get(id).ok()
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
pub struct List<T: Config>(PhantomData<T>);

impl<T: Config> List<T> {
	/// Remove all data associated with the voter list from storage.
	pub fn clear() {
		crate::CounterForVoters::<T>::kill();
		crate::VoterBagFor::<T>::remove_all(None);
		crate::VoterBags::<T>::remove_all(None);
		crate::VoterNodes::<T>::remove_all(None);
	}

	/// Migrate the voter list from one set of thresholds to another.
	///
	/// This should only be called as part of an intentional migration; it's fairly expensive.
	///
	/// Returns the number of accounts affected.
	///
	/// Preconditions:
	///
	/// - `old_thresholds` is the previous list of thresholds.
	/// - All `bag_upper` currently in storage are members of `old_thresholds`.
	/// - `T::BagThresholds` has already been updated.
	///
	/// Postconditions:
	///
	/// - All `bag_upper` currently in storage are members of `T::BagThresholds`.
	/// - No voter is changed unless required to by the difference between the old threshold list
	///   and the new.
	/// - Voters whose bags change at all are implicitly rebagged into the appropriate bag in the
	///   new threshold set.
	#[allow(dead_code)]
	pub fn migrate(old_thresholds: &[VoteWeight]) -> u32 {
		// we can't check all preconditions, but we can check one
		debug_assert!(
			crate::VoterBags::<T>::iter().all(|(threshold, _)| old_thresholds.contains(&threshold)),
			"not all `bag_upper` currently in storage are members of `old_thresholds`",
		);

		let old_set: BTreeSet<_> = old_thresholds.iter().copied().collect();
		let new_set: BTreeSet<_> = T::BagThresholds::get().iter().copied().collect();

		let mut affected_accounts = BTreeSet::new();
		let mut affected_old_bags = BTreeSet::new();

		// a new bag means that all accounts previously using the old bag's threshold must now
		// be rebagged
		for inserted_bag in new_set.difference(&old_set).copied() {
			let affected_bag = notional_bag_for::<T>(inserted_bag);
			if !affected_old_bags.insert(affected_bag) {
				// If the previous threshold list was [10, 20], and we insert [3, 5], then there's
				// no point iterating through bag 10 twice.
				continue;
			}

			if let Some(bag) = Bag::<T>::get(affected_bag) {
				affected_accounts.extend(bag.iter().map(|node| node.id));
			}
		}

		// a removed bag means that all members of that bag must be rebagged
		for removed_bag in old_set.difference(&new_set).copied() {
			if !affected_old_bags.insert(removed_bag) {
				continue;
			}

			if let Some(bag) = Bag::<T>::get(removed_bag) {
				affected_accounts.extend(bag.iter().map(|node| node.id));
			}
		}

		// migrate the
		let weight_of = T::VoteWeightProvider::vote_weight;
		Self::remove_many(affected_accounts.iter().map(|voter| voter));
		let num_affected = affected_accounts.len() as u32;
		Self::insert_many(affected_accounts.into_iter(), weight_of);

		// we couldn't previously remove the old bags because both insertion and removal assume that
		// it's always safe to add a bag if it's not present. Now that that's sorted, we can get rid
		// of them.
		//
		// it's pretty cheap to iterate this again, because both sets are in-memory and require no
		// lookups.
		for removed_bag in old_set.difference(&new_set).copied() {
			debug_assert!(
				!crate::VoterBagFor::<T>::iter().any(|(_voter, bag)| bag == removed_bag),
				"no voter should be present in a removed bag",
			);
			crate::VoterBags::<T>::remove(removed_bag);
		}

		debug_assert!(
			{
				let thresholds = T::BagThresholds::get();
				crate::VoterBags::<T>::iter().all(|(threshold, _)| thresholds.contains(&threshold))
			},
			"all `bag_upper` in storage must be members of the new thresholds",
		);

		num_affected
	}

	/// Regenerate voter data from the `Nominators` and `Validators` storage items.
	///
	/// This is expensive and should only ever be performed during a migration, never during
	/// consensus.
	///
	/// Returns the number of voters migrated.
	#[allow(dead_code)]
	pub fn regenerate(
		all: impl IntoIterator<Item = T::AccountId>,
		weight_of: Box<dyn Fn(&T::AccountId) -> VoteWeight>,
	) {
		Self::clear();
		Self::insert_many(all, weight_of);
	}

	/// Iterate over all nodes in all bags in the voter list.
	///
	/// Full iteration can be expensive; it's recommended to limit the number of items with
	/// `.take(n)`.
	pub fn iter() -> impl Iterator<Item = Node<T>> {
		// We need a touch of special handling here: because we permit `T::BagThresholds` to
		// omit the final bound, we need to ensure that we explicitly include that threshold in the
		// list.
		//
		// It's important to retain the ability to omit the final bound because it makes tests much
		// easier; they can just configure `type BagThresholds = ()`.
		let thresholds = T::BagThresholds::get();
		let iter = thresholds.iter().copied();
		let iter: Box<dyn Iterator<Item = u64>> = if thresholds.last() == Some(&VoteWeight::MAX) {
			// in the event that they included it, we can just pass the iterator through unchanged.
			Box::new(iter.rev())
		} else {
			// otherwise, insert it here.
			Box::new(iter.chain(iter::once(VoteWeight::MAX)).rev())
		};
		iter.filter_map(Bag::get).flat_map(|bag| bag.iter())
	}

	/// Insert several voters into the appropriate bags in the voter list.
	///
	/// This is more efficient than repeated calls to `Self::insert`.
	fn insert_many(
		voters: impl IntoIterator<Item = T::AccountId>,
		weight_of: impl Fn(&T::AccountId) -> VoteWeight,
	) {
		voters.into_iter().for_each(|v| {
			let weight = weight_of(&v);
			Self::insert(v, weight);
		});
	}

	/// Insert a new voter into the appropriate bag in the voter list.
	// WARNING: This does not check if the inserted AccountId is duplicate with others in any bag.
	pub(crate) fn insert(voter: T::AccountId, weight: VoteWeight) {
		// TODO: can check if this voter exists as a node by checking if `voter` exists in the nodes
		// map and return early if it does.

		let bag_weight = notional_bag_for::<T>(weight);
		crate::log!(
			debug,
			"inserting {:?} with weight {} into bag {:?}",
			voter,
			weight,
			bag_weight
		);
		let mut bag = Bag::<T>::get_or_make(bag_weight);
		bag.insert(voter);

		// TODO: why are we writing to the bag of the voter is neither head or tail????
		bag.put();

		crate::CounterForVoters::<T>::mutate(|prev_count| {
			*prev_count = prev_count.saturating_add(1)
		});
	}

	/// Remove a voter (by id) from the voter list.
	pub fn remove(voter: &T::AccountId) {
		Self::remove_many(sp_std::iter::once(voter));
	}

	/// Remove many voters (by id) from the voter list.
	///
	/// This is more efficient than repeated calls to `Self::remove`.
	pub fn remove_many<'a>(voters: impl IntoIterator<Item = &'a T::AccountId>) {
		let mut bags = BTreeMap::new();
		let mut count = 0;

		for voter_id in voters.into_iter() {
			let node = match Node::<T>::from_id(voter_id) {
				Some(node) => node,
				None => continue,
			};
			count += 1;

			// clear the bag head/tail pointers as necessary
			let bag = bags
				.entry(node.bag_upper)
				.or_insert_with(|| Bag::<T>::get_or_make(node.bag_upper));
			bag.remove_node(&node);

			// now get rid of the node itself
			crate::VoterNodes::<T>::remove(voter_id);
			crate::VoterBagFor::<T>::remove(voter_id);
		}

		for (_, bag) in bags {
			bag.put();
		}

		crate::CounterForVoters::<T>::mutate(|prev_count| {
			*prev_count = prev_count.saturating_sub(count)
		});
	}

	/// Update a voter's position in the voter list.
	///
	/// If the voter was in the correct bag, no effect. If the voter was in the incorrect bag, they
	/// are moved into the correct bag.
	///
	/// Returns `Some((old_idx, new_idx))` if the voter moved, otherwise `None`.
	///
	/// This operation is somewhat more efficient than simply calling [`self.remove`] followed by
	/// [`self.insert`]. However, given large quantities of voters to move, it may be more efficient
	/// to call [`self.remove_many`] followed by [`self.insert_many`].
	pub fn update_position_for(
		mut node: Node<T>,
		new_weight: VoteWeight,
	) -> Option<(VoteWeight, VoteWeight)> {
		node.is_misplaced(new_weight).then(move || {
			let old_idx = node.bag_upper;

			// TODO: there should be a way to move a non-head-tail node to another bag
			// with just 1 bag read of the destination bag and zero writes
			// https://github.com/paritytech/substrate/pull/9468/files/83289aa4a15d61e6cb334f9d7e7f6804cb7e3537..44875c511ebdc79270100720320c8e3d2d56eb4a#r680559166

			// clear the old bag head/tail pointers as necessary
			if let Some(mut bag) = Bag::<T>::get(node.bag_upper) {
				bag.remove_node(&node);
				bag.put();
			} else {
				crate::log!(
					error,
					"Node for voter {:?} did not have a bag; VoterBags is in an inconsistent state",
					node.id,
				);
				debug_assert!(false, "every node must have an extant bag associated with it");
			}

			// put the voter into the appropriate new bag
			let new_idx = notional_bag_for::<T>(new_weight);
			node.bag_upper = new_idx;
			let mut bag = Bag::<T>::get_or_make(node.bag_upper);
			bag.insert_node(node);
			bag.put();

			(old_idx, new_idx)
		})
	}

	/// Sanity check the voter list.
	///
	/// This should be called from the call-site, whenever one of the mutating apis (e.g. `insert`)
	/// is being used, after all other staking data (such as counter) has been updated. It checks
	/// that:
	///
	/// * Iterate all voters in list and make sure there are no duplicates.
	/// * Iterate all voters and ensure their count is in sync with `CounterForVoters`.
	/// * Sanity-checks all bags. This will cascade down all the checks and makes sure all bags are
	///   checked per *any* update to `List`.
	pub(crate) fn sanity_check() -> Result<(), String> {
		use frame_support::ensure;
		let mut seen_in_list = BTreeSet::new();
		ensure!(
			Self::iter().map(|node| node.id).all(|voter| seen_in_list.insert(voter)),
			"duplicate identified",
		);

		let iter_count = Self::iter().collect::<sp_std::vec::Vec<_>>().len() as u32;
		let stored_count = crate::CounterForVoters::<T>::get();
		ensure!(
			iter_count == stored_count,
			format!("iter_count {} != stored_count {}", iter_count, stored_count)
		);

		let _ = T::BagThresholds::get()
			.into_iter()
			.map(|t| Bag::<T>::get(*t).unwrap_or_default())
			.map(|b| b.sanity_check())
			.collect::<Result<_, _>>()?;

		Ok(())
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
#[cfg_attr(feature = "std", derive(frame_support::DebugNoBound))]
#[cfg_attr(test, derive(PartialEq))]
pub struct Bag<T: Config> {
	head: Option<T::AccountId>,
	tail: Option<T::AccountId>,

	#[codec(skip)]
	bag_upper: VoteWeight,
}

impl<T: Config> Bag<T> {
	#[cfg(test)]
	pub(crate) fn new(
		head: Option<T::AccountId>,
		tail: Option<T::AccountId>,
		bag_upper: VoteWeight,
	) -> Self {
		Self { head, tail, bag_upper }
	}

	/// Get a bag by its upper vote weight.
	pub(crate) fn get(bag_upper: VoteWeight) -> Option<Bag<T>> {
		debug_assert!(
			T::BagThresholds::get().contains(&bag_upper) || bag_upper == VoteWeight::MAX,
			"it is a logic error to attempt to get a bag which is not in the thresholds list"
		);
		crate::VoterBags::<T>::try_get(bag_upper).ok().map(|mut bag| {
			bag.bag_upper = bag_upper;
			bag
		})
	}

	/// Get a bag by its upper vote weight or make it, appropriately initialized.
	fn get_or_make(bag_upper: VoteWeight) -> Bag<T> {
		debug_assert!(
			T::BagThresholds::get().contains(&bag_upper) || bag_upper == VoteWeight::MAX,
			"it is a logic error to attempt to get a bag which is not in the thresholds list"
		);
		Self::get(bag_upper).unwrap_or(Bag { bag_upper, ..Default::default() })
	}

	/// `True` if self is empty.
	fn is_empty(&self) -> bool {
		self.head.is_none() && self.tail.is_none()
	}

	/// Put the bag back into storage.
	fn put(self) {
		if self.is_empty() {
			crate::VoterBags::<T>::remove(self.bag_upper);
		} else {
			crate::VoterBags::<T>::insert(self.bag_upper, self);
		}
	}

	/// Get the head node in this bag.
	fn head(&self) -> Option<Node<T>> {
		self.head.as_ref().and_then(|id| Node::get(self.bag_upper, id))
	}

	/// Get the tail node in this bag.
	fn tail(&self) -> Option<Node<T>> {
		self.tail.as_ref().and_then(|id| Node::get(self.bag_upper, id))
	}

	/// Iterate over the nodes in this bag.
	pub(crate) fn iter(&self) -> impl Iterator<Item = Node<T>> {
		sp_std::iter::successors(self.head(), |prev| prev.next())
	}

	/// Insert a new voter into this bag.
	///
	/// This is private on purpose because it's naive: it doesn't check whether this is the
	/// appropriate bag for this voter at all. Generally, use [`List::insert`] instead.
	///
	/// Storage note: this modifies storage, but only for the nodes. You still need to call
	/// `self.put()` after use.
	fn insert(&mut self, id: T::AccountId) {
		self.insert_node(Node::<T> { id, prev: None, next: None, bag_upper: self.bag_upper });
	}

	/// Insert a voter node into this bag.
	///
	/// This is private on purpose because it's naive; it doesn't check whether this is the
	/// appropriate bag for this voter at all. Generally, use [`List::insert`] instead.
	///
	/// Storage note: this modifies storage, but only for the node. You still need to call
	/// `self.put()` after use.
	fn insert_node(&mut self, mut node: Node<T>) {
		if let Some(tail) = &self.tail {
			if *tail == node.id {
				// DOCUMENT_ME
				// this should never happen, but this check prevents a worst case infinite loop
				debug_assert!(false, "system logic error: inserting a node who has the id of tail");
				crate::log!(warn, "system logic error: inserting a node who has the id of tail");
				return;
			};
		}

		// update this node now
		let id = node.id.clone();
		node.prev = self.tail.clone();
		node.next = None;
		node.put();

		// update the previous tail
		if let Some(mut old_tail) = self.tail() {
			old_tail.next = Some(id.clone());
			old_tail.put();
		}
		self.tail = Some(id.clone());

		// ensure head exist. This is typically only set when the length of the bag is just 1, i.e.
		// if this is the first insertion into the bag. In this case, both head and tail should
		// point to the same voter node.
		if self.head.is_none() {
			self.head = Some(id.clone());
			debug_assert!(self.iter().count() == 1);
		}

		// update the voter's bag index.
		crate::VoterBagFor::<T>::insert(id, self.bag_upper);
	}

	/// Remove a voter node from this bag.
	///
	/// This is private on purpose because it doesn't check whether this bag contains the voter in
	/// the first place. Generally, use [`List::remove`] instead.
	///
	/// Storage note: this modifies storage, but only for adjacent nodes. You still need to call
	/// `self.put()`, `VoterNodes::remove(voter_id)` and `VoterBagFor::remove(voter_id)`
	/// to update storage for the bag and `node`.
	fn remove_node(&mut self, node: &Node<T>) {
		// Update previous node.
		if let Some(mut prev) = node.prev() {
			prev.next = node.next.clone();
			prev.put();
		}
		// Update next node.
		if let Some(mut next) = node.next() {
			next.prev = node.prev.clone();
			next.put();
		}

		// clear the bag head/tail pointers as necessary
		if self.head.as_ref() == Some(&node.id) {
			self.head = node.next.clone();
		}
		if self.tail.as_ref() == Some(&node.id) {
			self.tail = node.prev.clone();
		}
	}

	/// Sanity check this bag.
	///
	/// Should be called by the call-site, after each mutating operation on a bag. The call site of
	/// this struct is always `List`.
	///
	/// * Ensures head has no prev.
	/// * Ensures tail has no next.
	/// * Ensures there are no loops, traversal from head to tail is correct.
	fn sanity_check(&self) -> Result<(), &'static str> {
		frame_support::ensure!(
			self.head()
				.map(|head| head.prev().is_none())
				// if there is no head, then there must not be a tail, meaning that the bag is
				// empty.
				.unwrap_or_else(|| self.tail.is_none()),
			"head has a prev"
		);

		frame_support::ensure!(
			self.tail()
				.map(|tail| tail.next().is_none())
				// if there is no tail, then there must not be a head, meaning that the bag is
				// empty.
				.unwrap_or_else(|| self.head.is_none()),
			"tail has a next"
		);

		let mut seen_in_bag = BTreeSet::new();
		frame_support::ensure!(
			self.iter()
				.map(|node| node.id)
				// each voter is only seen once, thus there is no cycle within a bag
				.all(|voter| seen_in_bag.insert(voter)),
			"duplicate found in bag"
		);

		Ok(())
	}
}

/// A Node is the fundamental element comprising the doubly-linked lists which for each bag.
#[derive(Encode, Decode)]
#[cfg_attr(feature = "std", derive(frame_support::DebugNoBound))]
#[cfg_attr(test, derive(PartialEq, Clone))]
pub struct Node<T: Config> {
	id: T::AccountId,
	prev: Option<T::AccountId>,
	next: Option<T::AccountId>,

	/// The bag index is not stored in storage, but injected during all fetch operations.
	#[codec(skip)]
	pub(crate) bag_upper: VoteWeight,
}

impl<T: Config> Node<T> {
	/// Get a node by bag idx and account id.
	fn get(bag_upper: VoteWeight, account_id: &T::AccountId) -> Option<Node<T>> {
		debug_assert!(
			T::BagThresholds::get().contains(&bag_upper) || bag_upper == VoteWeight::MAX,
			"it is a logic error to attempt to get a bag which is not in the thresholds list"
		);
		crate::VoterNodes::<T>::try_get(account_id).ok().map(|mut node| {
			node.bag_upper = bag_upper;
			node
		})
	}

	/// Get a node by account id.
	///
	/// Note that this must perform two storage lookups: one to identify which bag is appropriate,
	/// and another to actually fetch the node.
	pub(crate) fn from_id(account_id: &T::AccountId) -> Option<Node<T>> {
		let bag = current_bag_for::<T>(account_id)?;
		Self::get(bag, account_id)
	}

	/// Get a node by account id, assuming it's in the same bag as this node.
	fn in_bag(&self, account_id: &T::AccountId) -> Option<Node<T>> {
		Self::get(self.bag_upper, account_id)
	}

	/// Put the node back into storage.
	fn put(self) {
		crate::VoterNodes::<T>::insert(self.id.clone(), self);
	}

	/// Get the previous node in the bag.
	fn prev(&self) -> Option<Node<T>> {
		self.prev.as_ref().and_then(|id| self.in_bag(id))
	}

	/// Get the next node in the bag.
	fn next(&self) -> Option<Node<T>> {
		self.next.as_ref().and_then(|id| self.in_bag(id))
	}

	/// `true` when this voter is in the wrong bag.
	fn is_misplaced(&self, current_weight: VoteWeight) -> bool {
		notional_bag_for::<T>(current_weight) != self.bag_upper
	}

	/// Get the underlying voter.
	pub(crate) fn id(&self) -> &T::AccountId {
		&self.id
	}
}
