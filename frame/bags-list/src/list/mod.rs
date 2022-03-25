// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

//! Implementation of a "bags list": a semi-sorted list where ordering granularity is dictated by
//! configurable thresholds that delineate the boundaries of bags. It uses a pattern of composite
//! data structures, where multiple storage items are masked by one outer API. See
//! [`crate::ListNodes`], [`crate::ListBags`] for more information.
//!
//! The outer API of this module is the [`List`] struct. It wraps all acceptable operations on top
//! of the aggregate linked list. All operations with the bags list should happen through this
//! interface.

use crate::Config;
use codec::{Decode, Encode, MaxEncodedLen};
use frame_election_provider_support::ScoreProvider;
use frame_support::{traits::Get, DefaultNoBound};
use scale_info::TypeInfo;
use sp_runtime::traits::{Bounded, Zero};
use sp_std::{
	boxed::Box,
	collections::{btree_map::BTreeMap, btree_set::BTreeSet},
	iter,
	marker::PhantomData,
	vec::Vec,
};

#[derive(Debug, PartialEq, Eq)]
pub enum ListError {
	/// A duplicate id has been detected.
	Duplicate,
}

#[cfg(test)]
mod tests;

/// Given a certain score, to which bag does it belong to?
///
/// Bags are identified by their upper threshold; the value returned by this function is guaranteed
/// to be a member of `T::BagThresholds`.
///
/// Note that even if the thresholds list does not have `T::Score::max_value()` as its final member,
/// this function behaves as if it does.
pub fn notional_bag_for<T: Config<I>, I: 'static>(score: T::Score) -> T::Score {
	let thresholds = T::BagThresholds::get();
	let idx = thresholds.partition_point(|&threshold| score > threshold);
	thresholds.get(idx).copied().unwrap_or(T::Score::max_value())
}

/// The **ONLY** entry point of this module. All operations to the bags-list should happen through
/// this interface. It is forbidden to access other module members directly.
//
// Data structure providing efficient mostly-accurate selection of the top N id by `Score`.
//
// It's implemented as a set of linked lists. Each linked list comprises a bag of ids of
// arbitrary and unbounded length, all having a score within a particular constant range.
// This structure means that ids can be added and removed in `O(1)` time.
//
// Iteration is accomplished by chaining the iteration of each bag, from greatest to least. While
// the users within any particular bag are sorted in an entirely arbitrary order, the overall score
// decreases as successive bags are reached. This means that it is valid to truncate
// iteration at any desired point; only those ids in the lowest bag can be excluded. This
// satisfies both the desire for fairness and the requirement for efficiency.
pub struct List<T: Config<I>, I: 'static = ()>(PhantomData<(T, I)>);

impl<T: Config<I>, I: 'static> List<T, I> {
	/// Remove all data associated with the list from storage.
	///
	/// ## WARNING
	///
	/// this function should generally not be used in production as it could lead to a very large
	/// number of storage accesses.
	pub(crate) fn unsafe_clear() {
		crate::ListBags::<T, I>::remove_all(None);
		crate::ListNodes::<T, I>::remove_all();
	}

	/// Regenerate all of the data from the given ids.
	///
	/// WARNING: this is expensive and should only ever be performed when the list needs to be
	/// generated from scratch. Care needs to be taken to ensure
	///
	/// This may or may not need to be called at genesis as well, based on the configuration of the
	/// pallet using this `List`.
	///
	/// Returns the number of ids migrated.
	pub fn unsafe_regenerate(
		all: impl IntoIterator<Item = T::AccountId>,
		score_of: Box<dyn Fn(&T::AccountId) -> T::Score>,
	) -> u32 {
		// NOTE: This call is unsafe for the same reason as SortedListProvider::unsafe_regenerate.
		// I.e. because it can lead to many storage accesses.
		// So it is ok to call it as caller must ensure the conditions.
		Self::unsafe_clear();
		Self::insert_many(all, score_of)
	}

	/// Migrate the list from one set of thresholds to another.
	///
	/// This should only be called as part of an intentional migration; it's fairly expensive.
	///
	/// Returns the number of accounts affected.
	///
	/// Preconditions:
	///
	/// - `old_thresholds` is the previous list of thresholds.
	/// - All `bag_upper` currently in storage are members of `old_thresholds`.
	/// - `T::BagThresholds` has already been updated and is the new set of thresholds.
	///
	/// Postconditions:
	///
	/// - All `bag_upper` currently in storage are members of `T::BagThresholds`.
	/// - No id is changed unless required to by the difference between the old threshold list and
	///   the new.
	/// - ids whose bags change at all are implicitly rebagged into the appropriate bag in the new
	///   threshold set.
	#[allow(dead_code)]
	pub fn migrate(old_thresholds: &[T::Score]) -> u32 {
		let new_thresholds = T::BagThresholds::get();
		if new_thresholds == old_thresholds {
			return 0
		}

		// we can't check all preconditions, but we can check one
		debug_assert!(
			crate::ListBags::<T, I>::iter()
				.all(|(threshold, _)| old_thresholds.contains(&threshold)),
			"not all `bag_upper` currently in storage are members of `old_thresholds`",
		);
		debug_assert!(
			crate::ListNodes::<T, I>::iter()
				.all(|(_, node)| old_thresholds.contains(&node.bag_upper)),
			"not all `node.bag_upper` currently in storage are members of `old_thresholds`",
		);

		let old_set: BTreeSet<_> = old_thresholds.iter().copied().collect();
		let new_set: BTreeSet<_> = new_thresholds.iter().copied().collect();

		// accounts that need to be rebagged
		let mut affected_accounts = BTreeSet::new();
		// track affected old bags to make sure we only iterate them once
		let mut affected_old_bags = BTreeSet::new();

		let new_bags = new_set.difference(&old_set).copied();
		// a new bag means that all accounts previously using the old bag's threshold must now
		// be rebagged
		for inserted_bag in new_bags {
			let affected_bag = {
				// this recreates `notional_bag_for` logic, but with the old thresholds.
				let idx = old_thresholds.partition_point(|&threshold| inserted_bag > threshold);
				old_thresholds.get(idx).copied().unwrap_or(T::Score::max_value())
			};
			if !affected_old_bags.insert(affected_bag) {
				// If the previous threshold list was [10, 20], and we insert [3, 5], then there's
				// no point iterating through bag 10 twice.
				continue
			}

			if let Some(bag) = Bag::<T, I>::get(affected_bag) {
				affected_accounts.extend(bag.iter().map(|node| node.id));
			}
		}

		let removed_bags = old_set.difference(&new_set).copied();
		// a removed bag means that all members of that bag must be rebagged
		for removed_bag in removed_bags.clone() {
			if !affected_old_bags.insert(removed_bag) {
				continue
			}

			if let Some(bag) = Bag::<T, I>::get(removed_bag) {
				affected_accounts.extend(bag.iter().map(|node| node.id));
			}
		}

		// migrate the voters whose bag has changed
		let num_affected = affected_accounts.len() as u32;
		let score_of = T::ScoreProvider::score;
		let _removed = Self::remove_many(&affected_accounts);
		debug_assert_eq!(_removed, num_affected);
		let _inserted = Self::insert_many(affected_accounts.into_iter(), score_of);
		debug_assert_eq!(_inserted, num_affected);

		// we couldn't previously remove the old bags because both insertion and removal assume that
		// it's always safe to add a bag if it's not present. Now that that's sorted, we can get rid
		// of them.
		//
		// it's pretty cheap to iterate this again, because both sets are in-memory and require no
		// lookups.
		for removed_bag in removed_bags {
			debug_assert!(
				!crate::ListNodes::<T, I>::iter().any(|(_, node)| node.bag_upper == removed_bag),
				"no id should be present in a removed bag",
			);
			crate::ListBags::<T, I>::remove(removed_bag);
		}

		debug_assert_eq!(Self::sanity_check(), Ok(()));

		num_affected
	}

	/// Returns `true` if the list contains `id`, otherwise returns `false`.
	pub(crate) fn contains(id: &T::AccountId) -> bool {
		crate::ListNodes::<T, I>::contains_key(id)
	}

	/// Iterate over all nodes in all bags in the list.
	///
	/// Full iteration can be expensive; it's recommended to limit the number of items with
	/// `.take(n)`.
	pub(crate) fn iter() -> impl Iterator<Item = Node<T, I>> {
		// We need a touch of special handling here: because we permit `T::BagThresholds` to
		// omit the final bound, we need to ensure that we explicitly include that threshold in the
		// list.
		//
		// It's important to retain the ability to omit the final bound because it makes tests much
		// easier; they can just configure `type BagThresholds = ()`.
		let thresholds = T::BagThresholds::get();
		let iter = thresholds.iter().copied();
		let iter: Box<dyn Iterator<Item = T::Score>> = if thresholds.last() ==
			Some(&T::Score::max_value())
		{
			// in the event that they included it, we can just pass the iterator through unchanged.
			Box::new(iter.rev())
		} else {
			// otherwise, insert it here.
			Box::new(iter.chain(iter::once(T::Score::max_value())).rev())
		};

		iter.filter_map(Bag::get).flat_map(|bag| bag.iter())
	}

	/// Insert several ids into the appropriate bags in the list. Continues with insertions
	/// if duplicates are detected.
	///
	/// Returns the final count of number of ids inserted.
	fn insert_many(
		ids: impl IntoIterator<Item = T::AccountId>,
		score_of: impl Fn(&T::AccountId) -> T::Score,
	) -> u32 {
		let mut count = 0;
		ids.into_iter().for_each(|v| {
			let score = score_of(&v);
			if Self::insert(v, score).is_ok() {
				count += 1;
			}
		});

		count
	}

	/// Insert a new id into the appropriate bag in the list.
	///
	/// Returns an error if the list already contains `id`.
	pub(crate) fn insert(id: T::AccountId, score: T::Score) -> Result<(), ListError> {
		if Self::contains(&id) {
			return Err(ListError::Duplicate)
		}

		let bag_score = notional_bag_for::<T, I>(score);
		let mut bag = Bag::<T, I>::get_or_make(bag_score);
		// unchecked insertion is okay; we just got the correct `notional_bag_for`.
		bag.insert_unchecked(id.clone());

		// new inserts are always the tail, so we must write the bag.
		bag.put();

		crate::log!(
			debug,
			"inserted {:?} with score {:?
			} into bag {:?}, new count is {}",
			id,
			score,
			bag_score,
			crate::ListNodes::<T, I>::count(),
		);

		Ok(())
	}

	/// Remove an id from the list.
	pub(crate) fn remove(id: &T::AccountId) {
		Self::remove_many(sp_std::iter::once(id));
	}

	/// Remove many ids from the list.
	///
	/// This is more efficient than repeated calls to `Self::remove`.
	///
	/// Returns the final count of number of ids removed.
	fn remove_many<'a>(ids: impl IntoIterator<Item = &'a T::AccountId>) -> u32 {
		let mut bags = BTreeMap::new();
		let mut count = 0;

		for id in ids.into_iter() {
			let node = match Node::<T, I>::get(id) {
				Some(node) => node,
				None => continue,
			};
			count += 1;

			if !node.is_terminal() {
				// this node is not a head or a tail and thus the bag does not need to be updated
				node.excise()
			} else {
				// this node is a head or tail, so the bag needs to be updated
				let bag = bags
					.entry(node.bag_upper)
					.or_insert_with(|| Bag::<T, I>::get_or_make(node.bag_upper));
				// node.bag_upper must be correct, therefore this bag will contain this node.
				bag.remove_node_unchecked(&node);
			}

			// now get rid of the node itself
			node.remove_from_storage_unchecked()
		}

		for (_, bag) in bags {
			bag.put();
		}

		count
	}

	/// Update a node's position in the list.
	///
	/// If the node was in the correct bag, no effect. If the node was in the incorrect bag, they
	/// are moved into the correct bag.
	///
	/// Returns `Some((old_idx, new_idx))` if the node moved, otherwise `None`.
	///
	/// This operation is somewhat more efficient than simply calling [`self.remove`] followed by
	/// [`self.insert`]. However, given large quantities of nodes to move, it may be more efficient
	/// to call [`self.remove_many`] followed by [`self.insert_many`].
	pub(crate) fn update_position_for(
		node: Node<T, I>,
		new_score: T::Score,
	) -> Option<(T::Score, T::Score)> {
		node.is_misplaced(new_score).then(move || {
			let old_bag_upper = node.bag_upper;

			if !node.is_terminal() {
				// this node is not a head or a tail, so we can just cut it out of the list. update
				// and put the prev and next of this node, we do `node.put` inside `insert_note`.
				node.excise();
			} else if let Some(mut bag) = Bag::<T, I>::get(node.bag_upper) {
				// this is a head or tail, so the bag must be updated.
				bag.remove_node_unchecked(&node);
				bag.put();
			} else {
				crate::log!(
					error,
					"Node {:?} did not have a bag; ListBags is in an inconsistent state",
					node.id,
				);
				debug_assert!(false, "every node must have an extant bag associated with it");
			}

			// put the node into the appropriate new bag.
			let new_bag_upper = notional_bag_for::<T, I>(new_score);
			let mut bag = Bag::<T, I>::get_or_make(new_bag_upper);
			// prev, next, and bag_upper of the node are updated inside `insert_node`, also
			// `node.put` is in there.
			bag.insert_node_unchecked(node);
			bag.put();

			(old_bag_upper, new_bag_upper)
		})
	}

	/// Put `heavier_id` to the position directly in front of `lighter_id`. Both ids must be in the
	/// same bag and the `score_of` `lighter_id` must be less than that of `heavier_id`.
	pub(crate) fn put_in_front_of(
		lighter_id: &T::AccountId,
		heavier_id: &T::AccountId,
	) -> Result<(), crate::pallet::Error<T, I>> {
		use crate::pallet;
		use frame_support::ensure;

		let lighter_node = Node::<T, I>::get(&lighter_id).ok_or(pallet::Error::IdNotFound)?;
		let heavier_node = Node::<T, I>::get(&heavier_id).ok_or(pallet::Error::IdNotFound)?;

		ensure!(lighter_node.bag_upper == heavier_node.bag_upper, pallet::Error::NotInSameBag);

		// this is the most expensive check, so we do it last.
		ensure!(
			T::ScoreProvider::score(&heavier_id) > T::ScoreProvider::score(&lighter_id),
			pallet::Error::NotHeavier
		);

		// remove the heavier node from this list. Note that this removes the node from storage and
		// decrements the node counter.
		Self::remove(&heavier_id);

		// re-fetch `lighter_node` from storage since it may have been updated when `heavier_node`
		// was removed.
		let lighter_node = Node::<T, I>::get(&lighter_id).ok_or_else(|| {
			debug_assert!(false, "id that should exist cannot be found");
			crate::log!(warn, "id that should exist cannot be found");
			pallet::Error::IdNotFound
		})?;

		// insert `heavier_node` directly in front of `lighter_node`. This will update both nodes
		// in storage and update the node counter.
		Self::insert_at_unchecked(lighter_node, heavier_node);

		Ok(())
	}

	/// Insert `node` directly in front of `at`.
	///
	/// WARNINGS:
	/// - this is a naive function in that it does not check if `node` belongs to the same bag as
	/// `at`. It is expected that the call site will check preconditions.
	/// - this will panic if `at.bag_upper` is not a bag that already exists in storage.
	fn insert_at_unchecked(mut at: Node<T, I>, mut node: Node<T, I>) {
		// connect `node` to its new `prev`.
		node.prev = at.prev.clone();
		if let Some(mut prev) = at.prev() {
			prev.next = Some(node.id().clone());
			prev.put()
		}

		// connect `node` and `at`.
		node.next = Some(at.id().clone());
		at.prev = Some(node.id().clone());

		if node.is_terminal() {
			// `node` is the new head, so we make sure the bag is updated. Note,
			// since `node` is always in front of `at` we know that 1) there is always at least 2
			// nodes in the bag, and 2) only `node` could be the head and only `at` could be the
			// tail.
			let mut bag = Bag::<T, I>::get(at.bag_upper)
				.expect("given nodes must always have a valid bag. qed.");

			if node.prev == None {
				bag.head = Some(node.id().clone())
			}

			bag.put()
		};

		// write the updated nodes to storage.
		at.put();
		node.put();
	}

	/// Sanity check the list.
	///
	/// This should be called from the call-site, whenever one of the mutating apis (e.g. `insert`)
	/// is being used, after all other staking data (such as counter) has been updated. It checks:
	///
	/// * there are no duplicate ids,
	/// * length of this list is in sync with `ListNodes::count()`,
	/// * and sanity-checks all bags and nodes. This will cascade down all the checks and makes sure
	/// all bags and nodes are checked per *any* update to `List`.
	#[cfg(feature = "std")]
	pub(crate) fn sanity_check() -> Result<(), &'static str> {
		use frame_support::ensure;
		let mut seen_in_list = BTreeSet::new();
		ensure!(
			Self::iter().map(|node| node.id).all(|id| seen_in_list.insert(id)),
			"duplicate identified",
		);

		let iter_count = Self::iter().count() as u32;
		let stored_count = crate::ListNodes::<T, I>::count();
		let nodes_count = crate::ListNodes::<T, I>::iter().count() as u32;
		ensure!(iter_count == stored_count, "iter_count != stored_count");
		ensure!(stored_count == nodes_count, "stored_count != nodes_count");

		crate::log!(debug, "count of nodes: {}", stored_count);

		let active_bags = {
			let thresholds = T::BagThresholds::get().iter().copied();
			let thresholds: Vec<T::Score> =
				if thresholds.clone().last() == Some(T::Score::max_value()) {
					// in the event that they included it, we don't need to make any changes
					thresholds.collect()
				} else {
					// otherwise, insert it here.
					thresholds.chain(iter::once(T::Score::max_value())).collect()
				};
			thresholds.into_iter().filter_map(|t| Bag::<T, I>::get(t))
		};

		let _ = active_bags.clone().map(|b| b.sanity_check()).collect::<Result<_, _>>()?;

		let nodes_in_bags_count =
			active_bags.clone().fold(0u32, |acc, cur| acc + cur.iter().count() as u32);
		ensure!(nodes_count == nodes_in_bags_count, "stored_count != nodes_in_bags_count");

		crate::log!(debug, "count of active bags {}", active_bags.count());

		// check that all nodes are sane. We check the `ListNodes` storage item directly in case we
		// have some "stale" nodes that are not in a bag.
		for (_id, node) in crate::ListNodes::<T, I>::iter() {
			node.sanity_check()?
		}

		Ok(())
	}

	#[cfg(not(feature = "std"))]
	pub(crate) fn sanity_check() -> Result<(), &'static str> {
		Ok(())
	}

	/// Returns the nodes of all non-empty bags. For testing and benchmarks.
	#[cfg(any(feature = "std", feature = "runtime-benchmarks"))]
	#[allow(dead_code)]
	pub(crate) fn get_bags() -> Vec<(T::Score, Vec<T::AccountId>)> {
		use frame_support::traits::Get as _;

		let thresholds = T::BagThresholds::get();
		let iter = thresholds.iter().copied();
		let iter: Box<dyn Iterator<Item = T::Score>> = if thresholds.last() ==
			Some(&T::Score::max_value())
		{
			// in the event that they included it, we can just pass the iterator through unchanged.
			Box::new(iter)
		} else {
			// otherwise, insert it here.
			Box::new(iter.chain(sp_std::iter::once(T::Score::max_value())))
		};

		iter.filter_map(|t| {
			Bag::<T, I>::get(t)
				.map(|bag| (t, bag.iter().map(|n| n.id().clone()).collect::<Vec<_>>()))
		})
		.collect::<Vec<_>>()
	}
}

/// A Bag is a doubly-linked list of ids, where each id is mapped to a [`Node`].
///
/// Note that we maintain both head and tail pointers. While it would be possible to get away with
/// maintaining only a head pointer and cons-ing elements onto the front of the list, it's more
/// desirable to ensure that there is some element of first-come, first-serve to the list's
/// iteration so that there's no incentive to churn ids positioning to improve the chances of
/// appearing within the ids set.
#[derive(DefaultNoBound, Encode, Decode, MaxEncodedLen, TypeInfo)]
#[codec(mel_bound())]
#[scale_info(skip_type_params(T, I))]
#[cfg_attr(feature = "std", derive(frame_support::DebugNoBound, Clone, PartialEq))]
pub struct Bag<T: Config<I>, I: 'static = ()> {
	head: Option<T::AccountId>,
	tail: Option<T::AccountId>,

	#[codec(skip)]
	bag_upper: T::Score,
	#[codec(skip)]
	_phantom: PhantomData<I>,
}

impl<T: Config<I>, I: 'static> Bag<T, I> {
	#[cfg(test)]
	pub(crate) fn new(
		head: Option<T::AccountId>,
		tail: Option<T::AccountId>,
		bag_upper: T::Score,
	) -> Self {
		Self { head, tail, bag_upper, _phantom: PhantomData }
	}

	/// Get a bag by its upper score.
	pub(crate) fn get(bag_upper: T::Score) -> Option<Bag<T, I>> {
		crate::ListBags::<T, I>::try_get(bag_upper).ok().map(|mut bag| {
			bag.bag_upper = bag_upper;
			bag
		})
	}

	/// Get a bag by its upper score or make it, appropriately initialized. Does not check if
	/// if `bag_upper` is a valid threshold.
	fn get_or_make(bag_upper: T::Score) -> Bag<T, I> {
		Self::get(bag_upper).unwrap_or(Bag { bag_upper, ..Default::default() })
	}

	/// `True` if self is empty.
	fn is_empty(&self) -> bool {
		self.head.is_none() && self.tail.is_none()
	}

	/// Put the bag back into storage.
	fn put(self) {
		if self.is_empty() {
			crate::ListBags::<T, I>::remove(self.bag_upper);
		} else {
			crate::ListBags::<T, I>::insert(self.bag_upper, self);
		}
	}

	/// Get the head node in this bag.
	fn head(&self) -> Option<Node<T, I>> {
		self.head.as_ref().and_then(|id| Node::get(id))
	}

	/// Get the tail node in this bag.
	fn tail(&self) -> Option<Node<T, I>> {
		self.tail.as_ref().and_then(|id| Node::get(id))
	}

	/// Iterate over the nodes in this bag.
	pub(crate) fn iter(&self) -> impl Iterator<Item = Node<T, I>> {
		sp_std::iter::successors(self.head(), |prev| prev.next())
	}

	/// Insert a new id into this bag.
	///
	/// This is private on purpose because it's naive: it doesn't check whether this is the
	/// appropriate bag for this id at all. Generally, use [`List::insert`] instead.
	///
	/// Storage note: this modifies storage, but only for the nodes. You still need to call
	/// `self.put()` after use.
	fn insert_unchecked(&mut self, id: T::AccountId) {
		// insert_node will overwrite `prev`, `next` and `bag_upper` to the proper values. As long
		// as this bag is the correct one, we're good. All calls to this must come after getting the
		// correct [`notional_bag_for`].
		self.insert_node_unchecked(Node::<T, I> {
			id,
			prev: None,
			next: None,
			bag_upper: Zero::zero(),
			_phantom: PhantomData,
		});
	}

	/// Insert a node into this bag.
	///
	/// This is private on purpose because it's naive; it doesn't check whether this is the
	/// appropriate bag for this node at all. Generally, use [`List::insert`] instead.
	///
	/// Storage note: this modifies storage, but only for the node. You still need to call
	/// `self.put()` after use.
	fn insert_node_unchecked(&mut self, mut node: Node<T, I>) {
		if let Some(tail) = &self.tail {
			if *tail == node.id {
				// this should never happen, but this check prevents one path to a worst case
				// infinite loop.
				debug_assert!(false, "system logic error: inserting a node who has the id of tail");
				crate::log!(warn, "system logic error: inserting a node who has the id of tail");
				return
			};
		}

		// re-set the `bag_upper`. Regardless of whatever the node had previously, now it is going
		// to be `self.bag_upper`.
		node.bag_upper = self.bag_upper;

		let id = node.id.clone();
		// update this node now, treating it as the new tail.
		node.prev = self.tail.clone();
		node.next = None;
		node.put();

		// update the previous tail.
		if let Some(mut old_tail) = self.tail() {
			old_tail.next = Some(id.clone());
			old_tail.put();
		}
		self.tail = Some(id.clone());

		// ensure head exist. This is only set when the length of the bag is just 1, i.e. if this is
		// the first insertion into the bag. In this case, both head and tail should point to the
		// same node.
		if self.head.is_none() {
			self.head = Some(id.clone());
			debug_assert!(self.iter().count() == 1);
		}
	}

	/// Remove a node from this bag.
	///
	/// This is private on purpose because it doesn't check whether this bag contains the node in
	/// the first place. Generally, use [`List::remove`] instead, similar to `insert_unchecked`.
	///
	/// Storage note: this modifies storage, but only for adjacent nodes. You still need to call
	/// `self.put()` and `ListNodes::remove(id)` to update storage for the bag and `node`.
	fn remove_node_unchecked(&mut self, node: &Node<T, I>) {
		// reassign neighboring nodes.
		node.excise();

		// clear the bag head/tail pointers as necessary.
		if self.tail.as_ref() == Some(&node.id) {
			self.tail = node.prev.clone();
		}
		if self.head.as_ref() == Some(&node.id) {
			self.head = node.next.clone();
		}
	}

	/// Sanity check this bag.
	///
	/// Should be called by the call-site, after any mutating operation on a bag. The call site of
	/// this struct is always `List`.
	///
	/// * Ensures head has no prev.
	/// * Ensures tail has no next.
	/// * Ensures there are no loops, traversal from head to tail is correct.
	#[cfg(feature = "std")]
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

	#[cfg(not(feature = "std"))]
	fn sanity_check(&self) -> Result<(), &'static str> {
		Ok(())
	}

	/// Iterate over the nodes in this bag (public for tests).
	#[cfg(feature = "std")]
	#[allow(dead_code)]
	pub fn std_iter(&self) -> impl Iterator<Item = Node<T, I>> {
		sp_std::iter::successors(self.head(), |prev| prev.next())
	}

	/// Check if the bag contains a node with `id`.
	#[cfg(feature = "std")]
	fn contains(&self, id: &T::AccountId) -> bool {
		self.iter().any(|n| n.id() == id)
	}
}

/// A Node is the fundamental element comprising the doubly-linked list described by `Bag`.
#[derive(Encode, Decode, MaxEncodedLen, TypeInfo)]
#[codec(mel_bound())]
#[scale_info(skip_type_params(T, I))]
#[cfg_attr(feature = "std", derive(frame_support::DebugNoBound, Clone, PartialEq))]
pub struct Node<T: Config<I>, I: 'static = ()> {
	id: T::AccountId,
	prev: Option<T::AccountId>,
	next: Option<T::AccountId>,
	bag_upper: T::Score,
	#[codec(skip)]
	_phantom: PhantomData<I>,
}

impl<T: Config<I>, I: 'static> Node<T, I> {
	/// Get a node by id.
	pub fn get(id: &T::AccountId) -> Option<Node<T, I>> {
		crate::ListNodes::<T, I>::try_get(id).ok()
	}

	/// Put the node back into storage.
	fn put(self) {
		crate::ListNodes::<T, I>::insert(self.id.clone(), self);
	}

	/// Update neighboring nodes to point to reach other.
	///
	/// Only updates storage for adjacent nodes, but not `self`; so the user may need to call
	/// `self.put`.
	fn excise(&self) {
		// Update previous node.
		if let Some(mut prev) = self.prev() {
			prev.next = self.next.clone();
			prev.put();
		}
		// Update next self.
		if let Some(mut next) = self.next() {
			next.prev = self.prev.clone();
			next.put();
		}
	}

	/// This is a naive function that removes a node from the `ListNodes` storage item.
	///
	/// It is naive because it does not check if the node has first been removed from its bag.
	fn remove_from_storage_unchecked(&self) {
		crate::ListNodes::<T, I>::remove(&self.id)
	}

	/// Get the previous node in the bag.
	fn prev(&self) -> Option<Node<T, I>> {
		self.prev.as_ref().and_then(|id| Node::get(id))
	}

	/// Get the next node in the bag.
	fn next(&self) -> Option<Node<T, I>> {
		self.next.as_ref().and_then(|id| Node::get(id))
	}

	/// `true` when this voter is in the wrong bag.
	pub fn is_misplaced(&self, current_score: T::Score) -> bool {
		notional_bag_for::<T, I>(current_score) != self.bag_upper
	}

	/// `true` when this voter is a bag head or tail.
	fn is_terminal(&self) -> bool {
		self.prev.is_none() || self.next.is_none()
	}

	/// Get the underlying voter.
	pub(crate) fn id(&self) -> &T::AccountId {
		&self.id
	}

	/// Get the underlying voter (public fo tests).
	#[cfg(feature = "std")]
	#[allow(dead_code)]
	pub fn std_id(&self) -> &T::AccountId {
		&self.id
	}

	/// The bag this nodes belongs to (public for benchmarks).
	#[cfg(feature = "runtime-benchmarks")]
	#[allow(dead_code)]
	pub fn bag_upper(&self) -> T::Score {
		self.bag_upper
	}

	#[cfg(feature = "std")]
	fn sanity_check(&self) -> Result<(), &'static str> {
		let expected_bag = Bag::<T, I>::get(self.bag_upper).ok_or("bag not found for node")?;

		let id = self.id();

		frame_support::ensure!(
			expected_bag.contains(id),
			"node does not exist in the expected bag"
		);

		let non_terminal_check = !self.is_terminal() &&
			expected_bag.head.as_ref() != Some(id) &&
			expected_bag.tail.as_ref() != Some(id);
		let terminal_check =
			expected_bag.head.as_ref() == Some(id) || expected_bag.tail.as_ref() == Some(id);
		frame_support::ensure!(
			non_terminal_check || terminal_check,
			"a terminal node is neither its bag head or tail"
		);

		Ok(())
	}
}
