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

use codec::{Decode, Encode};
use frame_support::{ensure, traits::Get, DefaultNoBound};
use sp_runtime::SaturatedConversion;
use sp_std::{
	boxed::Box,
	collections::{btree_map::BTreeMap, btree_set::BTreeSet},
	iter,
	marker::PhantomData,
};

use crate::{
	slashing::SlashingSpans, AccountIdOf, Config, Nominations, Nominators, Pallet, Validators,
	VoteWeight, VoterBagFor, VotingDataOf,
};

/// [`Voter`] parametrized by [`Config`] instead of by `AccountId`.
pub type VoterOf<T> = Voter<AccountIdOf<T>>;

/// Given a certain vote weight, which bag should contain this voter?
///
/// Bags are identified by their upper threshold; the value returned by this function is guaranteed
/// to be a member of `T::VoterBagThresholds`.
///
/// This is used instead of a simpler scheme, such as the index within `T::VoterBagThresholds`,
/// because in the event that bags are inserted or deleted, the number of affected voters which need
/// to be migrated is smaller.
///
/// Note that even if the thresholds list does not have `VoteWeight::MAX` as its final member, this
/// function behaves as if it does.
fn notional_bag_for<T: Config>(weight: VoteWeight) -> VoteWeight {
	let thresholds = T::VoterBagThresholds::get();
	let idx = thresholds.partition_point(|&threshold| weight > threshold);
	thresholds.get(idx).copied().unwrap_or(VoteWeight::MAX)
}

/// Find the upper threshold of the actual bag containing the current voter.
fn current_bag_for<T: Config>(id: &AccountIdOf<T>) -> Option<VoteWeight> {
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
	/// Remove all data associated with the voter list from storage.
	pub fn clear() {
		crate::CounterForVoters::<T>::kill();
		crate::VoterBagFor::<T>::remove_all(None);
		crate::VoterBags::<T>::remove_all(None);
		crate::VoterNodes::<T>::remove_all(None);
	}

	/// Regenerate voter data from the `Nominators` and `Validators` storage items.
	///
	/// This is expensive and should only ever be performed during a migration, never during
	/// consensus.
	///
	/// Returns the number of voters migrated.
	pub fn regenerate() -> u32 {
		Self::clear();

		let nominators_iter = Nominators::<T>::iter().map(|(id, _)| Voter::nominator(id));
		let validators_iter = Validators::<T>::iter().map(|(id, _)| Voter::validator(id));
		let weight_of = Pallet::<T>::weight_of_fn();

		Self::insert_many(nominators_iter.chain(validators_iter), weight_of)
	}

	/// Decode the length of the voter list.
	pub fn decode_len() -> Option<usize> {
		let maybe_len = crate::CounterForVoters::<T>::try_get().ok().map(|n| n.saturated_into());
		debug_assert_eq!(
			maybe_len.unwrap_or_default(),
			crate::VoterNodes::<T>::iter().count(),
			"stored length must match count of nodes",
		);
		debug_assert_eq!(
			// TODO: this case will fail in migration pre check
			maybe_len.unwrap_or_default() as u32,
			crate::CounterForNominators::<T>::get() + crate::CounterForValidators::<T>::get(),
			"voter count must be sum of validator and nominator count",
		);
		maybe_len
	}

	/// Iterate over all nodes in all bags in the voter list.
	///
	/// Full iteration can be expensive; it's recommended to limit the number of items with
	/// `.take(n)`.
	pub fn iter() -> impl Iterator<Item = Node<T>> {
		// We need a touch of special handling here: because we permit `T::VoterBagThresholds` to
		// omit the final bound, we need to ensure that we explicitly include that threshold in the
		// list.
		//
		// It's important to retain the ability to omit the final bound because it makes tests much
		// easier; they can just configure `type VoterBagThresholds = ()`.
		let thresholds = T::VoterBagThresholds::get();
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

	/// Insert a new voter into the appropriate bag in the voter list.
	///
	/// If the voter is already present in the list, their type will be updated.
	/// That case is cheaper than inserting a new voter.
	pub fn insert_as(account_id: &AccountIdOf<T>, voter_type: VoterType) {
		// if this is an update operation we can complete this easily and cheaply
		if !Node::<T>::update_voter_type_for(account_id, voter_type) {
			// otherwise, we need to insert from scratch
			let weight_of = Pallet::<T>::weight_of_fn();
			let voter = Voter { id: account_id.clone(), voter_type };
			Self::insert(voter, weight_of);
		}
	}

	/// Insert a new voter into the appropriate bag in the voter list.
	fn insert(voter: VoterOf<T>, weight_of: impl Fn(&T::AccountId) -> VoteWeight) {
		Self::insert_many(sp_std::iter::once(voter), weight_of);
	}

	/// Insert several voters into the appropriate bags in the voter list.
	///
	/// This is more efficient than repeated calls to `Self::insert`.
	fn insert_many(
		voters: impl IntoIterator<Item = VoterOf<T>>,
		weight_of: impl Fn(&T::AccountId) -> VoteWeight,
	) -> u32 {
		let mut bags = BTreeMap::new();
		let mut count = 0;

		for voter in voters.into_iter() {
			let weight = weight_of(&voter.id);
			let bag = notional_bag_for::<T>(weight);
			crate::log!(debug, "inserting {:?} with weight {} into bag {:?}", voter, weight, bag);
			bags.entry(bag).or_insert_with(|| Bag::<T>::get_or_make(bag)).insert(voter);
			count += 1;
		}

		for (_, bag) in bags {
			bag.put();
		}

		crate::CounterForVoters::<T>::mutate(|prev_count| {
			*prev_count = prev_count.saturating_add(count)
		});
		count
	}

	/// Remove a voter (by id) from the voter list.
	pub fn remove(voter: &AccountIdOf<T>) {
		Self::remove_many(sp_std::iter::once(voter));
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
		weight_of: impl Fn(&AccountIdOf<T>) -> VoteWeight,
	) -> Option<(VoteWeight, VoteWeight)> {
		node.is_misplaced(&weight_of).then(move || {
			let old_idx = node.bag_upper;

			// clear the old bag head/tail pointers as necessary
			if let Some(mut bag) = Bag::<T>::get(node.bag_upper) {
				bag.remove_node(&node);
				bag.put();
			} else {
				debug_assert!(false, "every node must have an extant bag associated with it");
				crate::log!(
					error,
					"Node for staker {:?} did not have a bag; VoterBags is in an inconsistent state",
					node.voter.id,
				);
			}

			// put the voter into the appropriate new bag
			let new_idx = notional_bag_for::<T>(weight_of(&node.voter.id));
			node.bag_upper = new_idx;
			let mut bag = Bag::<T>::get_or_make(node.bag_upper);
			bag.insert_node(node);
			bag.put();

			(old_idx, new_idx)
		})
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
	/// - `T::VoterBagThresholds` has already been updated.
	///
	/// Postconditions:
	///
	/// - All `bag_upper` currently in storage are members of `T::VoterBagThresholds`.
	/// - No voter is changed unless required to by the difference between the old threshold list
	///   and the new.
	/// - Voters whose bags change at all are implicitly rebagged into the appropriate bag in the
	///   new threshold set.
	pub fn migrate(old_thresholds: &[VoteWeight]) -> u32 {
		// we can't check all preconditions, but we can check one
		debug_assert!(
			crate::VoterBags::<T>::iter().all(|(threshold, _)| old_thresholds.contains(&threshold)),
			"not all `bag_upper` currently in storage are members of `old_thresholds`",
		);

		let old_set: BTreeSet<_> = old_thresholds.iter().copied().collect();
		let new_set: BTreeSet<_> = T::VoterBagThresholds::get().iter().copied().collect();

		let mut affected_accounts = BTreeSet::new();
		let mut affected_old_bags = BTreeSet::new();

		// a new bag means that all accounts previously using the old bag's threshold must now
		// be rebagged
		for inserted_bag in new_set.difference(&old_set).copied() {
			let affected_bag = notional_bag_for::<T>(inserted_bag);
			if !affected_old_bags.insert(affected_bag) {
				// If the previous threshold list was [10, 20], and we insert [3, 5], then there's
				// no point iterating through bag 10 twice.
				continue
			}

			if let Some(bag) = Bag::<T>::get(affected_bag) {
				affected_accounts.extend(bag.iter().map(|node| node.voter));
			}
		}

		// a removed bag means that all members of that bag must be rebagged
		for removed_bag in old_set.difference(&new_set).copied() {
			if !affected_old_bags.insert(removed_bag) {
				continue
			}

			if let Some(bag) = Bag::<T>::get(removed_bag) {
				affected_accounts.extend(bag.iter().map(|node| node.voter));
			}
		}

		// migrate the
		let weight_of = Pallet::<T>::weight_of_fn();
		Self::remove_many(affected_accounts.iter().map(|voter| &voter.id));
		let num_affected = Self::insert_many(affected_accounts.into_iter(), weight_of);

		// we couldn't previously remove the old bags because both insertion and removal assume that
		// it's always safe to add a bag if it's not present. Now that that's sorted, we can get rid
		// of them.
		//
		// it's pretty cheap to iterate this again, because both sets are in-memory and require no
		// lookups.
		for removed_bag in old_set.difference(&new_set).copied() {
			debug_assert!(
				!VoterBagFor::<T>::iter().any(|(_voter, bag)| bag == removed_bag),
				"no voter should be present in a removed bag",
			);
			crate::VoterBags::<T>::remove(removed_bag);
		}

		debug_assert!(
			{
				let thresholds = T::VoterBagThresholds::get();
				crate::VoterBags::<T>::iter().all(|(threshold, _)| thresholds.contains(&threshold))
			},
			"all `bag_upper` in storage must be members of the new thresholds",
		);

		num_affected
	}

	/// Sanity check the voter list.
	///
	/// This should be called from the call-site, whenever one of the mutating apis (e.g. `insert`)
	/// is being used, after all other staking data (such as counter) has been updated. It checks
	/// that:
	///
	/// * Iterate all voters in list and make sure there are no duplicates.
	/// * Iterate all voters and ensure their count is in sync with `CounterForVoters`.
	/// * Ensure `CounterForVoters` is `CounterForValidators + CounterForNominators`.
	/// * Sanity-checks all bags. This will cascade down all the checks and makes sure all bags are
	///   checked per *any* update to `VoterList`.
	pub(super) fn sanity_check() -> Result<(), &'static str> {
		let mut seen_in_list = BTreeSet::new();
		ensure!(
			Self::iter().map(|node| node.voter.id).all(|voter| seen_in_list.insert(voter)),
			"duplicate identified",
		);

		let iter_count = Self::iter().collect::<sp_std::vec::Vec<_>>().len() as u32;
		let stored_count = crate::CounterForVoters::<T>::get();
		ensure!(iter_count == stored_count, "iter_count != voter_count");

		let validators = crate::CounterForValidators::<T>::get();
		let nominators = crate::CounterForNominators::<T>::get();
		ensure!(validators + nominators == stored_count, "validators + nominators != voters");

		let _ = T::VoterBagThresholds::get()
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
	head: Option<AccountIdOf<T>>,
	tail: Option<AccountIdOf<T>>,

	#[codec(skip)]
	bag_upper: VoteWeight,
}

impl<T: Config> Bag<T> {
	/// Get a bag by its upper vote weight.
	pub fn get(bag_upper: VoteWeight) -> Option<Bag<T>> {
		debug_assert!(
			T::VoterBagThresholds::get().contains(&bag_upper) || bag_upper == VoteWeight::MAX,
			"it is a logic error to attempt to get a bag which is not in the thresholds list"
		);
		crate::VoterBags::<T>::try_get(bag_upper).ok().map(|mut bag| {
			bag.bag_upper = bag_upper;
			bag
		})
	}

	/// Get a bag by its upper vote weight or make it, appropriately initialized.
	pub fn get_or_make(bag_upper: VoteWeight) -> Bag<T> {
		debug_assert!(
			T::VoterBagThresholds::get().contains(&bag_upper) || bag_upper == VoteWeight::MAX,
			"it is a logic error to attempt to get a bag which is not in the thresholds list"
		);
		Self::get(bag_upper).unwrap_or(Bag { bag_upper, ..Default::default() })
	}

	/// Put the bag back into storage.
	pub fn put(self) {
		crate::VoterBags::<T>::insert(self.bag_upper, self);
	}

	/// Get the head node in this bag.
	pub fn head(&self) -> Option<Node<T>> {
		self.head.as_ref().and_then(|id| Node::get(self.bag_upper, id))
	}

	/// Get the tail node in this bag.
	pub fn tail(&self) -> Option<Node<T>> {
		self.tail.as_ref().and_then(|id| Node::get(self.bag_upper, id))
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
		self.insert_node(Node::<T> { voter, prev: None, next: None, bag_upper: self.bag_upper });
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
		if let Some(mut old_tail) = self.tail() {
			old_tail.next = Some(id.clone());
			old_tail.put();
		}

		// update the internal bag links
		if self.head.is_none() {
			self.head = Some(id.clone());
		}
		self.tail = Some(id.clone());

		crate::VoterBagFor::<T>::insert(id, self.bag_upper);
	}

	/// Remove a voter node from this bag.
	///
	/// This is private on purpose because it doesn't check whether this bag contains the voter in
	/// the first place. Generally, use [`VoterList::remove`] instead.
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
		if self.head.as_ref() == Some(&node.voter.id) {
			self.head = node.next.clone();
		}
		if self.tail.as_ref() == Some(&node.voter.id) {
			self.tail = node.prev.clone();
		}
	}

	/// Sanity check this bag.
	///
	/// Should be called by the call-site, after each mutating operation on a bag. The call site of
	/// this struct is always `VoterList`.
	///
	/// * Ensures head has no prev.
	/// * Ensures tail has no next.
	/// * Ensures there are no loops, traversal from head to tail is correct.
	fn sanity_check(&self) -> Result<(), &'static str> {
		ensure!(
			self.head()
				.map(|head| head.prev().is_none())
				// if there is no head, then there must not be a tail, meaning that the bag is
				// empty.
				.unwrap_or_else(|| self.tail.is_none()),
			"head has a prev"
		);

		ensure!(
			self.tail()
				.map(|tail| tail.next().is_none())
				// if there is no tail, then there must not be a head, meaning that the bag is
				// empty.
				.unwrap_or_else(|| self.head.is_none()),
			"tail has a next"
		);

		let mut seen_in_bag = BTreeSet::new();
		ensure!(
			self.iter()
				.map(|node| node.voter.id)
				// each voter is only seen once, thus there is no cycle within a bag
				.all(|voter| seen_in_bag.insert(voter)),
			"Duplicate found in bag"
		);

		Ok(())
	}
}

/// A Node is the fundamental element comprising the doubly-linked lists which for each bag.
#[derive(Encode, Decode)]
#[cfg_attr(feature = "std", derive(frame_support::DebugNoBound))]
#[cfg_attr(test, derive(PartialEq, Clone))]
pub struct Node<T: Config> {
	voter: Voter<AccountIdOf<T>>,
	prev: Option<AccountIdOf<T>>,
	next: Option<AccountIdOf<T>>,

	/// The bag index is not stored in storage, but injected during all fetch operations.
	#[codec(skip)]
	pub(crate) bag_upper: VoteWeight,
}

impl<T: Config> Node<T> {
	/// Get a node by bag idx and account id.
	pub fn get(bag_upper: VoteWeight, account_id: &AccountIdOf<T>) -> Option<Node<T>> {
		debug_assert!(
			T::VoterBagThresholds::get().contains(&bag_upper) || bag_upper == VoteWeight::MAX,
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
	pub fn from_id(account_id: &AccountIdOf<T>) -> Option<Node<T>> {
		let bag = current_bag_for::<T>(account_id)?;
		Self::get(bag, account_id)
	}

	/// Get a node by account id, assuming it's in the same bag as this node.
	pub fn in_bag(&self, account_id: &AccountIdOf<T>) -> Option<Node<T>> {
		Self::get(self.bag_upper, account_id)
	}

	/// Put the node back into storage.
	pub fn put(self) {
		crate::VoterNodes::<T>::insert(self.voter.id.clone(), self);
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
		let voter_weight = weight_of(&self.voter.id);
		match self.voter.voter_type {
			VoterType::Validator =>
				Some((self.voter.id.clone(), voter_weight, sp_std::vec![self.voter.id.clone()])),
			VoterType::Nominator => {
				let Nominations { submitted_in, mut targets, .. } =
					Nominators::<T>::get(&self.voter.id)?;
				// Filter out nomination targets which were nominated before the most recent
				// slashing span.
				targets.retain(|stash| {
					slashing_spans
						.get(stash)
						.map_or(true, |spans| submitted_in >= spans.last_nonzero_slash())
				});

				(!targets.is_empty()).then(move || (self.voter.id.clone(), voter_weight, targets))
			},
		}
	}

	/// `true` when this voter is in the wrong bag.
	pub fn is_misplaced(&self, weight_of: impl Fn(&T::AccountId) -> VoteWeight) -> bool {
		notional_bag_for::<T>(weight_of(&self.voter.id)) != self.bag_upper
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

	/// Get the upper threshold of the bag that this node _should_ be in, given its vote weight.
	///
	/// This is a helper intended only for benchmarking and should not be used in production.
	#[cfg(any(test, feature = "runtime-benchmarks"))]
	pub fn proper_bag_for(&self) -> VoteWeight {
		let weight_of = crate::Pallet::<T>::weight_of_fn();
		let current_weight = weight_of(&self.voter.id);
		notional_bag_for::<T>(current_weight)
	}

	/// Get the underlying voter.
	#[cfg(any(test, feature = "runtime-benchmarks"))]
	pub fn voter(&self) -> &Voter<T::AccountId> {
		&self.voter
	}
}

/// Fundamental information about a voter.
#[derive(Clone, Encode, Decode, PartialEq, Eq, PartialOrd, Ord, sp_runtime::RuntimeDebug)]
pub struct Voter<AccountId> {
	/// Account Id of this voter
	pub id: AccountId,
	/// Whether the voter is a validator or nominator
	pub voter_type: VoterType,
}

impl<AccountId> Voter<AccountId> {
	pub fn nominator(id: AccountId) -> Self {
		Self { id, voter_type: VoterType::Nominator }
	}

	pub fn validator(id: AccountId) -> Self {
		Self { id, voter_type: VoterType::Validator }
	}
}

/// Type of voter.
///
/// Similar to [`crate::StakerStatus`], but somewhat more limited.
#[derive(Clone, Copy, Encode, Decode, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum VoterType {
	Validator,
	Nominator,
}

/// Compute the existential weight for the specified configuration.
///
/// Note that this value depends on the current issuance, a quantity known to change over time.
/// This makes the project of computing a static value suitable for inclusion in a static,
/// generated file _excitingly unstable_.
#[cfg(any(feature = "std", feature = "make-bags"))]
pub fn existential_weight<T: Config>() -> VoteWeight {
	use frame_support::traits::{Currency, CurrencyToVote};

	let existential_deposit = <T::Currency as Currency<AccountIdOf<T>>>::minimum_balance();
	let issuance = <T::Currency as Currency<AccountIdOf<T>>>::total_issuance();
	T::CurrencyToVote::to_vote(existential_deposit, issuance)
}

/// Support code to ease the process of generating voter bags.
///
/// The process of adding voter bags to a runtime requires only four steps.
///
/// 1. Update the runtime definition.
///
///    ```ignore
///    parameter_types!{
///         pub const VoterBagThresholds: &'static [u64] = &[];
///    }
///
///    impl pallet_staking::Config for Runtime {
///         // <snip>
///         type VoterBagThresholds = VoterBagThresholds;
///    }
///    ```
///
/// 2. Write a little program to generate the definitions. This can be a near-identical copy of
///    `substrate/node/runtime/voter-bags`. This program exists only to hook together the runtime
///    definitions with the various calculations here.
///
/// 3. Run that program:
///
///    ```sh,notrust
///    $ cargo run -p node-runtime-voter-bags -- bin/node/runtime/src/voter_bags.rs
///    ```
///
/// 4. Update the runtime definition.
///
///    ```diff,notrust
///    + mod voter_bags;
///    - pub const VoterBagThresholds: &'static [u64] = &[];
///    + pub const VoterBagThresholds: &'static [u64] = &voter_bags::THRESHOLDS;
///    ```
#[cfg(feature = "make-bags")]
pub mod make_bags {
	use crate::{voter_bags::existential_weight, Config};
	use frame_election_provider_support::VoteWeight;
	use frame_support::traits::Get;
	use std::{
		io::Write,
		path::{Path, PathBuf},
	};

	/// Return the path to a header file used in this repository if is exists.
	///
	/// Just searches the git working directory root for files matching certain patterns; it's
	/// pretty naive.
	fn path_to_header_file() -> Option<PathBuf> {
		let repo = git2::Repository::open_from_env().ok()?;
		let workdir = repo.workdir()?;
		for file_name in &["HEADER-APACHE2", "HEADER-GPL3", "HEADER", "file_header.txt"] {
			let path = workdir.join(file_name);
			if path.exists() {
				return Some(path)
			}
		}
		None
	}

	/// Create an underscore formatter: a formatter which inserts `_` every 3 digits of a number.
	fn underscore_formatter() -> num_format::CustomFormat {
		num_format::CustomFormat::builder()
			.grouping(num_format::Grouping::Standard)
			.separator("_")
			.build()
			.expect("format described here meets all constraints")
	}

	/// Compute the constant ratio for the thresholds.
	///
	/// This ratio ensures that each bag, with the possible exceptions of certain small ones and the
	/// final one, is a constant multiple of the previous, while fully occupying the `VoteWeight`
	/// space.
	pub fn constant_ratio(existential_weight: VoteWeight, n_bags: usize) -> f64 {
		((VoteWeight::MAX as f64 / existential_weight as f64).ln() / ((n_bags - 1) as f64)).exp()
	}

	/// Compute the list of bag thresholds.
	///
	/// Returns a list of exactly `n_bags` elements, except in the case of overflow.
	/// The first element is always `existential_weight`.
	/// The last element is always `VoteWeight::MAX`.
	///
	/// All other elements are computed from the previous according to the formula
	/// `threshold[k + 1] = (threshold[k] * ratio).max(threshold[k] + 1);
	pub fn thresholds(
		existential_weight: VoteWeight,
		constant_ratio: f64,
		n_bags: usize,
	) -> Vec<VoteWeight> {
		const WEIGHT_LIMIT: f64 = VoteWeight::MAX as f64;

		let mut thresholds = Vec::with_capacity(n_bags);

		if n_bags > 1 {
			thresholds.push(existential_weight);
		}

		while n_bags > 0 && thresholds.len() < n_bags - 1 {
			let last = thresholds.last().copied().unwrap_or(existential_weight);
			let successor = (last as f64 * constant_ratio).round().max(last as f64 + 1.0);
			if successor < WEIGHT_LIMIT {
				thresholds.push(successor as VoteWeight);
			} else {
				eprintln!("unexpectedly exceeded weight limit; breaking threshold generation loop");
				break
			}
		}

		thresholds.push(VoteWeight::MAX);

		debug_assert_eq!(thresholds.len(), n_bags);
		debug_assert!(n_bags == 0 || thresholds[0] == existential_weight);
		debug_assert!(n_bags == 0 || thresholds[thresholds.len() - 1] == VoteWeight::MAX);

		thresholds
	}

	/// Write a thresholds module to the path specified.
	///
	/// The `output` path should terminate with a Rust module name, i.e. `foo/bar/thresholds.rs`.
	///
	/// This generated module contains, in order:
	///
	/// - The contents of the header file in this repository's root, if found.
	/// - Module documentation noting that this is autogenerated and when.
	/// - Some associated constants.
	/// - The constant array of thresholds.
	pub fn generate_thresholds_module<T: Config>(
		n_bags: usize,
		output: &Path,
	) -> Result<(), std::io::Error> {
		// ensure the file is accessable
		if let Some(parent) = output.parent() {
			if !parent.exists() {
				std::fs::create_dir_all(parent)?;
			}
		}

		// copy the header file
		if let Some(header_path) = path_to_header_file() {
			std::fs::copy(header_path, output)?;
		}

		// open an append buffer
		let file = std::fs::OpenOptions::new().create(true).append(true).open(output)?;
		let mut buf = std::io::BufWriter::new(file);

		// create underscore formatter and format buffer
		let mut num_buf = num_format::Buffer::new();
		let format = underscore_formatter();

		// module docs
		let now = chrono::Utc::now();
		writeln!(buf)?;
		writeln!(buf, "//! Autogenerated voter bag thresholds.")?;
		writeln!(buf, "//!")?;
		writeln!(buf, "//! Generated on {}", now.to_rfc3339())?;
		writeln!(
			buf,
			"//! for the {} runtime.",
			<T as frame_system::Config>::Version::get().spec_name,
		)?;

		// existential weight
		let existential_weight = existential_weight::<T>();
		num_buf.write_formatted(&existential_weight, &format);
		writeln!(buf)?;
		writeln!(buf, "/// Existential weight for this runtime.")?;
		writeln!(buf, "#[cfg(any(test, feature = \"std\"))]")?;
		writeln!(buf, "#[allow(unused)]")?;
		writeln!(buf, "pub const EXISTENTIAL_WEIGHT: u64 = {};", num_buf.as_str())?;

		// constant ratio
		let constant_ratio = constant_ratio(existential_weight, n_bags);
		writeln!(buf)?;
		writeln!(buf, "/// Constant ratio between bags for this runtime.")?;
		writeln!(buf, "#[cfg(any(test, feature = \"std\"))]")?;
		writeln!(buf, "#[allow(unused)]")?;
		writeln!(buf, "pub const CONSTANT_RATIO: f64 = {:.16};", constant_ratio)?;

		// thresholds
		let thresholds = thresholds(existential_weight, constant_ratio, n_bags);
		writeln!(buf)?;
		writeln!(buf, "/// Upper thresholds delimiting the bag list.")?;
		writeln!(buf, "pub const THRESHOLDS: [u64; {}] = [", thresholds.len())?;
		for threshold in thresholds {
			num_buf.write_formatted(&threshold, &format);
			// u64::MAX, with spacers every 3 digits, is 26 characters wide
			writeln!(buf, "	{:>26},", num_buf.as_str())?;
		}
		writeln!(buf, "];")?;

		Ok(())
	}
}

// This is the highest level of abstraction provided by this module. More generic tests are here,
// among those related to `VoterList` struct.
#[cfg(test)]
mod voter_list {
	use super::*;
	use crate::mock::*;
	use frame_support::{assert_ok, assert_storage_noop, traits::Currency};

	#[test]
	fn basic_setup_works() {
		use crate::{
			CounterForNominators, CounterForValidators, CounterForVoters, VoterBags, VoterNodes,
		};
		let node = |voter, prev, next| Node::<Test> { voter, prev, next, bag_upper: 0 };

		// make sure ALL relevant data structures are setup correctly.
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(CounterForVoters::<Test>::get(), 4);
			assert_eq!(VoterBagFor::<Test>::iter().count(), 4);
			assert_eq!(VoterNodes::<Test>::iter().count(), 4);
			assert_eq!(VoterBags::<Test>::iter().count(), 2);
			assert_eq!(CounterForValidators::<Test>::get(), 3);
			assert_eq!(CounterForNominators::<Test>::get(), 1);

			assert_eq!(
				VoterBags::<Test>::get(10).unwrap(),
				Bag::<Test> { head: Some(31), tail: Some(31), bag_upper: 0 }
			);
			assert_eq!(
				VoterBags::<Test>::get(1_000).unwrap(),
				Bag::<Test> { head: Some(11), tail: Some(101), bag_upper: 0 }
			);

			let weight_of = Staking::weight_of_fn();

			assert_eq!(weight_of(&11), 1000);
			assert_eq!(VoterBagFor::<Test>::get(11).unwrap(), 1000);
			assert_eq!(
				VoterNodes::<Test>::get(11).unwrap(),
				node(Voter::validator(11), None, Some(21))
			);

			assert_eq!(weight_of(&21), 1000);
			assert_eq!(VoterBagFor::<Test>::get(21).unwrap(), 1000);
			assert_eq!(
				VoterNodes::<Test>::get(21).unwrap(),
				node(Voter::validator(21), Some(11), Some(101))
			);

			assert_eq!(weight_of(&31), 1);
			assert_eq!(VoterBagFor::<Test>::get(31).unwrap(), 10);
			assert_eq!(
				VoterNodes::<Test>::get(31).unwrap(),
				node(Voter::validator(31), None, None)
			);

			assert_eq!(weight_of(&41), 1000);
			assert_eq!(VoterBagFor::<Test>::get(41), None); // this staker is chilled!
			assert_eq!(VoterNodes::<Test>::get(41), None);

			assert_eq!(weight_of(&101), 500);
			assert_eq!(VoterBagFor::<Test>::get(101).unwrap(), 1000);
			assert_eq!(
				VoterNodes::<Test>::get(101).unwrap(),
				node(Voter::nominator(101), Some(21), None)
			);

			// iteration of the bags would yield:
			assert_eq!(
				VoterList::<Test>::iter().map(|n| n.voter().id).collect::<Vec<_>>(),
				vec![11, 21, 101, 31],
				//   ^^ note the order of insertion in genesis!
			);

			assert_eq!(get_bags(), vec![(10, vec![31]), (1000, vec![11, 21, 101])],);
		})
	}

	#[test]
	fn notional_bag_for_works() {
		// under a threshold gives the next threshold.
		assert_eq!(notional_bag_for::<Test>(0), 10);
		assert_eq!(notional_bag_for::<Test>(9), 10);
		assert_eq!(notional_bag_for::<Test>(11), 20);

		// at a threshold gives that threshold.
		assert_eq!(notional_bag_for::<Test>(10), 10);

		let max_explicit_threshold = *<Test as Config>::VoterBagThresholds::get().last().unwrap();
		assert_eq!(max_explicit_threshold, 10_000);
		// if the max explicit threshold is less than VoteWeight::MAX,
		assert!(VoteWeight::MAX > max_explicit_threshold);
		// anything above it will belong to the VoteWeight::MAX bag.
		assert_eq!(notional_bag_for::<Test>(max_explicit_threshold + 1), VoteWeight::MAX);
	}

	#[test]
	fn iteration_is_semi_sorted() {
		ExtBuilder::default().build_and_execute(|| {
			// add some new validators to the genesis state.
			bond_validator(51, 50, 2000);
			bond_validator(61, 60, 2000);

			// given
			assert_eq!(
				get_bags(),
				vec![(10, vec![31]), (1000, vec![11, 21, 101]), (2000, vec![51, 61])],
			);

			// when
			let iteration = VoterList::<Test>::iter().map(|node| node.voter.id).collect::<Vec<_>>();

			// then
			assert_eq!(
				iteration,
				vec![
					51, 61, // best bag
					11, 21, 101, // middle bag
					31,  // last bag.
				]
			);

			// when adding a voter that has a higher weight than pre-existing voters in the bag
			bond_validator(71, 70, 10);

			// then
			assert_eq!(
				iteration,
				vec![
					51, 61, // best bag
					11, 21, 101, // middle bag
					31,
					71, // last bag; the new voter is last, because it is order of insertion
				]
			);
		})
	}

	/// This tests that we can `take` x voters, even if that quantity ends midway through a list.
	#[test]
	fn take_works() {
		ExtBuilder::default().build_and_execute(|| {
			// add some new validators to the genesis state.
			bond_validator(51, 50, 2000);
			bond_validator(61, 60, 2000);

			// given
			assert_eq!(
				get_bags(),
				vec![(10, vec![31]), (1000, vec![11, 21, 101]), (2000, vec![51, 61])],
			);

			// when
			let iteration =
				VoterList::<Test>::iter().map(|node| node.voter.id).take(4).collect::<Vec<_>>();

			// then
			assert_eq!(
				iteration,
				vec![
					51, 61, // best bag, fully iterated
					11, 21, // middle bag, partially iterated
				]
			);
		})
	}

	#[test]
	fn insert_works() {
		ExtBuilder::default().build_and_execute_without_check_count(|| {
			// when inserting into an existing bag
			bond(42, 43, 1_000);
			VoterList::<Test>::insert(Voter::<_>::nominator(42), Pallet::<Test>::weight_of_fn());

			// then
			assert_eq!(get_voter_list_as_ids(), vec![11, 21, 101, 42, 31]);
			assert_eq!(get_bags(), vec![(10, vec![31]), (1_000, vec![11, 21, 101, 42])]);

			// when inserting into a non-existent bag
			bond(422, 433, 1_001);
			VoterList::<Test>::insert(Voter::<_>::nominator(422), Pallet::<Test>::weight_of_fn());

			// then
			assert_eq!(get_voter_list_as_ids(), vec![422, 11, 21, 101, 42, 31]);
			assert_eq!(
				get_bags(),
				vec![(10, vec![31]), (1_000, vec![11, 21, 101, 42]), (2_000, vec![422])]
			);
		});
	}

	#[test]
	fn insert_as_works() {
		ExtBuilder::default().build_and_execute_without_check_count(|| {
			// given
			let actual = get_voter_list_as_voters();
			let mut expected: Vec<Voter<u64>> = vec![
				Voter::<_>::validator(11),
				Voter::<_>::validator(21),
				Voter::<_>::nominator(101),
				Voter::<_>::validator(31),
			];
			assert_eq!(actual, expected);

			// when inserting a new voter
			VoterList::<Test>::insert_as(&42, VoterType::Nominator);

			// then
			let actual = get_voter_list_as_voters();
			expected.push(Voter::<_>::nominator(42));
			assert_eq!(actual, expected);

			// when updating the voter type of an already existing voter
			VoterList::<Test>::insert_as(&42, VoterType::Validator);

			// then
			let actual = get_voter_list_as_voters();
			expected[4] = Voter::<_>::validator(42);
			assert_eq!(actual, expected);
		});
	}

	#[test]
	fn remove_works() {
		use crate::{CounterForVoters, VoterNodes};

		let check_storage = |id, counter, voters, bags| {
			assert!(!VoterBagFor::<Test>::contains_key(id));
			assert!(!VoterNodes::<Test>::contains_key(id));
			assert_eq!(CounterForVoters::<Test>::get(), counter);
			assert_eq!(VoterBagFor::<Test>::iter().count() as u32, counter);
			assert_eq!(VoterNodes::<Test>::iter().count() as u32, counter);
			assert_eq!(get_voter_list_as_ids(), voters);
			assert_eq!(get_bags(), bags);
		};

		ExtBuilder::default().build_and_execute_without_check_count(|| {
			// when removing a non-existent voter
			VoterList::<Test>::remove(&42);
			assert!(!VoterBagFor::<Test>::contains_key(42));
			assert!(!VoterNodes::<Test>::contains_key(42));

			// then nothing changes
			assert_eq!(get_voter_list_as_ids(), vec![11, 21, 101, 31]);
			assert_eq!(get_bags(), vec![(10, vec![31]), (1_000, vec![11, 21, 101])]);
			assert_eq!(CounterForVoters::<Test>::get(), 4);

			// when removing a node from a bag with multiple nodes
			VoterList::<Test>::remove(&11);

			// then
			assert_eq!(get_voter_list_as_ids(), vec![21, 101, 31]);
			check_storage(
				11,
				3,
				vec![21, 101, 31],                            // voter list
				vec![(10, vec![31]), (1_000, vec![21, 101])], // bags
			);

			// when removing a node from a bag with only one node:
			VoterList::<Test>::remove(&31);

			// then
			assert_eq!(get_voter_list_as_ids(), vec![21, 101]);
			check_storage(
				31,
				2,
				vec![21, 101], // voter list
				vec![
					// bags
					(10, vec![]), // the bag itself is not cleaned up from storage, which is ok
					(1_000, vec![21, 101]),
				],
			);

			// remove remaining voters to make sure storage cleans up as expected
			VoterList::<Test>::remove(&21);
			check_storage(
				21,
				1,
				vec![101],                              // voter list
				vec![(10, vec![]), (1_000, vec![101])], // bags
			);

			VoterList::<Test>::remove(&101);
			check_storage(
				101,
				0,
				Vec::<u64>::new(),                   // voter list
				vec![(10, vec![]), (1_000, vec![])], // bags
			);

			// bags are not deleted via removals
			assert_eq!(crate::VoterBags::<Test>::iter().count(), 2);
			// nominator and validator counters are not updated at this level of the api
			assert_eq!(crate::CounterForValidators::<Test>::get(), 3);
			assert_eq!(crate::CounterForNominators::<Test>::get(), 1);

		});
	}

	#[test]
	fn update_position_for_works() {
		ExtBuilder::default().build_and_execute_without_check_count(|| {
			let weight_of = Staking::weight_of_fn();

			// given a correctly placed account 31
			let node_31 = Node::<Test>::from_id(&31).unwrap();
			assert!(!node_31.is_misplaced(&weight_of));

			// when account 31 bonds extra and needs to be moved to a non-existing higher bag
			// (we can't call bond_extra, because that implicitly calls update_position_for)
			set_ledger_and_free_balance(&31, 11);

			assert!(node_31.is_misplaced(&weight_of));
			assert_eq!(weight_of(&31), 11);

			// then updating position moves it to the correct bag
			assert_eq!(VoterList::<Test>::update_position_for(node_31, &weight_of), Some((10, 20)));
			assert_eq!(get_bags(), vec![(10, vec![]), (20, vec![31]), (1_000, vec![11, 21, 101])]);
			assert_eq!(get_voter_list_as_ids(), vec![11, 21, 101, 31]);

			// and if you try and update the position with no change in active stake nothing changes
			let node_31 = Node::<Test>::from_id(&31).unwrap();
			assert_storage_noop!(assert_eq!(
				VoterList::<Test>::update_position_for(node_31, &weight_of),
				None,
			));

			// when account 31 bonds extra and needs to be moved to an existing higher bag
			set_ledger_and_free_balance(&31, 61);

			// then updating positions moves it to the correct bag
			let node_31 = Node::<Test>::from_id(&31).unwrap();
			assert_eq!(
				VoterList::<Test>::update_position_for(node_31, &weight_of),
				Some((20, 1_000))
			);
			assert_eq!(
				get_bags(),
				vec![(10, vec![]), (20, vec![]), (1_000, vec![11, 21, 101, 31])]
			);
			assert_eq!(get_voter_list_as_ids(), vec![11, 21, 101, 31]);

			// when account 31 bonds extra but should not change bags
			set_ledger_and_free_balance(&31, 1_000);

			// then nothing changes
			let node_31 = Node::<Test>::from_id(&31).unwrap();
			assert_storage_noop!(assert_eq!(
				VoterList::<Test>::update_position_for(node_31, &weight_of),
				None,
			));
		});
	}

	// TODO: should probs remove this; Just wanted to document an edge case
	// I ran into where I read in a node, called bond_extra, and then called
	// update_position_for(node). The underlying issue is we insert a node with
	// the same ID twice.
	// When we insert we set node.prev = tail.id
	// and then old_tail.next = node.id. Which creates a cycle since old_tail
	// was the same node
	// tl;dr, don't insert the same id into a bag twice, especially if its tail
	// cover this explicitly in insert_node_bad_paths_documented
	#[test]
	fn node_reference_invalid_after_implicit_update_position() {
		ExtBuilder::default().build_and_execute_without_check_count(|| {
			let weight_of = Staking::weight_of_fn();

			// starts out in the correct place.
			let node_31 = Node::<Test>::from_id(&31).unwrap();
			assert!(!node_31.is_misplaced(&weight_of));

			Balances::make_free_balance_be(&31, 11);
			// when we call bond_extra
			assert_ok!(Staking::bond_extra(Origin::signed(31), 11));

			// then now the reference is outdated
			assert!(node_31.is_misplaced(&weight_of));
			// but we can expect the list is correct
			assert_eq!(get_bags(), vec![(10, vec![]), (20, vec![31]), (1_000, vec![11, 21, 101])]);
			assert_eq!(get_voter_list_as_ids(), vec![11, 21, 101, 31]);

			assert_eq!(VoterList::<Test>::update_position_for(node_31, &weight_of), Some((10, 20)));

			let bag = Bag::<Test>::get(20).unwrap();
			// there is a cycle,
			// the bags head/tail are the same node, and that node has its own
			// id for prev & next so when we iterate we will infinitely keep
			// reading the same node from storage.
			assert_eq!(
				bag.head().unwrap().voter().id,
				bag.head().unwrap().next().unwrap().voter().id
			);
			assert_eq!(
				bag.head().unwrap().voter().id,
				bag.head().unwrap().prev().unwrap().voter().id
			);
			assert_eq!(bag.head().unwrap().voter().id, bag.tail().unwrap().voter().id,)
		});
	}
}

#[cfg(test)]
mod bags {
	use super::*;
	use crate::mock::*;
	use frame_support::{assert_ok, assert_storage_noop};

	#[test]
	fn get_works() {
		use crate::VoterBags;
		ExtBuilder::default().build_and_execute_without_check_count(|| {
			let check_bag = |bag_upper, head, tail, ids| {
				assert_storage_noop!(Bag::<Test>::get(bag_upper));

				let bag = Bag::<Test>::get(bag_upper).unwrap();
				let bag_ids = bag.iter().map(|n| n.voter().id).collect::<Vec<_>>();

				assert_eq!(bag, Bag::<Test> { head, tail, bag_upper });
				assert_eq!(bag_ids, ids);
			};

			// given uppers of bags that exist.
			let existing_bag_uppers = vec![10, 1_000];

			// we can fetch them
			check_bag(existing_bag_uppers[0], Some(31), Some(31), vec![31]);
			// (getting the same bag twice has the same results)
			check_bag(existing_bag_uppers[0], Some(31), Some(31), vec![31]);
			check_bag(existing_bag_uppers[1], Some(11), Some(101), vec![11, 21, 101]);

			// and all other uppers don't get bags.
			<Test as Config>::VoterBagThresholds::get()
				.iter()
				.chain(iter::once(&VoteWeight::MAX))
				.filter(|bag_upper| !existing_bag_uppers.contains(bag_upper))
				.for_each(|bag_upper| {
					assert_storage_noop!(assert_eq!(Bag::<Test>::get(*bag_upper), None));
					assert!(!VoterBags::<Test>::contains_key(*bag_upper));
				});

			// when we make a pre-existing bag empty
			VoterList::<Test>::remove(&31);

			// then
			check_bag(existing_bag_uppers[0], None, None, vec![]);
		});
	}

	#[test]
	#[should_panic]
	fn get_panics_with_a_bad_threshold() {
		// NOTE: panic is only expected with debug compilation
		ExtBuilder::default().build_and_execute_without_check_count(|| {
			Bag::<Test>::get(11);
		});
	}

	#[test]
	fn insert_node_happy_paths_works() {
		ExtBuilder::default().build_and_execute_without_check_count(|| {
			let node = |voter, bag_upper| Node::<Test> { voter, prev: None, next: None, bag_upper };

			// when inserting into a bag with 1 node
			let mut bag_10 = Bag::<Test>::get(10).unwrap();
			// (note: bags api does not care about balance or ledger)
			bag_10.insert_node(node(Voter::nominator(42), bag_10.bag_upper));
			// then
			assert_eq!(bag_as_ids(&bag_10), vec![31, 42]);

			// when inserting into a bag with 3 nodes
			let mut bag_1000 = Bag::<Test>::get(1_000).unwrap();
			bag_1000.insert_node(node(Voter::nominator(52), bag_1000.bag_upper));
			// then
			assert_eq!(bag_as_ids(&bag_1000), vec![11, 21, 101, 52]);

			// when inserting into a new bag
			let mut bag_20 = Bag::<Test>::get_or_make(20);
			bag_20.insert_node(node(Voter::nominator(71), bag_20.bag_upper));
			// then
			assert_eq!(bag_as_ids(&bag_20), vec![71]);

			// when inserting a node pointing to the accounts not in the bag
			let voter_61 = Voter::validator(61);
			let node_61 = Node::<Test> {
				voter: voter_61.clone(),
				prev: Some(21),
				next: Some(101),
				bag_upper: 20,
			};
			bag_20.insert_node(node_61);
			// then ids are in order
			assert_eq!(bag_as_ids(&bag_20), vec![71, 61]);
			// and when the node is re-fetched all the info is correct
			assert_eq!(
				Node::<Test>::get(20, &61).unwrap(),
				Node::<Test> { voter: voter_61, prev: Some(71), next: None, bag_upper: 20 }
			);

			// state of all bags is as expected
			bag_20.put(); // need to put this bag so its in the storage map
			assert_eq!(
				get_bags(),
				vec![(10, vec![31, 42]), (20, vec![71, 61]), (1_000, vec![11, 21, 101, 52])]
			);
		});
	}

	// Document improper ways `insert_node` may be getting used.
	#[test]
	fn insert_node_bad_paths_documented() {
		ExtBuilder::default().build_and_execute_without_check_count(|| {
			let node = |voter, prev, next, bag_upper| Node::<Test> { voter, prev, next, bag_upper };
			// insert some validators into genesis state
			bond_validator(51, 50, 2_000);
			bond_validator(61, 60, 2_000);
			bond_validator(71, 70, 2_000);

			// given
			assert_eq!(
				get_bags(),
				vec![(10, vec![31]), (1000, vec![11, 21, 101]), (2000, vec![51, 61, 71])],
			);

			// when inserting a node with both prev & next pointing at an account in the bag
			// and an incorrect bag_upper
			let mut bag_1000 = Bag::<Test>::get(1_000).unwrap();
			let voter_42 = Voter::nominator(42);
			bag_1000.insert_node(node(voter_42.clone(), Some(11), Some(11), 0));
			// then the ids are in the correct order
			assert_eq!(bag_as_ids(&bag_1000), vec![11, 21, 101, 42]);
			// and when the node is re-fetched all the info is correct
			assert_eq!(
				Node::<Test>::get(1_000, &42).unwrap(),
				node(voter_42, Some(101), None, bag_1000.bag_upper)
			);

			// given 21 is a validator in bag_1000 (and not a tail node)
			let bag_1000_voter =
				bag_1000.iter().map(|node| node.voter().clone()).collect::<Vec<_>>();
			assert_eq!(bag_1000_voter[1], Voter::<_>::validator(21));
			// when inserting a node with duplicate id 21 but as a nominator
			let voter_21_nom = Voter::<_>::nominator(21);
			bag_1000.insert_node(node(voter_21_nom.clone(), None, None, bag_1000.bag_upper));
			// then all the nodes after the duplicate are lost (because it is set as the tail)
			assert_eq!(bag_as_ids(&bag_1000), vec![11, 21]);
			// and the re-fetched node is a nominator with an **incorrect** prev pointer.
			assert_eq!(
				Node::<Test>::get(1_000, &21).unwrap(),
				node(voter_21_nom, Some(42), None, bag_1000.bag_upper)
			);

			// TODO: this exact issue could be avoided at this level of abstraction if we check if
			// an id is already the bags tail before inserting

			// given a bag we are confident is in valid state
			let mut bag_2000 = Bag::<Test>::get(2_000).unwrap();
			assert_eq!(bag_as_ids(&bag_2000), vec![51, 61, 71]);
			// when inserting a duplicate id that is already the tail
			assert_eq!(bag_2000.tail, Some(71));
			let voter_71 = Voter::<_>::validator(71);
			bag_2000.insert_node(node(voter_71.clone(), None, None, bag_2000.bag_upper));
			// then a cycle is created
			assert_eq!(bag_2000.tail, Some(71));
			assert_eq!(
				Node::<Test>::get(2_000, &71).unwrap(),
				node(voter_71, Some(71), Some(71), bag_2000.bag_upper)
			);
		})
	}

	#[test]
	fn remove_node_happy_paths_works() {
		ExtBuilder::default().build_and_execute_without_check_count(|| {
			// add some validators to genesis state
			bond_validator(51, 50, 1_000);
			bond_validator(61, 60, 1_000);
			bond_validator(71, 70, 10);
			bond_validator(81, 80, 10);
			bond_validator(91, 90, 2_000);
			bond_validator(161, 160, 2_000);
			bond_validator(171, 170, 2_000);
			bond_validator(181, 180, 2_000);
			bond_validator(191, 190, 2_000);

			let mut bag_10 = Bag::<Test>::get(10).unwrap();
			let mut bag_1000 = Bag::<Test>::get(1_000).unwrap();
			let mut bag_2000 = Bag::<Test>::get(2_000).unwrap();

			// given
			assert_eq!(bag_as_ids(&bag_10), vec![31, 71, 81]);
			assert_eq!(bag_as_ids(&bag_1000), vec![11, 21, 101, 51, 61]);
			assert_eq!(bag_as_ids(&bag_2000), vec![91, 161, 171, 181, 191]);

			// remove node that is not pointing at head or tail
			let node_101 = Node::<Test>::get(bag_1000.bag_upper, &101).unwrap();
			let node_101_pre_remove = node_101.clone();
			bag_1000.remove_node(&node_101);
			assert_eq!(bag_as_ids(&bag_1000), vec![11, 21, 51, 61]);
			assert_ok!(bag_1000.sanity_check());
			// node isn't mutated when its removed
			assert_eq!(node_101, node_101_pre_remove);

			// remove head when its not pointing at tail
			let node_11 = Node::<Test>::get(bag_1000.bag_upper, &11).unwrap();
			bag_1000.remove_node(&node_11);
			assert_eq!(bag_as_ids(&bag_1000), vec![21, 51, 61]);
			assert_ok!(bag_1000.sanity_check());

			// remove tail when its not pointing at head
			let node_61 = Node::<Test>::get(bag_1000.bag_upper, &61).unwrap();
			bag_1000.remove_node(&node_61);
			assert_eq!(bag_as_ids(&bag_1000), vec![21, 51]);
			assert_ok!(bag_1000.sanity_check());

			// remove tail when its pointing at head
			let node_51 = Node::<Test>::get(bag_1000.bag_upper, &51).unwrap();
			bag_1000.remove_node(&node_51);
			assert_eq!(bag_as_ids(&bag_1000), vec![21]);
			assert_ok!(bag_1000.sanity_check());

			// remove node that is head & tail
			let node_21 = Node::<Test>::get(bag_1000.bag_upper, &21).unwrap();
			bag_1000.remove_node(&node_21);
			assert_eq!(bag_as_ids(&bag_1000), Vec::<u64>::new());
			assert_ok!(bag_1000.sanity_check());

			// remove node that is pointing at head and tail
			let node_71 = Node::<Test>::get(bag_10.bag_upper, &71).unwrap();
			bag_10.remove_node(&node_71);
			assert_eq!(bag_as_ids(&bag_10), vec![31, 81]);
			assert_ok!(bag_10.sanity_check());

			// remove head when pointing at tail
			let node_31 = Node::<Test>::get(bag_10.bag_upper, &31).unwrap();
			bag_10.remove_node(&node_31);
			assert_eq!(bag_as_ids(&bag_10), vec![81]);
			assert_ok!(bag_10.sanity_check());

			// remove node that is pointing at head, but not tail
			let node_161 = Node::<Test>::get(bag_2000.bag_upper, &161).unwrap();
			bag_2000.remove_node(&node_161);
			assert_eq!(bag_as_ids(&bag_2000), vec![91, 171, 181, 191]);
			assert_ok!(bag_2000.sanity_check());

			// remove node that is pointing at tail, but not head
			let node_181 = Node::<Test>::get(bag_2000.bag_upper, &181).unwrap();
			bag_2000.remove_node(&node_181);
			assert_eq!(bag_as_ids(&bag_2000), vec![91, 171, 191]);
			assert_ok!(bag_2000.sanity_check());

			// state of all bags is as expected
			assert_eq!(
				get_bags(),
				vec![(10, vec![81]), (1_000, vec![]), (2_000, vec![91, 171, 191])]
			);
		});
	}

	#[test]
	fn remove_node_bad_paths_documented() {
		ExtBuilder::default().build_and_execute_without_check_count(|| {
			// removing a node that is in the bag but has the wrong upper works.

			let bad_upper_node_11 = Node::<Test> {
				voter: Voter::<_>::validator(11),
				prev: None,
				next: Some(21),
				bag_upper: 10, // should be 1_000
			};
			let mut bag_1000 = Bag::<Test>::get(1_000).unwrap();
			bag_1000.remove_node(&bad_upper_node_11);
			bag_1000.put();

			assert_eq!(get_bags(), vec![(10, vec![31]), (1_000, vec![21, 101])]);
			let bag_1000 = Bag::<Test>::get(1_000).unwrap();
			assert_ok!(bag_1000.sanity_check());
			assert_eq!(bag_1000.head, Some(21));
			assert_eq!(bag_1000.tail, Some(101));
		});

		ExtBuilder::default().build_and_execute_without_check_count(|| {
			// removing a node that is in another bag, will mess up the
			// other bag.

			let node_101 = Node::<Test>::get(1_000, &101).unwrap();
			let mut bag_10 = Bag::<Test>::get(10).unwrap();
			bag_10.remove_node(&node_101); // node_101 is in bag 1_000
			bag_10.put();

			// the node was removed from its actual bag, bag_1000.
			assert_eq!(get_bags(), vec![(10, vec![31]), (1_000, vec![11, 21])]);

			// the bag removed was called on is ok.
			let bag_10 = Bag::<Test>::get(10).unwrap();
			assert_eq!(bag_10.tail, Some(31));
			assert_eq!(bag_10.head, Some(31));

			// but the bag that the node belonged to is in an invalid state
			let bag_1000 = Bag::<Test>::get(1_000).unwrap();
			// because it still has the removed node as its tail.
			assert_eq!(bag_1000.tail, Some(101));
			assert_eq!(bag_1000.head, Some(11));
			assert_ok!(bag_1000.sanity_check());
		});
	}
}

#[cfg(test)]
mod voter_node {
	use super::*;
	use crate::mock::*;

	#[test]
	fn voting_data_works() {
		ExtBuilder::default().build_and_execute_without_check_count(|| {
			let weight_of = Staking::weight_of_fn();

			// add nominator with no targets
			bond_nominator(42, 43, 1_000, vec![11]);

			// given
			assert_eq!(
				get_voter_list_as_voters(),
				vec![
					Voter::validator(11),
					Voter::validator(21),
					Voter::nominator(101),
					Voter::nominator(42),
					Voter::validator(31),
				]
			);
			assert_eq!(active_era(), 0);

			let slashing_spans =
				<Staking as crate::Store>::SlashingSpans::iter().collect::<BTreeMap<_, _>>();
			assert_eq!(slashing_spans.keys().len(), 0); // no pre-existing slashing spans

			let node_11 = Node::<Test>::get(10, &11).unwrap();
			assert_eq!(
				node_11.voting_data(&weight_of, &slashing_spans).unwrap(),
				(11, 1_000, vec![11])
			);

			// getting data for a nominators with 0 slashed targets
			let node_101 = Node::<Test>::get(1_000, &101).unwrap();
			assert_eq!(
				node_101.voting_data(&weight_of, &slashing_spans).unwrap(),
				(101, 500, vec![11, 21])
			);
			let node_42 = Node::<Test>::get(10, &42).unwrap();
			assert_eq!(
				node_42.voting_data(&weight_of, &slashing_spans).unwrap(),
				(42, 1_000, vec![11])
			);

			// roll ahead an era so any slashes will be after the previous nominations
			start_active_era(1);

			// when a validator gets a slash,
			add_slash(&11);
			let slashing_spans =
				<Staking as crate::Store>::SlashingSpans::iter().collect::<BTreeMap<_, _>>();

			assert_eq!(slashing_spans.keys().cloned().collect::<Vec<_>>(), vec![11, 42, 101]);
			// then its node no longer exists
			assert_eq!(
				get_voter_list_as_voters(),
				vec![
					Voter::validator(21),
					Voter::nominator(101),
					Voter::nominator(42),
					Voter::validator(31),
				]
			);
			// and its nominators no longer have it as a target
			let node_101 = Node::<Test>::get(10, &101).unwrap();
			assert_eq!(
				node_101.voting_data(&weight_of, &slashing_spans),
				Some((101, 475, vec![21])),
			);

			let node_42 = Node::<Test>::get(10, &42).unwrap();
			assert_eq!(
				node_42.voting_data(&weight_of, &slashing_spans),
				None, // no voting data since its 1 target has been slashed since nominating
			);
		});
	}

	#[test]
	fn is_misplaced_works() {
		ExtBuilder::default().build_and_execute_without_check_count(|| {
			let weight_of = Staking::weight_of_fn();
			let node_31 = Node::<Test>::get(10, &31).unwrap();

			// a node is properly placed if its slashable balance is in range
			// of the threshold of the bag its in.
			assert_eq!(Staking::slashable_balance_of(&31), 1);
			assert!(!node_31.is_misplaced(&weight_of));

			// and will become misplaced if its slashable balance does not
			// correspond to the bag it is in.
			set_ledger_and_free_balance(&31, 11);

			assert_eq!(Staking::slashable_balance_of(&31), 11);
			assert!(node_31.is_misplaced(&weight_of));
		});
	}
}
