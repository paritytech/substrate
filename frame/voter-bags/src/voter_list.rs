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

//! VoterList implementation.

use crate::{AccountIdOf, Config};
use codec::{Decode, Encode};
use frame_election_provider_support::VoteWeight;
use frame_support::{ensure, traits::Get, DefaultNoBound};
use pallet_staking as staking;
use sp_runtime::SaturatedConversion;
use sp_std::{
	boxed::Box,
	collections::{btree_map::BTreeMap, btree_set::BTreeSet},
	iter,
	marker::PhantomData,
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
	let thresholds = T::BVoterBagThresholds::get();
	let idx = thresholds.partition_point(|&threshold| weight > threshold);
	thresholds.get(idx).copied().unwrap_or(VoteWeight::MAX)
}

/// Find the upper threshold of the actual bag containing the current voter.
fn current_bag_for<T: Config>(id: &AccountIdOf<T>) -> Option<VoteWeight> {
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

		let nominators_iter = staking::Nominators::<T>::iter().map(|(id, _)| Voter::nominator(id));
		let validators_iter = staking::Validators::<T>::iter().map(|(id, _)| Voter::validator(id));
		let weight_of = staking::Pallet::<T>::weight_of_fn();

		// Self::insert_many(nominators_iter.chain(validators_iter), weight_of)
		1
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
			maybe_len.unwrap_or_default() as u32,
			staking::CounterForNominators::<T>::get() + staking::CounterForValidators::<T>::get(),
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
		let thresholds = T::BVoterBagThresholds::get();
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
			let weight_of = staking::Pallet::<T>::weight_of_fn();
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

				// TODO: there should be a way to move a non-head-tail node to another bag
				// with just 1 bag read of the destination bag and zero writes
				// https://github.com/paritytech/substrate/pull/9468/files/83289aa4a15d61e6cb334f9d7e7f6804cb7e3537..44875c511ebdc79270100720320c8e3d2d56eb4a#r680559166

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
			let weight_of = pallet_staking::Pallet::<T>::weight_of_fn();
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
					!crate::VoterBagFor::<T>::iter().any(|(_voter, bag)| bag == removed_bag),
					"no voter should be present in a removed bag",
				);
				crate::VoterBags::<T>::remove(removed_bag);
			}

			debug_assert!(
				{
					let thresholds = T::BVoterBagThresholds::get();
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
	pub(crate) fn sanity_check() -> Result<(), &'static str> {
		let mut seen_in_list = BTreeSet::new();
		ensure!(
			Self::iter().map(|node| node.voter.id).all(|voter| seen_in_list.insert(voter)),
			"duplicate identified",
		);

		let iter_count = Self::iter().collect::<sp_std::vec::Vec<_>>().len() as u32;
		let stored_count = crate::CounterForVoters::<T>::get();
		ensure!(iter_count == stored_count, "iter_count != voter_count");

		let validators = staking::CounterForValidators::<T>::get();
		let nominators = staking::CounterForNominators::<T>::get();
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
			T::BVoterBagThresholds::get().contains(&bag_upper) || bag_upper == VoteWeight::MAX,
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
			T::BVoterBagThresholds::get().contains(&bag_upper) || bag_upper == VoteWeight::MAX,
			"it is a logic error to attempt to get a bag which is not in the thresholds list"
		);
		Self::get(bag_upper).unwrap_or(Bag { bag_upper, ..Default::default() })
	}

	/// `True` if self is empty.
	pub fn is_empty(&self) -> bool {
		self.head.is_none() && self.tail.is_none()
	}

	/// Put the bag back into storage.
	pub fn put(self) {
		if self.is_empty() {
			crate::VoterBags::<T>::remove(self.bag_upper);
		} else {
			crate::VoterBags::<T>::insert(self.bag_upper, self);
		}
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
		if let Some(tail) = &self.tail {
			if *tail == node.voter.id {
				// this should never happen, but this check prevents a worst case infinite loop
				debug_assert!(false, "system logic error: inserting a node who has the id of tail");
				crate::log!(warn, "system logic error: inserting a node who has the id of tail");
				return
			};
		}

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
			T::BVoterBagThresholds::get().contains(&bag_upper) || bag_upper == VoteWeight::MAX,
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
		slashing_spans: &BTreeMap<AccountIdOf<T>, staking::slashing::SlashingSpans>,
	) -> Option<staking::VotingDataOf<T>> {
		let voter_weight = weight_of(&self.voter.id);
		match self.voter.voter_type {
			VoterType::Validator =>
				Some((self.voter.id.clone(), voter_weight, sp_std::vec![self.voter.id.clone()])),
			VoterType::Nominator => {
				let staking::Nominations { submitted_in, mut targets, .. } =
					staking::Nominators::<T>::get(&self.voter.id)?;
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
