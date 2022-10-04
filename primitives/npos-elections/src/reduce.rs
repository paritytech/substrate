// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Rust implementation of the Phragmén reduce algorithm. This can be used by any off chain
//! application to reduce cycles from the edge assignment, which will result in smaller size.
//!
//!  ### Notions
//!  - `m`: size of the committee to elect.
//!  - `k`: maximum allowed votes (16 as of this writing).
//!  - `nv ∈ E` means that nominator `n ∈ N` supports the election of candidate `v ∈ V`.
//!  - A valid solution consists of a tuple `(S, W)` , where `S ⊆ V` is a committee of m validators,
//!    and `W : E → R ≥ 0` is an edge weight vector which describes how the budget of each nominator
//!    n is fractionally assigned to n 's elected neighbors.
//!  - `E_w := { e ∈ E : w_e > 0 }`.
//!
//!  ### Algorithm overview
//!
//! > We consider the input edge weight vector `w` as a directed flow over `E_w` , where the flow in
//! > each edge is directed from the nominator to the validator. We build `w′` from `w` by removing
//! > **circulations** to cancel out the flow over as many edges as possible, while preserving flow
//! > demands over all vertices and without reverting the flow direction over any edge. As long as
//! > there is a cycle, we can remove an additional circulation and eliminate at least one new edge
//! > from `E_w′` . This shows that the algorithm always progresses and will eventually finish with
//! > an acyclic edge support. We keep a data structure that represents a forest of rooted trees,
//! > which is initialized as a collection of singletons – one per vertex – and to which edges in
//! > `E_w` are added one by one, causing the trees to merge. Whenever a new edge creates a cycle,
//! > we detect it and destroy it by removing a circulation. We also run a pre-computation which is
//! > designed to detect and remove cycles of length four exclusively. This pre-computation is
//! > optional, and if we skip it then the running time becomes `O (|E_w| ⋅ m), so the
//! > pre-computation makes sense only if `m >> k` and `|E_w| >> m^2`.
//!
//! ### Resources:
//!
//! 1. <https://hackmd.io/JOn9x98iS0e0DPWQ87zGWg?view>

use crate::{
	node::{Node, NodeId, NodeRef, NodeRole},
	ExtendedBalance, IdentifierT, StakedAssignment,
};
use sp_arithmetic::traits::{Bounded, Zero};
use sp_std::{
	collections::btree_map::{BTreeMap, Entry::*},
	prelude::*,
	vec,
};

/// Map type used for reduce_4. Can be easily swapped with HashMap.
type Map<A> = BTreeMap<(A, A), A>;

/// Returns all combinations of size two in the collection `input` with no repetition.
fn combinations_2<T: Clone>(input: &[T]) -> Vec<(T, T)> {
	let n = input.len();
	if n < 2 {
		return Default::default()
	}

	let mut comb = Vec::with_capacity(n * (n - 1) / 2);
	for i in 0..n {
		for j in i + 1..n {
			comb.push((input[i].clone(), input[j].clone()))
		}
	}
	comb
}

/// Returns the count of trailing common elements in two slices.
pub(crate) fn trailing_common<T: Eq>(t1: &[T], t2: &[T]) -> usize {
	t1.iter().rev().zip(t2.iter().rev()).take_while(|e| e.0 == e.1).count()
}

/// Merges two parent roots as described by the reduce algorithm.
fn merge<A: IdentifierT>(voter_root_path: Vec<NodeRef<A>>, target_root_path: Vec<NodeRef<A>>) {
	let (shorter_path, longer_path) = if voter_root_path.len() <= target_root_path.len() {
		(voter_root_path, target_root_path)
	} else {
		(target_root_path, voter_root_path)
	};

	// iterate from last to beginning, skipping the first one. This asserts that
	// indexing is always correct.
	shorter_path
		.iter()
		.zip(shorter_path.iter().skip(1))
		.for_each(|(voter, next)| Node::set_parent_of(&next, &voter));
	Node::set_parent_of(&shorter_path[0], &longer_path[0]);
}

/// Reduce only redundant edges with cycle length of 4.
///
/// Returns the number of edges removed.
///
/// It is strictly assumed that the `who` attribute of all provided assignments are unique. The
/// result will most likely be corrupt otherwise.
///
/// O(|E_w| ⋅ k).
fn reduce_4<A: IdentifierT>(assignments: &mut Vec<StakedAssignment<A>>) -> u32 {
	let mut combination_map: Map<A> = Map::new();
	let mut num_changed: u32 = Zero::zero();

	// we have to use the old fashioned loops here with manual indexing. Borrowing assignments will
	// not work since then there is NO way to mutate it inside.
	for assignment_index in 0..assignments.len() {
		let who = assignments[assignment_index].who.clone();

		// all combinations for this particular voter
		let distribution_ids = &assignments[assignment_index]
			.distribution
			.iter()
			.map(|(t, _p)| t.clone())
			.collect::<Vec<A>>();
		let candidate_combinations = combinations_2(distribution_ids);

		for (v1, v2) in candidate_combinations {
			match combination_map.entry((v1.clone(), v2.clone())) {
				Vacant(entry) => {
					entry.insert(who.clone());
				},
				Occupied(mut entry) => {
					let other_who = entry.get_mut();

					// double check if who is still voting for this pair. If not, it means that this
					// pair is no longer valid and must have been removed in previous rounds. The
					// reason for this is subtle; candidate_combinations is created once while the
					// inner loop might remove some edges. Note that if count() > 2, the we have
					// duplicates.
					if assignments[assignment_index]
						.distribution
						.iter()
						.filter(|(t, _)| *t == v1 || *t == v2)
						.count() != 2
					{
						continue
					}

					// check if other_who voted for the same pair v1, v2.
					let maybe_other_assignments = assignments.iter().find(|a| a.who == *other_who);
					if maybe_other_assignments.is_none() {
						continue
					}
					let other_assignment =
						maybe_other_assignments.expect("value is checked to be 'Some'");

					// Collect potential cycle votes
					let mut other_cycle_votes =
						other_assignment
							.distribution
							.iter()
							.filter_map(|(t, w)| {
								if *t == v1 || *t == v2 {
									Some((t.clone(), *w))
								} else {
									None
								}
							})
							.collect::<Vec<(A, ExtendedBalance)>>();

					let other_votes_count = other_cycle_votes.len();

					// If the length is more than 2, then we have identified duplicates. For now, we
					// just skip. Later on we can early exit and stop processing this data since it
					// is corrupt anyhow.
					debug_assert!(other_votes_count <= 2);

					if other_votes_count < 2 {
						// This is not a cycle. Replace and continue.
						*other_who = who.clone();
						continue
					} else if other_votes_count == 2 {
						// This is a cycle.
						let mut who_cycle_votes: Vec<(A, ExtendedBalance)> = Vec::with_capacity(2);
						assignments[assignment_index].distribution.iter().for_each(|(t, w)| {
							if *t == v1 || *t == v2 {
								who_cycle_votes.push((t.clone(), *w));
							}
						});

						if who_cycle_votes.len() != 2 {
							continue
						}

						// Align the targets similarly. This helps with the circulation below.
						if other_cycle_votes[0].0 != who_cycle_votes[0].0 {
							other_cycle_votes.swap(0, 1);
						}

						// Find min
						let mut min_value: ExtendedBalance = Bounded::max_value();
						let mut min_index: usize = 0;
						let cycle = who_cycle_votes
							.iter()
							.chain(other_cycle_votes.iter())
							.enumerate()
							.map(|(index, (t, w))| {
								if *w <= min_value {
									min_value = *w;
									min_index = index;
								}
								(t.clone(), *w)
							})
							.collect::<Vec<(A, ExtendedBalance)>>();

						// min was in the first part of the chained iters
						let mut increase_indices: Vec<usize> = Vec::new();
						let mut decrease_indices: Vec<usize> = Vec::new();
						decrease_indices.push(min_index);
						if min_index < 2 {
							// min_index == 0 => sibling_index <- 1
							// min_index == 1 => sibling_index <- 0
							let sibling_index = 1 - min_index;
							increase_indices.push(sibling_index);
							// valid because the two chained sections of `cycle` are aligned;
							// index [0, 2] are both voting for v1 or both v2. Same goes for [1, 3].
							decrease_indices.push(sibling_index + 2);
							increase_indices.push(min_index + 2);
						} else {
							// min_index == 2 => sibling_index <- 3
							// min_index == 3 => sibling_index <- 2
							let sibling_index = 3 - min_index % 2;
							increase_indices.push(sibling_index);
							// valid because the two chained sections of `cycle` are aligned;
							// index [0, 2] are both voting for v1 or both v2. Same goes for [1, 3].
							decrease_indices.push(sibling_index - 2);
							increase_indices.push(min_index - 2);
						}

						// apply changes
						let mut remove_indices: Vec<usize> = Vec::with_capacity(1);
						increase_indices.into_iter().for_each(|i| {
							let voter = if i < 2 { who.clone() } else { other_who.clone() };
							// Note: so this is pretty ambiguous. We should only look for one
							// assignment that meets this criteria and if we find multiple then that
							// is a corrupt input. Same goes for the next block.
							assignments.iter_mut().filter(|a| a.who == voter).for_each(|ass| {
								ass.distribution
									.iter_mut()
									.position(|(t, _)| *t == cycle[i].0)
									.map(|idx| {
										let next_value =
											ass.distribution[idx].1.saturating_add(min_value);
										ass.distribution[idx].1 = next_value;
									});
							});
						});
						decrease_indices.into_iter().for_each(|i| {
							let voter = if i < 2 { who.clone() } else { other_who.clone() };
							assignments.iter_mut().filter(|a| a.who == voter).for_each(|ass| {
								ass.distribution
									.iter_mut()
									.position(|(t, _)| *t == cycle[i].0)
									.map(|idx| {
										let next_value =
											ass.distribution[idx].1.saturating_sub(min_value);
										if next_value.is_zero() {
											ass.distribution.remove(idx);
											remove_indices.push(i);
											num_changed += 1;
										} else {
											ass.distribution[idx].1 = next_value;
										}
									});
							});
						});

						// remove either one of them.
						let who_removed = remove_indices.iter().find(|i| **i < 2usize).is_some();
						let other_removed =
							remove_indices.into_iter().find(|i| *i >= 2usize).is_some();

						match (who_removed, other_removed) {
							(false, true) => {
								*other_who = who.clone();
							},
							(true, false) => {
								// nothing, other_who can stay there.
							},
							(true, true) => {
								// remove and don't replace
								entry.remove();
							},
							(false, false) => {
								// Neither of the edges was removed? impossible.
								panic!("Duplicate voter (or other corrupt input).");
							},
						}
					}
				},
			}
		}
	}

	num_changed
}

/// Reduce redundant edges from the edge weight graph, with all possible length.
///
/// To get the best performance, this should be called after `reduce_4()`.
///
/// Returns the number of edges removed.
///
/// It is strictly assumed that the `who` attribute of all provided assignments are unique. The
/// result will most likely be corrupt otherwise.
///
/// O(|Ew| ⋅ m)
fn reduce_all<A: IdentifierT>(assignments: &mut Vec<StakedAssignment<A>>) -> u32 {
	let mut num_changed: u32 = Zero::zero();
	let mut tree: BTreeMap<NodeId<A>, NodeRef<A>> = BTreeMap::new();

	// NOTE: This code can heavily use an index cache. Looking up a pair of (voter, target) in the
	// assignments happens numerous times and and we can save time. For now it is written as such
	// because abstracting some of this code into a function/closure is super hard due to borrow
	// checks (and most likely needs unsafe code at the end). For now I will keep it as it and
	// refactor later.

	// a flat iterator of (voter, target) over all pairs of votes. Similar to reduce_4, we loop
	// without borrowing.
	for assignment_index in 0..assignments.len() {
		let voter = assignments[assignment_index].who.clone();

		let mut dist_index = 0;
		loop {
			// A distribution could have been removed. We don't know for sure. Hence, we check.
			let maybe_dist = assignments[assignment_index].distribution.get(dist_index);
			if maybe_dist.is_none() {
				// The rest of this loop is moot.
				break
			}
			let (target, _) = maybe_dist.expect("Value checked to be some").clone();

			// store if they existed already.
			let voter_id = NodeId::from(voter.clone(), NodeRole::Voter);
			let target_id = NodeId::from(target.clone(), NodeRole::Target);
			let voter_exists = tree.contains_key(&voter_id);
			let target_exists = tree.contains_key(&target_id);

			// create both.
			let voter_node = tree
				.entry(voter_id.clone())
				.or_insert_with(|| Node::new(voter_id).into_ref())
				.clone();
			let target_node = tree
				.entry(target_id.clone())
				.or_insert_with(|| Node::new(target_id).into_ref())
				.clone();

			// If one exists but the other one doesn't, or if both does not, then set the existing
			// one as the parent of the non-existing one and move on. Else, continue with the rest
			// of the code.
			match (voter_exists, target_exists) {
				(false, false) => {
					Node::set_parent_of(&target_node, &voter_node);
					dist_index += 1;
					continue
				},
				(false, true) => {
					Node::set_parent_of(&voter_node, &target_node);
					dist_index += 1;
					continue
				},
				(true, false) => {
					Node::set_parent_of(&target_node, &voter_node);
					dist_index += 1;
					continue
				},
				(true, true) => { /* don't continue and execute the rest */ },
			};

			let (voter_root, voter_root_path) = Node::root(&voter_node);
			let (target_root, target_root_path) = Node::root(&target_node);

			if voter_root != target_root {
				// swap
				merge(voter_root_path, target_root_path);
				dist_index += 1;
			} else {
				// find common and cycle.
				let common_count = trailing_common(&voter_root_path, &target_root_path);

				// because roots are the same.
				#[cfg(feature = "std")]
				debug_assert_eq!(target_root_path.last().unwrap(), voter_root_path.last().unwrap());
				debug_assert!(common_count > 0);

				// cycle part of each path will be `path[path.len() - common_count - 1 : 0]`
				// NOTE: the order of chaining is important! it is always build from [target, ...,
				// voter]
				let cycle = target_root_path
					.iter()
					.take(target_root_path.len() - common_count + 1)
					.cloned()
					.chain(
						voter_root_path
							.iter()
							.take(voter_root_path.len() - common_count)
							.rev()
							.cloned(),
					)
					.collect::<Vec<NodeRef<A>>>();

				// a cycle's length shall always be multiple of two.
				#[cfg(feature = "std")]
				debug_assert_eq!(cycle.len() % 2, 0);

				// find minimum of cycle.
				let mut min_value: ExtendedBalance = Bounded::max_value();
				// The voter and the target pair that create the min edge.
				let mut min_target: A = Default::default();
				let mut min_voter: A = Default::default();
				// The index of the min in opaque cycle list.
				let mut min_index = 0usize;
				// 1 -> next // 0 -> prev
				let mut min_direction = 0u32;
				// helpers
				let next_index = |i| {
					if i < (cycle.len() - 1) {
						i + 1
					} else {
						0
					}
				};
				let prev_index = |i| {
					if i > 0 {
						i - 1
					} else {
						cycle.len() - 1
					}
				};
				for i in 0..cycle.len() {
					if cycle[i].borrow().id.role == NodeRole::Voter {
						// NOTE: sadly way too many clones since I don't want to make A: Copy
						let current = cycle[i].borrow().id.who.clone();
						let next = cycle[next_index(i)].borrow().id.who.clone();
						let prev = cycle[prev_index(i)].borrow().id.who.clone();
						assignments.iter().find(|a| a.who == current).map(|ass| {
							ass.distribution.iter().find(|d| d.0 == next).map(|(_, w)| {
								if *w < min_value {
									min_value = *w;
									min_target = next.clone();
									min_voter = current.clone();
									min_index = i;
									min_direction = 1;
								}
							})
						});
						assignments.iter().find(|a| a.who == current).map(|ass| {
							ass.distribution.iter().find(|d| d.0 == prev).map(|(_, w)| {
								if *w < min_value {
									min_value = *w;
									min_target = prev.clone();
									min_voter = current.clone();
									min_index = i;
									min_direction = 0;
								}
							})
						});
					}
				}

				// if the min edge is in the voter's sub-chain.
				// [target, ..., X, Y, ... voter]
				let target_chunk = target_root_path.len() - common_count;
				let min_chain_in_voter = (min_index + min_direction as usize) > target_chunk;

				// walk over the cycle and update the weights
				let mut should_inc_counter = true;
				let start_operation_add = ((min_index % 2) + min_direction as usize) % 2 == 1;
				let mut additional_removed = Vec::new();
				for i in 0..cycle.len() {
					let current = cycle[i].borrow();
					if current.id.role == NodeRole::Voter {
						let prev = cycle[prev_index(i)].borrow();
						assignments
							.iter_mut()
							.enumerate()
							.filter(|(_, a)| a.who == current.id.who)
							.for_each(|(target_ass_index, ass)| {
								ass.distribution
									.iter_mut()
									.position(|(t, _)| *t == prev.id.who)
									.map(|idx| {
										let next_value = if i % 2 == 0 {
											if start_operation_add {
												ass.distribution[idx].1.saturating_add(min_value)
											} else {
												ass.distribution[idx].1.saturating_sub(min_value)
											}
										} else {
											if start_operation_add {
												ass.distribution[idx].1.saturating_sub(min_value)
											} else {
												ass.distribution[idx].1.saturating_add(min_value)
											}
										};

										if next_value.is_zero() {
											// if the removed edge is from the current assignment, dis_index
											// should NOT be increased.
											if target_ass_index == assignment_index {
												should_inc_counter = false
											}
											ass.distribution.remove(idx);
											num_changed += 1;
											// only add if this is not the min itself.
											if !(i == min_index && min_direction == 0) {
												additional_removed.push((
													cycle[i].clone(),
													cycle[prev_index(i)].clone(),
												));
											}
										} else {
											ass.distribution[idx].1 = next_value;
										}
									});
							});

						let next = cycle[next_index(i)].borrow();
						assignments
							.iter_mut()
							.enumerate()
							.filter(|(_, a)| a.who == current.id.who)
							.for_each(|(target_ass_index, ass)| {
								ass.distribution
									.iter_mut()
									.position(|(t, _)| *t == next.id.who)
									.map(|idx| {
										let next_value = if i % 2 == 0 {
											if start_operation_add {
												ass.distribution[idx].1.saturating_sub(min_value)
											} else {
												ass.distribution[idx].1.saturating_add(min_value)
											}
										} else {
											if start_operation_add {
												ass.distribution[idx].1.saturating_add(min_value)
											} else {
												ass.distribution[idx].1.saturating_sub(min_value)
											}
										};

										if next_value.is_zero() {
											// if the removed edge is from the current assignment, dis_index
											// should NOT be increased.
											if target_ass_index == assignment_index {
												should_inc_counter = false
											}
											ass.distribution.remove(idx);
											num_changed += 1;
											if !(i == min_index && min_direction == 1) {
												additional_removed.push((
													cycle[i].clone(),
													cycle[next_index(i)].clone(),
												));
											}
										} else {
											ass.distribution[idx].1 = next_value;
										}
									});
							});
					}
				}

				// don't do anything if the edge removed itself. This is always the first and last
				// element
				let should_reorg = !(min_index == (cycle.len() - 1) && min_direction == 1);

				// re-org.
				if should_reorg {
					let min_edge = vec![min_voter, min_target];
					if min_chain_in_voter {
						// NOTE: safe; voter_root_path is always bigger than 1 element.
						for i in 0..voter_root_path.len() - 1 {
							let current = voter_root_path[i].clone().borrow().id.who.clone();
							let next = voter_root_path[i + 1].clone().borrow().id.who.clone();
							if min_edge.contains(&current) && min_edge.contains(&next) {
								break
							}
							Node::set_parent_of(&voter_root_path[i + 1], &voter_root_path[i]);
						}
						Node::set_parent_of(&voter_node, &target_node);
					} else {
						// NOTE: safe; target_root_path is always bigger than 1 element.
						for i in 0..target_root_path.len() - 1 {
							let current = target_root_path[i].clone().borrow().id.who.clone();
							let next = target_root_path[i + 1].clone().borrow().id.who.clone();
							if min_edge.contains(&current) && min_edge.contains(&next) {
								break
							}
							Node::set_parent_of(&target_root_path[i + 1], &target_root_path[i]);
						}
						Node::set_parent_of(&target_node, &voter_node);
					}
				}

				// remove every other node which has collapsed to zero
				for (r1, r2) in additional_removed {
					if Node::is_parent_of(&r1, &r2) {
						Node::remove_parent(&r1);
					} else if Node::is_parent_of(&r2, &r1) {
						Node::remove_parent(&r2);
					}
				}

				// increment the counter if needed.
				if should_inc_counter {
					dist_index += 1;
				}
			}
		}
	}

	num_changed
}

/// Reduce the given [`Vec<StakedAssignment<IdentifierT>>`]. This removes redundant edges from
/// without changing the overall backing of any of the elected candidates.
///
/// Returns the number of edges removed.
///
/// IMPORTANT: It is strictly assumed that the `who` attribute of all provided assignments are
/// unique. The result will most likely be corrupt otherwise. Furthermore, if the _distribution
/// vector_ contains duplicate ids, only the first instance is ever updates.
///
/// O(min{ |Ew| ⋅ k + m3 , |Ew| ⋅ m })
pub fn reduce<A: IdentifierT>(assignments: &mut Vec<StakedAssignment<A>>) -> u32 where {
	let mut num_changed = reduce_4(assignments);
	num_changed += reduce_all(assignments);
	num_changed
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn merging_works() {
		// 	D <-- A <-- B <-- C
		//
		// 		F <-- E
		let d = Node::new(NodeId::from(1, NodeRole::Target)).into_ref();
		let a = Node::new(NodeId::from(2, NodeRole::Target)).into_ref();
		let b = Node::new(NodeId::from(3, NodeRole::Target)).into_ref();
		let c = Node::new(NodeId::from(4, NodeRole::Target)).into_ref();
		let e = Node::new(NodeId::from(5, NodeRole::Target)).into_ref();
		let f = Node::new(NodeId::from(6, NodeRole::Target)).into_ref();

		Node::set_parent_of(&c, &b);
		Node::set_parent_of(&b, &a);
		Node::set_parent_of(&a, &d);
		Node::set_parent_of(&e, &f);

		let path1 = vec![c.clone(), b.clone(), a.clone(), d.clone()];
		let path2 = vec![e.clone(), f.clone()];

		merge(path1, path2);
		// 	D <-- A <-- B <-- C
		// 					  |
		// 		F --> E --> -->
		assert_eq!(e.borrow().clone().parent.unwrap().borrow().id.who, 4u32); // c
	}

	#[test]
	fn merge_with_len_one() {
		// 	D <-- A <-- B <-- C
		//
		// 		F <-- E
		let d = Node::new(NodeId::from(1, NodeRole::Target)).into_ref();
		let a = Node::new(NodeId::from(2, NodeRole::Target)).into_ref();
		let b = Node::new(NodeId::from(3, NodeRole::Target)).into_ref();
		let c = Node::new(NodeId::from(4, NodeRole::Target)).into_ref();
		let f = Node::new(NodeId::from(6, NodeRole::Target)).into_ref();

		Node::set_parent_of(&c, &b);
		Node::set_parent_of(&b, &a);
		Node::set_parent_of(&a, &d);

		let path1 = vec![c.clone(), b.clone(), a.clone(), d.clone()];
		let path2 = vec![f.clone()];

		merge(path1, path2);
		// 	D <-- A <-- B <-- C
		// 					  |
		// 			F -->  -->
		assert_eq!(f.borrow().clone().parent.unwrap().borrow().id.who, 4u32); // c
	}

	#[test]
	fn basic_reduce_4_cycle_works() {
		use super::*;

		let assignments = vec![
			StakedAssignment { who: 1, distribution: vec![(10, 25), (20, 75)] },
			StakedAssignment { who: 2, distribution: vec![(10, 50), (20, 50)] },
		];

		let mut new_assignments = assignments.clone();
		let num_reduced = reduce_4(&mut new_assignments);

		assert_eq!(num_reduced, 1);
		assert_eq!(
			new_assignments,
			vec![
				StakedAssignment { who: 1, distribution: vec![(20, 100),] },
				StakedAssignment { who: 2, distribution: vec![(10, 75), (20, 25),] },
			],
		);
	}

	#[test]
	fn basic_reduce_all_cycles_works() {
		let mut assignments = vec![
			StakedAssignment { who: 1, distribution: vec![(10, 10)] },
			StakedAssignment { who: 2, distribution: vec![(10, 15), (20, 5)] },
			StakedAssignment { who: 3, distribution: vec![(20, 15), (40, 15)] },
			StakedAssignment { who: 4, distribution: vec![(20, 10), (30, 10), (40, 20)] },
			StakedAssignment { who: 5, distribution: vec![(20, 20), (30, 10), (40, 20)] },
		];

		assert_eq!(3, reduce_all(&mut assignments));

		assert_eq!(
			assignments,
			vec![
				StakedAssignment { who: 1, distribution: vec![(10, 10),] },
				StakedAssignment { who: 2, distribution: vec![(10, 15), (20, 5),] },
				StakedAssignment { who: 3, distribution: vec![(20, 30),] },
				StakedAssignment { who: 4, distribution: vec![(40, 40),] },
				StakedAssignment { who: 5, distribution: vec![(20, 15), (30, 20), (40, 15),] },
			],
		)
	}

	#[test]
	fn basic_reduce_works() {
		let mut assignments = vec![
			StakedAssignment { who: 1, distribution: vec![(10, 10)] },
			StakedAssignment { who: 2, distribution: vec![(10, 15), (20, 5)] },
			StakedAssignment { who: 3, distribution: vec![(20, 15), (40, 15)] },
			StakedAssignment { who: 4, distribution: vec![(20, 10), (30, 10), (40, 20)] },
			StakedAssignment { who: 5, distribution: vec![(20, 20), (30, 10), (40, 20)] },
		];

		assert_eq!(3, reduce(&mut assignments));

		assert_eq!(
			assignments,
			vec![
				StakedAssignment { who: 1, distribution: vec![(10, 10),] },
				StakedAssignment { who: 2, distribution: vec![(10, 15), (20, 5),] },
				StakedAssignment { who: 3, distribution: vec![(20, 30),] },
				StakedAssignment { who: 4, distribution: vec![(40, 40),] },
				StakedAssignment { who: 5, distribution: vec![(20, 15), (30, 20), (40, 15),] },
			],
		)
	}

	#[test]
	fn should_deal_with_self_vote() {
		let mut assignments = vec![
			StakedAssignment { who: 1, distribution: vec![(10, 10)] },
			StakedAssignment { who: 2, distribution: vec![(10, 15), (20, 5)] },
			StakedAssignment { who: 3, distribution: vec![(20, 15), (40, 15)] },
			StakedAssignment { who: 4, distribution: vec![(20, 10), (30, 10), (40, 20)] },
			StakedAssignment { who: 5, distribution: vec![(20, 20), (30, 10), (40, 20)] },
			// self vote from 10 and 20 to itself.
			StakedAssignment { who: 10, distribution: vec![(10, 100)] },
			StakedAssignment { who: 20, distribution: vec![(20, 200)] },
		];

		assert_eq!(3, reduce(&mut assignments));

		assert_eq!(
			assignments,
			vec![
				StakedAssignment { who: 1, distribution: vec![(10, 10),] },
				StakedAssignment { who: 2, distribution: vec![(10, 15), (20, 5),] },
				StakedAssignment { who: 3, distribution: vec![(20, 30),] },
				StakedAssignment { who: 4, distribution: vec![(40, 40),] },
				StakedAssignment { who: 5, distribution: vec![(20, 15), (30, 20), (40, 15),] },
				// should stay untouched.
				StakedAssignment { who: 10, distribution: vec![(10, 100)] },
				StakedAssignment { who: 20, distribution: vec![(20, 200)] },
			],
		)
	}

	#[test]
	fn reduce_3_common_votes_same_weight() {
		let mut assignments = vec![
			StakedAssignment {
				who: 4,
				distribution: vec![(1000000, 100), (1000002, 100), (1000004, 100)],
			},
			StakedAssignment {
				who: 5,
				distribution: vec![(1000000, 100), (1000002, 100), (1000004, 100)],
			},
		];

		reduce_4(&mut assignments);

		assert_eq!(
			assignments,
			vec![
				StakedAssignment { who: 4, distribution: vec![(1000000, 200,), (1000004, 100,),] },
				StakedAssignment { who: 5, distribution: vec![(1000002, 200,), (1000004, 100,),] },
			],
		)
	}

	#[test]
	#[should_panic]
	fn reduce_panics_on_duplicate_voter() {
		let mut assignments = vec![
			StakedAssignment { who: 1, distribution: vec![(10, 10), (20, 10)] },
			StakedAssignment { who: 1, distribution: vec![(10, 15), (20, 5)] },
			StakedAssignment { who: 2, distribution: vec![(10, 15), (20, 15)] },
		];

		reduce(&mut assignments);
	}

	#[test]
	fn should_deal_with_duplicates_target() {
		let mut assignments = vec![
			StakedAssignment { who: 1, distribution: vec![(10, 15), (20, 5)] },
			StakedAssignment {
				who: 2,
				distribution: vec![
					(10, 15),
					(20, 15),
					// duplicate
					(10, 1),
					// duplicate
					(20, 1),
				],
			},
		];

		reduce(&mut assignments);

		assert_eq!(
			assignments,
			vec![
				StakedAssignment { who: 1, distribution: vec![(10, 20),] },
				StakedAssignment {
					who: 2,
					distribution: vec![
						(10, 10),
						(20, 20),
						// duplicate votes are silently ignored.
						(10, 1),
						(20, 1),
					],
				},
			],
		)
	}

	#[test]
	fn bound_should_be_kept() {
		let mut assignments = vec![
			StakedAssignment {
				who: 1,
				distribution: vec![(103, 72), (101, 53), (100, 83), (102, 38)],
			},
			StakedAssignment {
				who: 2,
				distribution: vec![(103, 18), (101, 36), (102, 54), (100, 94)],
			},
			StakedAssignment {
				who: 3,
				distribution: vec![(100, 96), (101, 35), (102, 52), (103, 69)],
			},
			StakedAssignment {
				who: 4,
				distribution: vec![(102, 34), (100, 47), (103, 91), (101, 73)],
			},
		];

		let winners = vec![103, 101, 100, 102];

		let n = 4;
		let m = winners.len() as u32;
		let num_reduced = reduce_all(&mut assignments);
		assert!(16 - num_reduced <= n + m);
	}
}
