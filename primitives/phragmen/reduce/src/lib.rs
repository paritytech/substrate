// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

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
//! >
//!
//! ### Resources:
//!
//! 1. https://hackmd.io/JOn9x98iS0e0DPWQ87zGWg?view

use std::collections::{btree_map::{Entry::*}};
use std::collections::BTreeMap;

use sp_runtime::traits::{Zero, Bounded};
use sp_phragmen::{ExtendedBalance, StakedAssignment};

mod node;

/// Map type used for caching. Can be easily swapped with HashMap.
type Map<A> = BTreeMap<(A, A), A>;

/// Returns all combinations of size two in the collection `input` with no repetition.
fn combinations_2<T: Clone + std::fmt::Debug>(input: &[T]) -> Vec<(T, T)> {
	let n = input.len();
	if n < 2 {
		return Default::default()
	}

	let mut comb = Vec::with_capacity(n * (n-1) / 2);
	for i in 0..n {
		for j in i+1..n {
			comb.push((input[i].clone(), input[j].clone()))
		}
	}
	comb
}

/// Returns the count of trailing common elements in a slice.
fn trailing_common<T: Eq>(t1: &[T], t2: &[T]) -> usize {
	let mut t1_pointer = t1.len() - 1;
	let mut t2_pointer = t2.len() - 1;
	let mut common = 0usize;

	while t1[t1_pointer] == t2[t2_pointer] {
		common += 1;
		if t1_pointer == 0 || t2_pointer == 0 {
			break;
		}
		t1_pointer -= 1;
		t2_pointer -= 1;
	}

	common
}

/// Reduce only redundant edges with cycle length of 4.
///
/// O(|E_w| ⋅ k).
fn reduce_4<AccountId: Clone + Eq + Default + Ord + std::fmt::Debug>(
	assignments: &mut Vec<StakedAssignment<AccountId>>,
) -> u32 {

	let mut combination_map: Map<AccountId> = Map::new();
	let mut num_changed: u32 = Zero::zero();

	// NOTE: we have to use the old fashioned style loops here with manual indexing. Borrowing
	// assignments will not work since then there is NO way to mutate it inside.
	for i in 0..assignments.len() {
		let who = assignments[i].who.clone();
		// immutable copy -- needed for further read operations. TODO: As an optimization at the
		// expense of readability, we can remove this.
		let distribution = &assignments[i].distribution.clone();

		// all combinations for this particular voter
		let candidate_combinations = combinations_2(
			&distribution.iter().map(|(t, _p)| t.clone()).collect::<Vec<AccountId>>(),
		);

		for (v1, v2) in candidate_combinations {
			match combination_map.entry((v1.clone(), v2.clone())) {
				Vacant(entry) => {
					entry.insert(who.clone());
				},
				Occupied(mut entry) => {
					let other_who = entry.get_mut();
					println!("Occupied {:?} -> ({:?} {:?}) other: {:?}", &who, &v1, &v2, &other_who);

					// check if other_who voted for the same pair v1, v2.
					let maybe_other_assignments = assignments.iter().find(|a| a.who == *other_who);
					if maybe_other_assignments.is_none() {
						// TODO: test for this path?
						// This combination is not a cycle.
						continue;
					}
					let other_assignment = maybe_other_assignments.expect("value is checked to be 'Some'");

					// Collect potential cycle votes
					let mut other_cycle_votes: Vec<(AccountId, ExtendedBalance)> = Vec::with_capacity(2);
					other_assignment.distribution.iter().for_each(|(t, w)| {
						if *t == v1 || *t == v2  { other_cycle_votes.push((t.clone(), *w)); }
					});

					// This is not a cycle. Replace and continue.
					let other_votes_count = other_cycle_votes.len();
					// TODO: this might need testing. Some duplicate can cause this and this
					// function should reject them.
					debug_assert!(other_votes_count <= 2);

					if other_votes_count < 2 {
						// Not a cycle. Replace and move on.
						// TODO test fro this path??
						*other_who = who.clone();
						continue;
					} else {
						println!("And it is a cycle! ");
						// This is a cycle.
						let mut who_cycle_votes: Vec<(AccountId, ExtendedBalance)> = Vec::with_capacity(2);
						distribution.iter().for_each(|(t, w)| {
							if *t == v1 || *t == v2  { who_cycle_votes.push((t.clone(), *w)); }
						});

						if who_cycle_votes.len() != 2 { continue; }

						// Align the targets similarly. This helps with the circulation below.
						if other_cycle_votes[0].0 != who_cycle_votes[0].0 {
							other_cycle_votes.swap(0, 1);
						}

						debug_assert_eq!(who_cycle_votes[0].0, other_cycle_votes[0].0);
						debug_assert_eq!(who_cycle_votes[1].0, other_cycle_votes[1].0);

						// Find min
						let mut min_value: ExtendedBalance = Bounded::max_value();
						let mut min_index: usize = 0;
						let cycle = who_cycle_votes
							.iter()
							.chain(other_cycle_votes.iter())
							.enumerate()
							.map(|(index, (t, w))| {
								if *w <= min_value { min_value = *w; min_index = index; }
								(t.clone(), *w)
							}).collect::<Vec<(AccountId, ExtendedBalance)>>();
						dbg!(&cycle, &min_value);

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

						dbg!(&increase_indices, &decrease_indices);

						// apply changes
						increase_indices.into_iter().for_each(|i| {
							assignments.iter_mut().filter(|a| a.who == if i < 2 { who.clone() } else { other_who.clone() }).for_each(|ass| {
								ass.distribution
									.iter_mut()
									.position(|(t, _)| *t == cycle[i].0)
									.map(|idx| {
										let next_value = ass.distribution[idx].1.saturating_add(min_value);
										if next_value.is_zero() {
											ass.distribution.remove(idx);
										} else {
											ass.distribution[idx].1 = next_value;
										}
									});
							});
						});
						decrease_indices.into_iter().for_each(|i| {
							assignments.iter_mut().filter(|a| a.who == if i < 2 { who.clone() } else { other_who.clone() }).for_each(|ass| {
								ass.distribution
									.iter_mut()
									.position(|(t, _)| *t == cycle[i].0)
									.map(|idx| {
										let next_value = ass.distribution[idx].1.saturating_sub(min_value);
										if next_value.is_zero() {
											ass.distribution.remove(idx);
											num_changed += 1;
										} else {
											ass.distribution[idx].1 = next_value;
										}
									});
							});
						});
					}
				}
			}
		}
	}

	num_changed
}

/// Reduce all redundant edges from the edge weight graph.
///
/// O(|Ew| ⋅ m)
fn reduce_all<AccountId: Clone + Eq + Default + Ord + std::fmt::Debug>(
	assignments: &mut Vec<StakedAssignment<AccountId>>,
) -> u32 {
	let mut num_changed: u32 = Zero::zero();

	// ----------------- Phase 2: remove any other cycle
	use node::{Node, NodeRef, NodeRole};
	let mut tree: BTreeMap<AccountId, NodeRef<AccountId>> = BTreeMap::new();

	// a flat iterator of (voter, target) over all pairs of votes. Similar to reduce_4, we loop
	// without borrowing.
	for i in 0..assignments.len() {
		let voter = assignments[i].who.clone();

		for j in 0..assignments[i].distribution.len() {
			let (target, _) = assignments[i].distribution[j].clone();

			let voter_node = tree.entry(voter.clone())
				.or_insert(Node::new(voter.clone(), NodeRole::Voter).into_ref()).clone();
			let target_node = tree.entry(target.clone())
				.or_insert(Node::new(target.clone(), NodeRole::Target).into_ref()).clone();

			if !voter_node.borrow().has_parent() {
				Node::set_parent_of(&voter_node, &target_node);
				continue;
			}
			if !target_node.borrow().has_parent() {
				Node::set_parent_of(&target_node, &voter_node);
				continue;
			}

			let (voter_root, voter_root_path) = Node::root(&voter_node);
			let (target_root, target_root_path) = Node::root(&target_node);

			if voter_root != target_root {
				// swap
				// TODO: test case for this path
				if voter_root_path.len() <= target_root_path.len() {
					// iterate from last to beginning, skipping the first one. This asserts that
					// indexing is always correct.
					voter_root_path
						.iter()
						.skip(1)
						.rev()
						.enumerate()
						.map(|(index, r)| (voter_root_path.len() - index - 1, r))
						.for_each(|(index, r)| {
							let index = voter_root_path.len() - index;
							Node::set_parent_of(r, &voter_root_path[index-1])
						});
					debug_assert_eq!(voter_root_path[0], voter_node);
					Node::set_parent_of(&voter_node, &target_node);
				} else {
					target_root_path
						.iter()
						.skip(1)
						.rev()
						.enumerate()
						.map(|(index, r)| (target_root_path.len() - index - 1, r))
						.for_each(|(index, r)| {
							let index = target_root_path.len() - index;
							Node::set_parent_of(r, &target_root_path[index-1])
						});
					debug_assert_eq!(target_root_path[0], target_node);
					Node::set_parent_of(&target_node, &voter_node);
				}
			} else {
				debug_assert_eq!(target_root_path.last().unwrap(), voter_root_path.last().unwrap());

				// find common and cycle.
				let common_count = trailing_common(&voter_root_path, &target_root_path);

				// because roots are the same. TODO: replace with a bail-out
				debug_assert!(common_count > 0);

				// cycle part of each path will be `path[path.len() - common_count - 1 : 0]`
				// NOTE: the order of chaining is important! it is always build from [target, ...,
				// voter]
				// TODO: check borrows panic!
				let cycle =
					target_root_path.iter().take(target_root_path.len() - common_count + 1).cloned()
					.chain(voter_root_path.iter().take(voter_root_path.len() - common_count).rev().cloned())
					.collect::<Vec<NodeRef<AccountId>>>();


				// TODO: a cycle struct that gives you min + to which chunk it belonged.
				// find minimum of cycle.
				let mut min_value: ExtendedBalance = Bounded::max_value();
				// Note that this can only ever point to a target, not a voter.
				let mut min_who: AccountId = Default::default();
				let mut min_index = 0usize;
				// 1 -> next // 0 -> prev  TOOD: I have some ideas of fixing this.
				let mut min_direction = 0u32;
				// helpers
				let next_index = |i| { if i < (cycle.len() - 1) { i + 1 } else { 0 } };
				let prev_index = |i| { if i > 0 { i - 1 } else { cycle.len() - 1 } };
				for i in 0..cycle.len() {
					if cycle[i].borrow().role == NodeRole::Voter {
						// NOTE: sadly way too many clones since I don't want to make AccountId: Copy
						let current = cycle[i].borrow().who.clone();
						let next = cycle[next_index(i)].borrow().who.clone();
						let prev = cycle[prev_index(i)].borrow().who.clone();
						assignments.iter().find(|a| a.who == current).map(|ass| {
							ass.distribution.iter().find(|d| d.0 == next).map(|(_, w)| {
								if *w < min_value {
									min_value = *w;
									min_who = next.clone();
									min_index = i;
									min_direction = 1;
								}
							})
						});
						assignments.iter().find(|a| a.who == current).map(|ass| {
							ass.distribution.iter().find(|d| d.0 == prev).map(|(_, w)| {
								if *w < min_value {
									min_value = *w;
									min_who = prev.clone();
									min_index = i;
									min_direction = 0;
								}
							})
						});
					}
				}
				// if the min edge is in the voter's sub-chain.
				let target_chunk = target_root_path.len() - common_count;
				let min_chain_in_voter = (min_index + min_direction as usize) >= target_chunk;

				dbg!(min_value, min_index, &min_who, min_direction);

				// walk over the cycle and update the weights
				// TODO: or at least unify and merge the process of adding this flow in both places. and surely add dedicated tests for this supply demand circulation math
				// if the circulation begins with an addition. It is assumed that a cycle always starts with a target.
				let start_operation_add = ((min_index % 2) + min_direction as usize) % 2 == 1;
				for i in 0..cycle.len() {
					let current = cycle[i].borrow();
					if current.role == NodeRole::Voter {
						let prev = cycle[prev_index(i)].borrow();

						assignments.iter_mut().filter(|a| a.who == current.who).for_each(|ass| {
							ass.distribution.iter_mut().position(|(t, _)| *t == prev.who).map(|idx| {
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
								// println!("Next value for edge {:?} -> {:?} is {}", current.who, prev.who, next_value);
								if next_value.is_zero() {
									ass.distribution.remove(idx);
									num_changed += 1;
								} else {
									ass.distribution[idx].1 = next_value;
								}
							});
						});

						let next = cycle[next_index(i)].borrow();

						assignments.iter_mut().filter(|a| a.who == current.who).for_each(|ass| {
							ass.distribution.iter_mut().position(|(t, _)| *t == next.who).map(|idx| {
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
								// println!("Next value for edge {:?} -> {:?} is {}", current.who, next.who, next_value);
								if next_value.is_zero() {
									ass.distribution.remove(idx);
									num_changed += 1;
								} else {
									ass.distribution[idx].1 = next_value;
								}
							});
						});
					}
				};

				// don't do anything if the edge removed itself
				if min_index == (cycle.len() - 1) && min_direction == 1 { continue; }

				// TODO: this is most likely buggy
				// re-org otherwise.
				if min_chain_in_voter {
					// NOTE: safe; voter_root_path is always bigger than 1 element.
					for i in 0..voter_root_path.len()-1 {
						let next = voter_root_path[i + 1].clone();
						if next.borrow().who == min_who {
							break;
						}
						Node::set_parent_of(&voter_root_path[i + 1], &voter_root_path[i]);
					}
					Node::set_parent_of(&voter_node, &target_node);
				} else {
					// NOTE: safe; target_root_path is always bigger than 1 element.
					for i in 0..target_root_path.len()-1 {
						if target_root_path[i].borrow().who == min_who {
							break;
						}
						Node::set_parent_of(&target_root_path[i + 1], &target_root_path[i]);
					}
					Node::set_parent_of(&target_node, &voter_node);
				}



			}
		}
	}

	num_changed
}

/// Reduce the given [`PhragmenResult`]. This removes redundant edges from without changing the
/// overall backing of any of the elected candidates.
///
/// O(min{ |Ew| ⋅ k + m3 , |Ew| ⋅ m })
pub fn reduce<
	AccountId: Clone + Eq + Default + Ord + std::fmt::Debug,
>(
	assignments: &mut Vec<StakedAssignment<AccountId>>,
) -> u32 where {
	let mut num_changed = reduce_4(assignments);
	num_changed += reduce_all(assignments);
	num_changed
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_phragmen::build_support_map;

	type AccountId = u64;
	type Balance = u128;

	#[allow(dead_code)] // to be used with fuzzing
	pub fn assert_assignments_equal(
		winners: &Vec<AccountId>,
		ass1: &Vec<StakedAssignment<AccountId>>,
		ass2: &Vec<StakedAssignment<AccountId>>,
	) {
		let (support_1, _) = build_support_map::<Balance, AccountId>(winners, ass1);
		let (support_2, _) = build_support_map::<Balance, AccountId>(winners, ass2);

		for (who, support) in support_1.iter() {
			assert_eq!(support.total, support_2.get(who).unwrap().total);
			assert_eq!(support.voters, support_2.get(who).unwrap().voters);

		}
	}

	#[allow(dead_code)] // to be used with fuzzing
	pub fn reduce_and_compare(
		assignment: &Vec<StakedAssignment<AccountId>>,
		winners: &Vec<AccountId>,
	) {
		let mut altered_assignment = assignment.clone();
		crate::reduce(&mut altered_assignment);
		assert_assignments_equal(
			winners,
			&assignment,
			&altered_assignment,
		);
	}

	#[test]
	fn trailing_common_works() {
		assert_eq!(
			trailing_common(&vec![1u8, 2, 3, 4, 5], &vec![7u8, 8, 4, 5]),
			2,
		);
		assert_eq!(
			trailing_common(&vec![1u8, 2], &vec![7u8, 8]),
			0,
		);
		assert_eq!(
			trailing_common(&vec![1u8, 2, 3, 4, 5], &vec![3u8, 4, 5]),
			3,
		);
	}

	#[test]
	fn basic_reduce_4_cycle_works() {
		use super::*;

		let assignments = vec![
			StakedAssignment {
				who: 1,
				distribution: vec![
					(10, 25),
					(20, 75),
				],
			},
			StakedAssignment {
				who: 2,
				distribution: vec![
					(10, 50),
					(20, 50),
				],
			},
		];

		let mut new_assignments = assignments.clone();
		let num_reduced = reduce_4(&mut new_assignments);

		assert_eq!(num_reduced, 1);
		assert_eq!(
			new_assignments,
			vec![
				StakedAssignment {
					who: 1,
					distribution: vec![
						(20, 100),
					],
				},
				StakedAssignment {
					who: 2,
					distribution: vec![
						(10, 75),
						(20, 25),
					],
				},
			],
		);
	}

	#[test]
	fn basic_reduce_all_cycles_works() {
		let mut assignments = vec![
			StakedAssignment {
				who: 1,
				distribution: vec![(10, 10)]
			},
			StakedAssignment {
				who: 2,
				distribution: vec![
					(10, 15),
					(20, 5),
				],
			},
			StakedAssignment {
				who: 3,
				distribution: vec![
					(20, 15),
					(40, 15)
				],
			},
			StakedAssignment {
				who: 4, distribution:
				vec![
					(20, 10),
					(30, 10),
					(40, 20),
				]
			},
			StakedAssignment {
				who: 5,
				distribution: vec![
					(20, 20),
					(30, 10),
					(40, 20),
				],
			},
		];

		assert_eq!(3, reduce_all(&mut assignments));

		assert_eq!(
			assignments,
			vec![
				StakedAssignment {
				who: 1,
				distribution: vec![
					(10, 10),
				]
			},
			StakedAssignment {
				who: 2,
				distribution: vec![
					(10, 15),
					(20, 5),
				],
			},
			StakedAssignment {
				who: 3,
				distribution: vec![
					(20, 30),
				],
			},
			StakedAssignment {
				who: 4, distribution:
				vec![
					(40, 40),
				]
			},
			StakedAssignment {
				who: 5,
				distribution: vec![
					(20, 15),
					(30, 20),
					(40, 15),
				],
			},
			],
		)
	}

	#[test]
	fn basic_reduce_works() {
		let mut assignments = vec![
			StakedAssignment {
				who: 1,
				distribution: vec![(10, 10)]
			},
			StakedAssignment {
				who: 2,
				distribution: vec![
					(10, 15),
					(20, 5),
				],
			},
			StakedAssignment {
				who: 3,
				distribution: vec![
					(20, 15),
					(40, 15)
				],
			},
			StakedAssignment {
				who: 4, distribution:
				vec![
					(20, 10),
					(30, 10),
					(40, 20),
				]
			},
			StakedAssignment {
				who: 5,
				distribution: vec![
					(20, 20),
					(30, 10),
					(40, 20),
				],
			},
		];

		assert_eq!(3, reduce(&mut assignments));

		assert_eq!(
			assignments,
			vec![
				StakedAssignment {
				who: 1,
				distribution: vec![
					(10, 10),
				]
			},
			StakedAssignment {
				who: 2,
				distribution: vec![
					(10, 15),
					(20, 5),
				],
			},
			StakedAssignment {
				who: 3,
				distribution: vec![
					(20, 30),
				],
			},
			StakedAssignment {
				who: 4, distribution:
				vec![
					(40, 40),
				]
			},
			StakedAssignment {
				who: 5,
				distribution: vec![
					(20, 15),
					(30, 20),
					(40, 15),
				],
			},
			],
		)
	}

}
