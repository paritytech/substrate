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

//! Rust implementation of the Phragmén election algorithm. This is used in several SRML modules to
//! optimally distribute the weight of a set of voters among an elected set of candidates. In the
//! context of staking this is mapped to validators and nominators.
//!
//! The algorithm has two phases:
//!   - Sequential phragmen: performed in [`elect`] function which is first pass of the distribution
//!     The results are not optimal but the execution time is less.
//!   - Equalize post-processing: tries to further distribute the weight fairly among candidates.
//!     Incurs more execution time.
//!
//! The main objective of the assignments done by phragmen is to maximize the minimum backed
//! candidate in the elected set.
//!
//! Reference implementation: https://github.com/w3f/consensus
//! Further details:
//! https://research.web3.foundation/en/latest/polkadot/NPoS/4.%20Sequential%20Phragm%C3%A9n%E2%80%99s%20method/

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::{prelude::*, collections::btree_map::BTreeMap};
use sp_runtime::{helpers_128bit::multiply_by_rational, Perbill, Rational128, RuntimeDebug};
use sp_runtime::traits::{Zero, Convert, Member, SimpleArithmetic, Saturating, Bounded};

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

mod node;

/// A type in which performing operations on balances and stakes of candidates and voters are safe.
///
/// This module's functions expect a `Convert` type to convert all balances to u64. Hence, u128 is
/// a safe type for arithmetic operations over them.
///
/// Balance types converted to `ExtendedBalance` are referred to as `Votes`.
pub type ExtendedBalance = u128;

/// The denominator used for loads. Since votes are collected as u64, the smallest ratio that we
/// might collect is `1/approval_stake` where approval stake is the sum of votes. Hence, some number
/// bigger than u64::max_value() is needed. For maximum accuracy we simply use u128;
const DEN: u128 = u128::max_value();

/// A candidate entity for phragmen election.
#[derive(Clone, Default, RuntimeDebug)]
struct Candidate<AccountId> {
	/// Identifier.
	who: AccountId,
	/// Intermediary value used to sort candidates.
	score: Rational128,
	/// Sum of the stake of this candidate based on received votes.
	approval_stake: ExtendedBalance,
	/// Flag for being elected.
	elected: bool,
}

/// A voter entity.
#[derive(Clone, Default, RuntimeDebug)]
struct Voter<AccountId> {
	/// Identifier.
	who: AccountId,
	/// List of candidates proposed by this voter.
	edges: Vec<Edge<AccountId>>,
	/// The stake of this voter.
	budget: ExtendedBalance,
	/// Incremented each time a candidate that this voter voted for has been elected.
	load: Rational128,
}

/// A candidate being backed by a voter.
#[derive(Clone, Default, RuntimeDebug)]
struct Edge<AccountId> {
	/// Identifier.
	who: AccountId,
	/// Load of this vote.
	load: Rational128,
	/// Index of the candidate stored in the 'candidates' vector.
	candidate_index: usize,
}

/// Final result of the phragmen election.
#[derive(RuntimeDebug)]
pub struct PhragmenResult<AccountId> {
	/// Just winners zipped with their approval stake. Note that the approval stake is merely the
	/// sub of their received stake and could be used for very basic sorting and approval voting.
	pub winners: Vec<(AccountId, ExtendedBalance)>,
	/// Individual assignments. for each tuple, the first elements is a voter and the second
	/// is the list of candidates that it supports.
	pub assignments: Vec<Assignment<AccountId>>
}

#[derive(RuntimeDebug, Clone)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq))]
pub struct Assignment<AccountId> {
	/// Voter's identifier
	pub who: AccountId,
	/// The distribution of the voter's stake.
	pub distribution: Vec<(AccountId, Perbill)>,
}

impl<AccountId> Assignment<AccountId> {
	fn into_staked<Balance, C, FS>(self, stake_of: FS) -> StakedAssignment<AccountId>
	where
		C: Convert<Balance, ExtendedBalance>,
		for<'r> FS: Fn(&'r AccountId) -> Balance,
	{
		let stake = C::convert(stake_of(&self.who));
		let distribution = self.distribution.into_iter().map(|(target, p)| {
			let distribution_stake = p * stake;
			(target, distribution_stake)
		}).collect::<Vec<(AccountId, ExtendedBalance)>>();

		StakedAssignment {
			who: self.who,
			distribution,
		}
	}
}

#[derive(RuntimeDebug, Clone)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq))]
pub struct StakedAssignment<AccountId> {
	/// Voter's identifier
	pub who: AccountId,
	/// The distribution of the voter's stake.
	pub distribution: Vec<(AccountId, ExtendedBalance)>,
}

/// A structure to demonstrate the phragmen result from the perspective of the candidate, i.e. how
/// much support each candidate is receiving.
///
/// This complements the [`PhragmenResult`] and is needed to run the equalize post-processing.
///
/// This, at the current version, resembles the `Exposure` defined in the staking SRML module, yet
/// they do not necessarily have to be the same.
#[derive(Default, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(serde::Serialize, serde::Deserialize, Eq, PartialEq))]
pub struct Support<AccountId> {
	/// Total support.
	pub total: ExtendedBalance,
	/// Support from voters.
	pub voters: Vec<(AccountId, ExtendedBalance)>,
}

/// A linkage from a candidate and its [`Support`].
pub type SupportMap<A> = BTreeMap<A, Support<A>>;

/// Perform election based on Phragmén algorithm.
///
/// Returns an `Option` the set of winners and their detailed support ratio from each voter if
/// enough candidates are provided. Returns `None` otherwise.
///
/// * `candidate_count`: number of candidates to elect.
/// * `minimum_candidate_count`: minimum number of candidates to elect. If less candidates exist,
///   `None` is returned.
/// * `initial_candidates`: candidates list to be elected from.
/// * `initial_voters`: voters list.
/// * `stake_of`: something that can return the stake stake of a particular candidate or voter.
///
/// This function does not strip out candidates who do not have any backing stake. It is the
/// responsibility of the caller to make sure only those candidates who have a sensible economic
/// value are passed in. From the perspective of this function, a candidate can easily be among the
/// winner with no backing stake.
pub fn elect<AccountId, Balance, FS, C>(
	candidate_count: usize,
	minimum_candidate_count: usize,
	initial_candidates: Vec<AccountId>,
	initial_voters: Vec<(AccountId, Vec<AccountId>)>,
	stake_of: FS,
) -> Option<PhragmenResult<AccountId>> where
	AccountId: Default + Ord + Member,
	Balance: Default + Copy + SimpleArithmetic,
	for<'r> FS: Fn(&'r AccountId) -> Balance,
	// TODO: btw now we can remove the backward convert!
	C: Convert<Balance, u64> + Convert<u128, Balance>,
{
	let to_votes = |b: Balance| <C as Convert<Balance, u64>>::convert(b) as ExtendedBalance;

	// return structures
	let mut elected_candidates: Vec<(AccountId, ExtendedBalance)>;
	let mut assigned: Vec<Assignment<AccountId>>;

	// used to cache and access candidates index.
	let mut c_idx_cache = BTreeMap::<AccountId, usize>::new();

	// voters list.
	let num_voters = initial_candidates.len() + initial_voters.len();
	let mut voters: Vec<Voter<AccountId>> = Vec::with_capacity(num_voters);

	// Iterate once to create a cache of candidates indexes. This could be optimized by being
	// provided by the call site.
	let mut candidates = initial_candidates
		.into_iter()
		.enumerate()
		.map(|(idx, who)| {
			c_idx_cache.insert(who.clone(), idx);
			Candidate { who, ..Default::default() }
		})
		.collect::<Vec<Candidate<AccountId>>>();

	// early return if we don't have enough candidates
	if candidates.len() < minimum_candidate_count { return None; }

	// collect voters. use `c_idx_cache` for fast access and aggregate `approval_stake` of
	// candidates.
	voters.extend(initial_voters.into_iter().map(|(who, votes)| {
		let voter_stake = stake_of(&who);
		let mut edges: Vec<Edge<AccountId>> = Vec::with_capacity(votes.len());
		for v in votes {
			if let Some(idx) = c_idx_cache.get(&v) {
				// This candidate is valid + already cached.
				candidates[*idx].approval_stake = candidates[*idx].approval_stake
					.saturating_add(to_votes(voter_stake));
				edges.push(Edge { who: v.clone(), candidate_index: *idx, ..Default::default() });
			} // else {} would be wrong votes. We don't really care about it.
		}
		Voter {
			who,
			edges: edges,
			budget: to_votes(voter_stake),
			load: Rational128::zero(),
		}
	}));


	// we have already checked that we have more candidates than minimum_candidate_count.
	// run phragmen.
	let to_elect = candidate_count.min(candidates.len());
	elected_candidates = Vec::with_capacity(candidate_count);
	assigned = Vec::with_capacity(candidate_count);

	// main election loop
	for _round in 0..to_elect {
		// loop 1: initialize score
		for c in &mut candidates {
			if !c.elected {
				// 1 / approval_stake == (DEN / approval_stake) / DEN. If approval_stake is zero,
				// then the ratio should be as large as possible, essentially `infinity`.
				if c.approval_stake.is_zero() {
					c.score = Rational128::from_unchecked(DEN, 0);
				} else {
					c.score = Rational128::from(DEN / c.approval_stake, DEN);
				}
			}
		}

		// loop 2: increment score
		for n in &voters {
			for e in &n.edges {
				let c = &mut candidates[e.candidate_index];
				if !c.elected && !c.approval_stake.is_zero() {
					let temp_n = multiply_by_rational(
						n.load.n(),
						n.budget,
						c.approval_stake,
					).unwrap_or(Bounded::max_value());
					let temp_d = n.load.d();
					let temp = Rational128::from(temp_n, temp_d);
					c.score = c.score.lazy_saturating_add(temp);
				}
			}
		}

		// loop 3: find the best
		if let Some(winner) = candidates
			.iter_mut()
			.filter(|c| !c.elected)
			.min_by_key(|c| c.score)
		{
			// loop 3: update voter and edge load
			winner.elected = true;
			for n in &mut voters {
				for e in &mut n.edges {
					if e.who == winner.who {
						e.load = winner.score.lazy_saturating_sub(n.load);
						n.load = winner.score;
					}
				}
			}

			elected_candidates.push((winner.who.clone(), winner.approval_stake));
		} else {
			break
		}
	} // end of all rounds

	// update backing stake of candidates and voters
	for n in &mut voters {
		let mut assignment = Assignment {
			who: n.who.clone(),
			distribution: vec![],
		};
		for e in &mut n.edges {
			if elected_candidates.iter().position(|(ref c, _)| *c == e.who).is_some() {
				let per_bill_parts =
				{
					if n.load == e.load {
						// Full support. No need to calculate.
						Perbill::accuracy().into()
					} else {
						if e.load.d() == n.load.d() {
							// return e.load / n.load.
							let desired_scale: u128 = Perbill::accuracy().into();
							multiply_by_rational(
								desired_scale,
								e.load.n(),
								n.load.n(),
							).unwrap_or(Bounded::max_value())
						} else {
							// defensive only. Both edge and nominator loads are built from
							// scores, hence MUST have the same denominator.
							Zero::zero()
						}
					}
				};
				// safer to .min() inside as well to argue as u32 is safe.
				let per_thing = Perbill::from_parts(
					per_bill_parts.min(Perbill::accuracy().into()) as u32
				);
				assignment.distribution.push((e.who.clone(), per_thing));
			}
		}

		if assignment.distribution.len() > 0 {
			// To ensure an assertion indicating: no stake from the nominator going to waste,
			// we add a minimal post-processing to equally assign all of the leftover stake ratios.
			let vote_count = assignment.distribution.len() as u32;
			let len = assignment.distribution.len();
			let sum = assignment.distribution.iter()
				.map(|a| a.1.deconstruct())
				.sum::<u32>();
			let accuracy = Perbill::accuracy();
			let diff = accuracy.checked_sub(sum).unwrap_or(0);
			let diff_per_vote = (diff / vote_count).min(accuracy);

			if diff_per_vote > 0 {
				for i in 0..len {
					let current_ratio = assignment.distribution[i % len].1;
					let next_ratio = current_ratio
						.saturating_add(Perbill::from_parts(diff_per_vote));
					assignment.distribution[i % len].1 = next_ratio;
				}
			}

			// `remainder` is set to be less than maximum votes of a nominator (currently 16).
			// safe to cast it to usize.
			let remainder = diff - diff_per_vote * vote_count;
			for i in 0..remainder as usize {
				let current_ratio = assignment.distribution[i % len].1;
				let next_ratio = current_ratio.saturating_add(Perbill::from_parts(1));
				assignment.distribution[i % len].1 = next_ratio;
			}
			assigned.push(assignment);
		}
	}

	Some(PhragmenResult {
		winners: elected_candidates,
		assignments: assigned,
	})
}

/// Build the support map from the given phragmen result. It maps a flat structure like
///
/// ```nocompile
/// assignments: vec![
/// 	voter1, vec![(candidate1, w11), (candidate2, w12)],
/// 	voter2, vec![(candidate1, w21), (candidate2, w22)]
/// ]
/// ```
///
/// into a mapping of candidates and their respective support:
///
/// ```nocompile
///  SupportMap {
/// 	candidate1: Support {
/// 		own:0,
/// 		total: w11 + w21,
/// 		others: vec![(candidate1, w11), (candidate2, w21)]
///		},
/// 	candidate2: Support {
/// 		own:0,
/// 		total: w12 + w22,
/// 		others: vec![(candidate1, w12), (candidate2, w22)]
///		},
/// }
/// ```
pub fn build_support_map<Balance, AccountId>(
	elected_stashes: &Vec<AccountId>,
	assignments: &Vec<StakedAssignment<AccountId>>,
) -> SupportMap<AccountId> where
	AccountId: Default + Ord + Member,
	Balance: Default + Copy + SimpleArithmetic,
{
	// Initialize the support of each candidate.
	let mut supports = <SupportMap<AccountId>>::new();
	elected_stashes
		.iter()
		.for_each(|e| { supports.insert(e.clone(), Default::default()); });

	// build support struct.
	for StakedAssignment { who, distribution } in assignments.iter() {
		for (c, weight_extended) in distribution.iter() {
			if let Some(support) = supports.get_mut(c) {
				support.total = support.total.saturating_add(*weight_extended);
				support.voters.push((who.clone(), *weight_extended));
			}
		}
	}
	supports
}

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
/// TODO: this need not to be in the public interface.
/// ```rust
/// use sp_phragmen::trailing_common;
///
/// fn main() {
/// 	assert_eq!(
/// 		trailing_common(&vec![1u8, 2, 3, 4, 5], &vec![7u8, 8, 4, 5]),
/// 		2,
/// 	);
///
/// 	assert_eq!(
/// 		trailing_common(&vec![1u8, 2], &vec![7u8, 8]),
/// 		0,
/// 	);
///
/// 	assert_eq!(
/// 		trailing_common(&vec![1u8, 2, 3, 4, 5], &vec![3u8, 4, 5]),
/// 		3,
/// 	)
/// }
/// ```
pub fn trailing_common<T: Eq>(t1: &[T], t2: &[T]) -> usize {
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

// TODO: maybe replace with BTreeMap if we want to support this in no_std?
type Map<A> = std::collections::HashMap<(A, A), A>;

fn reduce_4<AccountId: Clone + Eq + Default + std::hash::Hash + std::fmt::Debug,>(
	assignments: &mut Vec<StakedAssignment<AccountId>>,
) -> u32 {
	use std::collections::{HashMap, hash_map::{Entry::*}};

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

						// TODO: remove later.
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

	println!("DoNE {:?}", assignments);
	num_changed
}

fn reduce_all<AccountId: Clone + Eq + Default + std::hash::Hash + std::fmt::Debug>(
	assignments: &mut Vec<StakedAssignment<AccountId>>,
) -> u32 {
	dbg!(&assignments);
	use std::collections::{HashMap, hash_map::{Entry::*}};
	use std::cell::{Cell, RefCell};
	let mut change_buffer: HashMap<AccountId, Vec<(AccountId, Perbill)>> = HashMap::new();
	let mut num_changed: u32 = Zero::zero();

	// ----------------- Phase 2: remove any other cycle
	use node::{Node, NodeRef, NodeRole};
	let mut tree: HashMap<AccountId, NodeRef<AccountId>> = HashMap::new();

	// needless to say, this can be improved. TODO
	let edge_weight_of = |voter: &AccountId, candidate: &AccountId| {
		if let Some(a) = assignments.iter().find(|a| a.who == *voter) {
			if let Some((_, w)) = a.distribution.iter().find(|(t, _)| t == candidate) {
				Some(w)
			} else {
				None
			}
		} else {
			None
		}
	};


	// TODO: unify this terminology: we only have VOTER -> TARGET. no candidate. no staking terms.
	// a flat iterator of (voter, candidate) over all pairs of votes. Similar to reduce_4, we loop
	// without borrowing.
	for i in 0..assignments.len() {
		let voter = assignments[i].who.clone();

		for j in 0..assignments[i].distribution.len() {
			let (target, _) = assignments[i].distribution[j].clone();
			println!("+++++ {:?} -> {:?}, Tree", voter, target);
			for (key, value) in tree.iter() {
				println!("{:?}", value.borrow());
			}

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

				println!("cycle = {:?}", cycle.iter().map(|w| w.borrow().who.clone()).collect::<Vec<AccountId>>());

				// TODO: a cycle struct that gives you min + to which chunk it belonged.
				// find minimum of cycle.
				let mut min_value: ExtendedBalance = Bounded::max_value();
				// Note that this can only ever point to a target, not a voter.
				let mut min_who: AccountId = Default::default();
				let mut min_neighbor: AccountId = Default::default();
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
				let cycle_len = cycle.len();
				let target_chunk = target_root_path.len() - common_count;
				let voter_chunk = voter_root_path.len() - common_count;
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
/// TODO: add complexity to all functions.
pub fn reduce<
	AccountId: Clone + Eq + Default + std::hash::Hash + std::fmt::Debug,
>(
	assignments: &mut Vec<StakedAssignment<AccountId>>,
) -> u32 where {
	let mut num_changed = reduce_4(assignments);
	num_changed += reduce_all(assignments);
	num_changed
}

/// Performs equalize post-processing to the output of the election algorithm. This happens in
/// rounds. The number of rounds and the maximum diff-per-round tolerance can be tuned through input
/// parameters.
///
/// No value is returned from the function and the `supports` parameter is updated.
///
/// * `assignments`: exactly the same is the output of phragmen.
/// * `supports`: mutable reference to s `SupportMap`. This parameter is updated.
/// * `tolerance`: maximum difference that can occur before an early quite happens.
/// * `iterations`: maximum number of iterations that will be processed.
/// * `stake_of`: something that can return the stake stake of a particular candidate or voter.
pub fn equalize<Balance, AccountId, C, FS>(
	mut assignments: Vec<StakedAssignment<AccountId>>,
	supports: &mut SupportMap<AccountId>,
	tolerance: ExtendedBalance,
	iterations: usize,
	stake_of: FS,
) where
	C: Convert<Balance, u64> + Convert<u128, Balance>,
	for<'r> FS: Fn(&'r AccountId) -> Balance,
	AccountId: Ord + Clone,
{
	// prepare the data for equalise
	for _i in 0..iterations {
		let mut max_diff = 0;

		for StakedAssignment { who, distribution } in assignments.iter_mut() {
			let voter_budget = stake_of(&who);

			let diff = do_equalize::<_, _, C>(
				who,
				voter_budget,
				distribution,
				supports,
				tolerance,
			);
			if diff > max_diff { max_diff = diff; }
		}

		if max_diff < tolerance {
			break;
		}
	}
}

/// actually perform equalize. same interface is `equalize`. Just called in loops with a check for
/// maximum difference.
fn do_equalize<Balance, AccountId, C>(
	voter: &AccountId,
	budget_balance: Balance,
	elected_edges: &mut Vec<(AccountId, ExtendedBalance)>,
	support_map: &mut SupportMap<AccountId>,
	tolerance: ExtendedBalance
) -> ExtendedBalance where
	C: Convert<Balance, u64> + Convert<u128, Balance>,
	AccountId: Ord + Clone,
{
	let to_votes = |b: Balance|
		<C as Convert<Balance, u64>>::convert(b) as ExtendedBalance;
	let budget = to_votes(budget_balance);

	// Nothing to do. This voter had nothing useful.
	// Defensive only. Assignment list should always be populated. 1 might happen for self vote.
	if elected_edges.is_empty() || elected_edges.len() == 1 { return 0; }

	let stake_used = elected_edges
		.iter()
		.fold(0 as ExtendedBalance, |s, e| s.saturating_add(e.1));

	let backed_stakes_iter = elected_edges
		.iter()
		.filter_map(|e| support_map.get(&e.0))
		.map(|e| e.total);

	let backing_backed_stake = elected_edges
		.iter()
		.filter(|e| e.1 > 0)
		.filter_map(|e| support_map.get(&e.0))
		.map(|e| e.total)
		.collect::<Vec<ExtendedBalance>>();

	let mut difference;
	if backing_backed_stake.len() > 0 {
		let max_stake = backing_backed_stake
			.iter()
			.max()
			.expect("vector with positive length will have a max; qed");
		let min_stake = backed_stakes_iter
			.min()
			.expect("iterator with positive length will have a min; qed");

		difference = max_stake.saturating_sub(min_stake);
		difference = difference.saturating_add(budget.saturating_sub(stake_used));
		if difference < tolerance {
			return difference;
		}
	} else {
		difference = budget;
	}

	// Undo updates to support
	elected_edges.iter_mut().for_each(|e| {
		if let Some(support) = support_map.get_mut(&e.0) {
			support.total = support.total.saturating_sub(e.1);
			support.voters.retain(|i_support| i_support.0 != *voter);
		}
		e.1 = 0;
	});

	elected_edges.sort_unstable_by_key(|e|
		if let Some(e) = support_map.get(&e.0) { e.total } else { Zero::zero() }
	);

	let mut cumulative_stake: ExtendedBalance = 0;
	let mut last_index = elected_edges.len() - 1;
	let mut idx = 0usize;
	for e in &mut elected_edges[..] {
		if let Some(support) = support_map.get_mut(&e.0) {
			let stake = support.total;
			let stake_mul = stake.saturating_mul(idx as ExtendedBalance);
			let stake_sub = stake_mul.saturating_sub(cumulative_stake);
			if stake_sub > budget {
				last_index = idx.checked_sub(1).unwrap_or(0);
				break;
			}
			cumulative_stake = cumulative_stake.saturating_add(stake);
		}
		idx += 1;
	}

	let last_stake = elected_edges[last_index].1;
	let split_ways = last_index + 1;
	let excess = budget
		.saturating_add(cumulative_stake)
		.saturating_sub(last_stake.saturating_mul(split_ways as ExtendedBalance));
	elected_edges.iter_mut().take(split_ways).for_each(|e| {
		if let Some(support) = support_map.get_mut(&e.0) {
			e.1 = (excess / split_ways as ExtendedBalance)
				.saturating_add(last_stake)
				.saturating_sub(support.total);
			support.total = support.total.saturating_add(e.1);
			support.voters.push((voter.clone(), e.1));
		}
	});

	difference
}
