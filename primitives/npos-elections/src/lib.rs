// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! A set of election algorithms to be used with a substrate runtime, typically within the staking
//! sub-system. Notable implementation include
//!
//! - [`seq_phragmen`]: Implements the Phragmén Sequential Method. An un-ranked, relatively fast
//!   election method that ensures PJR, but does not provide a constant factor approximation of the
//!   maximin problem.
//! - [`balance_solution`]: Implements the star balancing algorithm. This iterative process can
//!   increase a solutions score, as described in [`evaluate_support`].
//!
//! More information can be found at: https://arxiv.org/abs/2004.12990

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::{prelude::*, collections::btree_map::BTreeMap, fmt::Debug, cmp::Ordering, convert::TryFrom};
use sp_arithmetic::{
	PerThing, Rational128, ThresholdOrd, InnerOf, Normalizable,
	helpers_128bit::multiply_by_rational,
	traits::{Zero, Saturating, Bounded, SaturatedConversion},
};

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;
#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
#[cfg(feature = "std")]
use codec::{Encode, Decode};

mod node;
mod reduce;
mod helpers;

// re-export reduce stuff.
pub use reduce::reduce;

// re-export the helpers.
pub use helpers::*;

// re-export the compact macro, with the dependencies of the macro.
#[doc(hidden)]
pub use codec;
#[doc(hidden)]
pub use sp_arithmetic;

// re-export the compact solution type.
pub use sp_npos_elections_compact::generate_compact_solution_type;

/// A trait to limit the number of votes per voter. The generated compact type will implement this.
pub trait VotingLimit {
	const LIMIT: usize;
}

/// an aggregator trait for a generic type of a voter/target identifier. This usually maps to
/// substrate's account id.
pub trait IdentifierT: Clone + Eq + Default + Ord + Debug + codec::Codec {}

impl<T: Clone + Eq + Default + Ord + Debug + codec::Codec> IdentifierT for T {}

/// The errors that might occur in the this crate and compact.
#[derive(Debug, Eq, PartialEq)]
pub enum Error {
	/// While going from compact to staked, the stake of all the edges has gone above the
	/// total and the last stake cannot be assigned.
	CompactStakeOverflow,
	/// The compact type has a voter who's number of targets is out of bound.
	CompactTargetOverflow,
	/// One of the index functions returned none.
	CompactInvalidIndex,
	/// An error occurred in some arithmetic operation.
	ArithmeticError(&'static str),
}

/// A type which is used in the API of this crate as a numeric weight of a vote, most often the
/// stake of the voter. It is always converted to [`ExtendedBalance`] for computation.
pub type VoteWeight = u64;

/// A type in which performing operations on vote weights are safe.
pub type ExtendedBalance = u128;

/// The score of an assignment. This can be computed from the support map via [`evaluate_support`].
pub type ElectionScore = [ExtendedBalance; 3];

/// A winner, with their respective approval stake.
pub type WithApprovalOf<A> = (A, ExtendedBalance);

/// The denominator used for loads. Since votes are collected as u64, the smallest ratio that we
/// might collect is `1/approval_stake` where approval stake is the sum of votes. Hence, some number
/// bigger than u64::max_value() is needed. For maximum accuracy we simply use u128;
const DEN: u128 = u128::max_value();

/// A candidate entity for the election.
#[derive(Clone, Default, Debug)]
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
#[derive(Clone, Default, Debug)]
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
#[derive(Clone, Default, Debug)]
struct Edge<AccountId> {
	/// Identifier.
	who: AccountId,
	/// Load of this vote.
	load: Rational128,
	/// Index of the candidate stored in the 'candidates' vector.
	candidate_index: usize,
}

/// Final result of the election.
#[derive(Debug)]
pub struct ElectionResult<AccountId, T: PerThing> {
	/// Just winners zipped with their approval stake. Note that the approval stake is merely the
	/// sub of their received stake and could be used for very basic sorting and approval voting.
	pub winners: Vec<WithApprovalOf<AccountId>>,
	/// Individual assignments. for each tuple, the first elements is a voter and the second
	/// is the list of candidates that it supports.
	pub assignments: Vec<Assignment<AccountId, T>>,
}

/// A voter's stake assignment among a set of targets, represented as ratios.
#[derive(Debug, Clone, Default)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Encode, Decode))]
pub struct Assignment<AccountId, P: PerThing> {
	/// Voter's identifier.
	pub who: AccountId,
	/// The distribution of the voter's stake.
	pub distribution: Vec<(AccountId, P)>,
}

impl<AccountId: IdentifierT, P: PerThing> Assignment<AccountId, P>
where
	ExtendedBalance: From<InnerOf<P>>,
{
	/// Convert from a ratio assignment into one with absolute values aka. [`StakedAssignment`].
	///
	/// It needs `stake` which is the total budget of the voter. If `fill` is set to true,
	/// it _tries_ to ensure that all the potential rounding errors are compensated and the
	/// distribution's sum is exactly equal to the total budget, by adding or subtracting the
	/// remainder from the last distribution.
	///
	/// If an edge ratio is [`Bounded::min_value()`], it is dropped. This edge can never mean
	/// anything useful.
	pub fn into_staked(self, stake: ExtendedBalance) -> StakedAssignment<AccountId>
	where
		P: sp_std::ops::Mul<ExtendedBalance, Output = ExtendedBalance>,
	{
		let distribution = self.distribution
			.into_iter()
			.filter_map(|(target, p)| {
				// if this ratio is zero, then skip it.
				if p.is_zero() {
					None
				} else {
					// NOTE: this mul impl will always round to the nearest number, so we might both
					// overflow and underflow.
					let distribution_stake = p * stake;
					Some((target, distribution_stake))
				}
			})
			.collect::<Vec<(AccountId, ExtendedBalance)>>();

		StakedAssignment {
			who: self.who,
			distribution,
		}
	}

	/// Try and normalize this assignment.
	///
	/// If `Ok(())` is returned, then the assignment MUST have been successfully normalized to 100%.
	pub fn try_normalize(&mut self) -> Result<(), &'static str> {
		self.distribution
			.iter()
			.map(|(_, p)| *p)
			.collect::<Vec<_>>()
			.normalize(P::one())
			.map(|normalized_ratios|
				self.distribution
					.iter_mut()
					.zip(normalized_ratios)
					.for_each(|((_, old), corrected)| { *old = corrected; })
			)
	}
}

/// A voter's stake assignment among a set of targets, represented as absolute values in the scale
/// of [`ExtendedBalance`].
#[derive(Debug, Clone, Default)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Encode, Decode))]
pub struct StakedAssignment<AccountId> {
	/// Voter's identifier
	pub who: AccountId,
	/// The distribution of the voter's stake.
	pub distribution: Vec<(AccountId, ExtendedBalance)>,
}

impl<AccountId> StakedAssignment<AccountId> {
	/// Converts self into the normal [`Assignment`] type.
	///
	/// If `fill` is set to true, it _tries_ to ensure that all the potential rounding errors are
	/// compensated and the distribution's sum is exactly equal to 100%, by adding or subtracting
	/// the remainder from the last distribution.
	///
	/// NOTE: it is quite critical that this attempt always works. The data type returned here will
	/// potentially get used to create a compact type; a compact type requires sum of ratios to be
	/// less than 100% upon un-compacting.
	///
	/// If an edge stake is so small that it cannot be represented in `T`, it is ignored. This edge
	/// can never be re-created and does not mean anything useful anymore.
	pub fn into_assignment<P: PerThing>(self) -> Assignment<AccountId, P>
	where
		ExtendedBalance: From<InnerOf<P>>,
		AccountId: IdentifierT,
	{
		let stake = self.total();
		let distribution = self.distribution
			.into_iter()
			.filter_map(|(target, w)| {
				let per_thing = P::from_rational_approximation(w, stake);
				if per_thing == Bounded::min_value() {
					None
				} else {
					Some((target, per_thing))
				}
			})
			.collect::<Vec<(AccountId, P)>>();

		Assignment {
			who: self.who,
			distribution,
		}
	}

	/// Try and normalize this assignment.
	///
	/// If `Ok(())` is returned, then the assignment MUST have been successfully normalized to
	/// `stake`.
	///
	/// NOTE: current implementation of `.normalize` is almost safe to `expect()` upon. The only
	/// error case is when the input cannot fit in `T`, or the sum of input cannot fit in `T`.
	/// Sadly, both of these are dependent upon the implementation of `VoteLimit`, i.e. the limit
	/// of edges per voter which is enforced from upstream. Hence, at this crate, we prefer
	/// returning a result and a use the name prefix `try_`.
	pub fn try_normalize(&mut self, stake: ExtendedBalance) -> Result<(), &'static str> {
		self.distribution
			.iter()
			.map(|(_, ref weight)| *weight)
			.collect::<Vec<_>>()
			.normalize(stake)
			.map(|normalized_weights|
				self.distribution
					.iter_mut()
					.zip(normalized_weights.into_iter())
					.for_each(|((_, weight), corrected)| { *weight = corrected; })
			)
	}

	/// Get the total stake of this assignment (aka voter budget).
	pub fn total(&self) -> ExtendedBalance {
		self.distribution.iter().fold(Zero::zero(), |a, b| a.saturating_add(b.1))
	}
}

/// A structure to demonstrate the election result from the perspective of the candidate, i.e. how
/// much support each candidate is receiving.
///
/// This complements the [`ElectionResult`] and is needed to run the balancing post-processing.
///
/// This, at the current version, resembles the `Exposure` defined in the Staking pallet, yet
/// they do not necessarily have to be the same.
#[derive(Default, Debug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Eq, PartialEq))]
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
///
/// This function does not strip out candidates who do not have any backing stake. It is the
/// responsibility of the caller to make sure only those candidates who have a sensible economic
/// value are passed in. From the perspective of this function, a candidate can easily be among the
/// winner with no backing stake.
pub fn seq_phragmen<AccountId, R>(
	candidate_count: usize,
	minimum_candidate_count: usize,
	initial_candidates: Vec<AccountId>,
	initial_voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)>,
) -> Option<ElectionResult<AccountId, R>> where
	AccountId: Default + Ord + Clone,
	R: PerThing,
{
	// return structures
	let mut elected_candidates: Vec<(AccountId, ExtendedBalance)>;
	let mut assigned: Vec<Assignment<AccountId, R>>;

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
	voters.extend(initial_voters.into_iter().map(|(who, voter_stake, votes)| {
		let mut edges: Vec<Edge<AccountId>> = Vec::with_capacity(votes.len());
		for v in votes {
			if edges.iter().any(|e| e.who == v) {
				// duplicate edge.
				continue;
			}
			if let Some(idx) = c_idx_cache.get(&v) {
				// This candidate is valid + already cached.
				candidates[*idx].approval_stake = candidates[*idx].approval_stake
					.saturating_add(voter_stake.into());
				edges.push(Edge { who: v.clone(), candidate_index: *idx, ..Default::default() });
			} // else {} would be wrong votes. We don't really care about it.
		}
		Voter {
			who,
			edges: edges,
			budget: voter_stake.into(),
			load: Rational128::zero(),
		}
	}));


	// we have already checked that we have more candidates than minimum_candidate_count.
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
					).unwrap_or_else(|_| Bounded::max_value());
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
			..Default::default()
		};
		for e in &mut n.edges {
			if elected_candidates.iter().position(|(ref c, _)| *c == e.who).is_some() {
				let per_bill_parts: R::Inner =
				{
					if n.load == e.load {
						// Full support. No need to calculate.
						R::ACCURACY
					} else {
						if e.load.d() == n.load.d() {
							// return e.load / n.load.
							let desired_scale: u128 = R::ACCURACY.saturated_into();
							let parts = multiply_by_rational(
								desired_scale,
								e.load.n(),
								n.load.n(),
							)
							// If result cannot fit in u128. Not much we can do about it.
							.unwrap_or_else(|_| Bounded::max_value());

							TryFrom::try_from(parts)
								// If the result cannot fit into R::Inner. Defensive only. This can
								// never happen. `desired_scale * e / n`, where `e / n < 1` always
								// yields a value smaller than `desired_scale`, which will fit into
								// R::Inner.
								.unwrap_or_else(|_| Bounded::max_value())
						} else {
							// defensive only. Both edge and voter loads are built from
							// scores, hence MUST have the same denominator.
							Zero::zero()
						}
					}
				};
				let per_thing = R::from_parts(per_bill_parts);
				assignment.distribution.push((e.who.clone(), per_thing));
			}
		}

		let len = assignment.distribution.len();
		if len > 0 {
			// To ensure an assertion indicating: no stake from the voter going to waste,
			// we add a minimal post-processing to equally assign all of the leftover stake ratios.
			let vote_count: R::Inner = len.saturated_into();
			let accuracy = R::ACCURACY;
			let mut sum: R::Inner = Zero::zero();
			assignment.distribution.iter().for_each(|a| sum = sum.saturating_add(a.1.deconstruct()));

			let diff = accuracy.saturating_sub(sum);
			let diff_per_vote = (diff / vote_count).min(accuracy);

			if !diff_per_vote.is_zero() {
				for i in 0..len {
					let current_ratio = assignment.distribution[i % len].1;
					let next_ratio = current_ratio
						.saturating_add(R::from_parts(diff_per_vote));
					assignment.distribution[i % len].1 = next_ratio;
				}
			}

			// `remainder` is set to be less than maximum votes of a voter (currently 16).
			// safe to cast it to usize.
			let remainder = diff - diff_per_vote * vote_count;
			for i in 0..remainder.saturated_into::<usize>() {
				let current_ratio = assignment.distribution[i % len].1;
				let next_ratio = current_ratio.saturating_add(R::from_parts(1u8.into()));
				assignment.distribution[i % len].1 = next_ratio;
			}
			assigned.push(assignment);
		}
	}

	Some(ElectionResult {
		winners: elected_candidates,
		assignments: assigned,
	})
}

/// Build the support map from the given election result. It maps a flat structure like
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
///
/// The second returned flag indicates the number of edges who didn't corresponded to an actual
/// winner from the given winner set. A value in this place larger than 0 indicates a potentially
/// faulty assignment.
///
/// `O(E)` where `E` is the total number of edges.
pub fn build_support_map<AccountId>(
	winners: &[AccountId],
	assignments: &[StakedAssignment<AccountId>],
) -> (SupportMap<AccountId>, u32) where
	AccountId: Default + Ord + Clone,
{
	let mut errors = 0;
	// Initialize the support of each candidate.
	let mut supports = <SupportMap<AccountId>>::new();
	winners
		.iter()
		.for_each(|e| { supports.insert(e.clone(), Default::default()); });

	// build support struct.
	for StakedAssignment { who, distribution } in assignments.iter() {
		for (c, weight_extended) in distribution.iter() {
			if let Some(support) = supports.get_mut(c) {
				support.total = support.total.saturating_add(*weight_extended);
				support.voters.push((who.clone(), *weight_extended));
			} else {
				errors = errors.saturating_add(1);
			}
		}
	}
	(supports, errors)
}

/// Evaluate a support map. The returned tuple contains:
///
/// - Minimum support. This value must be **maximized**.
/// - Sum of all supports. This value must be **maximized**.
/// - Sum of all supports squared. This value must be **minimized**.
///
/// `O(E)` where `E` is the total number of edges.
pub fn evaluate_support<AccountId>(
	support: &SupportMap<AccountId>,
) -> ElectionScore {
	let mut min_support = ExtendedBalance::max_value();
	let mut sum: ExtendedBalance = Zero::zero();
	// NOTE: The third element might saturate but fine for now since this will run on-chain and need
	// to be fast.
	let mut sum_squared: ExtendedBalance = Zero::zero();
	for (_, support) in support.iter() {
		sum = sum.saturating_add(support.total);
		let squared = support.total.saturating_mul(support.total);
		sum_squared = sum_squared.saturating_add(squared);
		if support.total < min_support {
			min_support = support.total;
		}
	}
	[min_support, sum, sum_squared]
}

/// Compares two sets of election scores based on desirability and returns true if `this` is
/// better than `that`.
///
/// Evaluation is done in a lexicographic manner, and if each element of `this` is `that * epsilon`
/// greater or less than `that`.
///
/// Note that the third component should be minimized.
pub fn is_score_better<P: PerThing>(this: ElectionScore, that: ElectionScore, epsilon: P) -> bool
	where ExtendedBalance: From<sp_arithmetic::InnerOf<P>>
{
	match this
		.iter()
		.enumerate()
		.map(|(i, e)| (
			e.ge(&that[i]),
			e.tcmp(&that[i], epsilon.mul_ceil(that[i])),
		))
		.collect::<Vec<(bool, Ordering)>>()
		.as_slice()
	{
		// epsilon better in the score[0], accept.
		[(_, Ordering::Greater), _, _] => true,

		// less than epsilon better in score[0], but more than epsilon better in the second.
		[(true, Ordering::Equal), (_, Ordering::Greater), _] => true,

		// less than epsilon better in score[0, 1], but more than epsilon better in the third
		[(true, Ordering::Equal), (true, Ordering::Equal), (_, Ordering::Less)] => true,

		// anything else is not a good score.
		_ => false,
	}
}

/// Performs balancing post-processing to the output of the election algorithm. This happens in
/// rounds. The number of rounds and the maximum diff-per-round tolerance can be tuned through input
/// parameters.
///
/// Returns the number of iterations that were preformed.
///
/// - `assignments`: exactly the same as the output of [`seq_phragmen`].
/// - `supports`: mutable reference to s `SupportMap`. This parameter is updated.
/// - `tolerance`: maximum difference that can occur before an early quite happens.
/// - `iterations`: maximum number of iterations that will be processed.
pub fn balance_solution<AccountId>(
	assignments: &mut Vec<StakedAssignment<AccountId>>,
	supports: &mut SupportMap<AccountId>,
	tolerance: ExtendedBalance,
	iterations: usize,
) -> usize where AccountId: Ord + Clone {
	if iterations == 0 { return 0; }

	let mut i = 0 ;
	loop {
		let mut max_diff = 0;
		for assignment in assignments.iter_mut() {
			let voter_budget = assignment.total();
			let StakedAssignment { who, distribution } =  assignment;
			let diff = do_balancing(
				who,
				voter_budget,
				distribution,
				supports,
				tolerance,
			);
			if diff > max_diff { max_diff = diff; }
		}

		i += 1;
		if max_diff <= tolerance || i >= iterations {
			break i;
		}
	}
}

/// actually perform balancing. same interface is `balance_solution`. Just called in loops with a check for
/// maximum difference.
fn do_balancing<AccountId>(
	voter: &AccountId,
	budget: ExtendedBalance,
	elected_edges: &mut Vec<(AccountId, ExtendedBalance)>,
	support_map: &mut SupportMap<AccountId>,
	tolerance: ExtendedBalance
) -> ExtendedBalance where AccountId: Ord + Clone {
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
