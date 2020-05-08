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

//! Rust implementation of the Phragmén election algorithm. This is used in several pallets to
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

use sp_std::{prelude::*, collections::btree_map::BTreeMap, fmt::Debug, cmp::Ordering, convert::TryFrom};
use sp_arithmetic::{
	PerThing, Rational128,
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
pub use sp_phragmen_compact::generate_compact_solution_type;

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
}

/// A type which is used in the API of this crate as a numeric weight of a vote, most often the
/// stake of the voter. It is always converted to [`ExtendedBalance`] for computation.
pub type VoteWeight = u64;

/// A type in which performing operations on vote weights are safe.
pub type ExtendedBalance = u128;

/// The score of an assignment. This can be computed from the support map via [`evaluate_support`].
pub type PhragmenScore = [ExtendedBalance; 3];

/// A winner, with their respective approval stake.
pub type WithApprovalOf<A> = (A, ExtendedBalance);

/// The denominator used for loads. Since votes are collected as u64, the smallest ratio that we
/// might collect is `1/approval_stake` where approval stake is the sum of votes. Hence, some number
/// bigger than u64::max_value() is needed. For maximum accuracy we simply use u128;
const DEN: u128 = u128::max_value();

/// A candidate entity for phragmen election.
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

/// Final result of the phragmen election.
#[derive(Debug)]
pub struct PhragmenResult<AccountId, T: PerThing> {
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
pub struct Assignment<AccountId, T: PerThing> {
	/// Voter's identifier.
	pub who: AccountId,
	/// The distribution of the voter's stake.
	pub distribution: Vec<(AccountId, T)>,
}

impl<AccountId, T: PerThing> Assignment<AccountId, T>
where
	ExtendedBalance: From<<T as PerThing>::Inner>,
{
	/// Convert from a ratio assignment into one with absolute values aka. [`StakedAssignment`].
	///
	/// It needs `stake` which is the total budget of the voter. If `fill` is set to true,
	/// it _tries_ to ensure that all the potential rounding errors are compensated and the
	/// distribution's sum is exactly equal to the total budget, by adding or subtracting the
	/// remainder from the last distribution.
	///
	/// If an edge ratio is [`Bounded::max_value()`], it is dropped. This edge can never mean
	/// anything useful.
	pub fn into_staked(self, stake: ExtendedBalance, fill: bool) -> StakedAssignment<AccountId>
	where
		T: sp_std::ops::Mul<ExtendedBalance, Output = ExtendedBalance>,
	{
		let mut sum: ExtendedBalance = Bounded::min_value();
		let mut distribution = self
			.distribution
			.into_iter()
			.filter_map(|(target, p)| {
				// if this ratio is zero, then skip it.
				if p == Bounded::min_value() {
					None
				} else {
					// NOTE: this mul impl will always round to the nearest number, so we might both
					// overflow and underflow.
					let distribution_stake = p * stake;
					// defensive only. We assume that balance cannot exceed extended balance.
					sum = sum.saturating_add(distribution_stake);
					Some((target, distribution_stake))
				}
			})
			.collect::<Vec<(AccountId, ExtendedBalance)>>();

		if fill {
			// NOTE: we can do this better.
			// https://revs.runtime-revolution.com/getting-100-with-rounded-percentages-273ffa70252b
			if let Some(leftover) = stake.checked_sub(sum) {
				if let Some(last) = distribution.last_mut() {
					last.1 = last.1.saturating_add(leftover);
				}
			} else if let Some(excess) = sum.checked_sub(stake) {
				if let Some(last) = distribution.last_mut() {
					last.1 = last.1.saturating_sub(excess);
				}
			}
		}

		StakedAssignment {
			who: self.who,
			distribution,
		}
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
	pub fn into_assignment<T: PerThing>(self, fill: bool) -> Assignment<AccountId, T>
	where
		ExtendedBalance: From<<T as PerThing>::Inner>,
	{
		let accuracy: u128 = T::ACCURACY.saturated_into();
		let mut sum: u128 = Zero::zero();
		let stake = self.distribution.iter().map(|x| x.1).sum();
		let mut distribution = self
			.distribution
			.into_iter()
			.filter_map(|(target, w)| {
				let per_thing = T::from_rational_approximation(w, stake);
				if per_thing == Bounded::min_value() {
					None
				} else {
					sum += per_thing.clone().deconstruct().saturated_into();
					Some((target, per_thing))
				}
			})
			.collect::<Vec<(AccountId, T)>>();

		if fill {
			if let Some(leftover) = accuracy.checked_sub(sum) {
				if let Some(last) = distribution.last_mut() {
					last.1 = last.1.saturating_add(
						T::from_parts(leftover.saturated_into())
					);
				}
			} else if let Some(excess) = sum.checked_sub(accuracy) {
				if let Some(last) = distribution.last_mut() {
					last.1 = last.1.saturating_sub(
						T::from_parts(excess.saturated_into())
					);
				}
			}
		}

		Assignment {
			who: self.who,
			distribution,
		}
	}

	/// Get the total stake of this assignment (aka voter budget).
	pub fn total(&self) -> ExtendedBalance {
		self.distribution.iter().fold(Zero::zero(), |a, b| a.saturating_add(b.1))
	}
}

/// A structure to demonstrate the phragmen result from the perspective of the candidate, i.e. how
/// much support each candidate is receiving.
///
/// This complements the [`PhragmenResult`] and is needed to run the equalize post-processing.
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
pub fn elect<AccountId, R>(
	candidate_count: usize,
	minimum_candidate_count: usize,
	initial_candidates: Vec<AccountId>,
	initial_voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)>,
) -> Option<PhragmenResult<AccountId, R>> where
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
							.unwrap_or(Bounded::max_value());

							TryFrom::try_from(parts)
								// If the result cannot fit into R::Inner. Defensive only. This can
								// never happen. `desired_scale * e / n`, where `e / n < 1` always
								// yields a value smaller than `desired_scale`, which will fit into
								// R::Inner.
								.unwrap_or(Bounded::max_value())
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

/// Evaluate a phragmen result, given the support map. The returned tuple contains:
///
/// - Minimum support. This value must be **maximized**.
/// - Sum of all supports. This value must be **maximized**.
/// - Sum of all supports squared. This value must be **minimized**.
///
/// `O(E)` where `E` is the total number of edges.
pub fn evaluate_support<AccountId>(
	support: &SupportMap<AccountId>,
) -> PhragmenScore {
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

/// Compares two sets of phragmen scores based on desirability and returns true if `that` is
/// better than `this`.
///
/// Evaluation is done in a lexicographic manner.
///
/// Note that the third component should be minimized.
pub fn is_score_better(this: PhragmenScore, that: PhragmenScore) -> bool {
	match that
		.iter()
		.enumerate()
		.map(|(i, e)| e.cmp(&this[i]))
		.collect::<Vec<Ordering>>()
		.as_slice()
	{
		[Ordering::Greater, _, _] => true,
		[Ordering::Equal, Ordering::Greater, _] => true,
		[Ordering::Equal, Ordering::Equal, Ordering::Less] => true,
		_ => false,
	}
}

/// Performs equalize post-processing to the output of the election algorithm. This happens in
/// rounds. The number of rounds and the maximum diff-per-round tolerance can be tuned through input
/// parameters.
///
/// Returns the number of iterations that were preformed.
///
/// - `assignments`: exactly the same is the output of phragmen.
/// - `supports`: mutable reference to s `SupportMap`. This parameter is updated.
/// - `tolerance`: maximum difference that can occur before an early quite happens.
/// - `iterations`: maximum number of iterations that will be processed.
pub fn equalize<AccountId>(
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
			let diff = do_equalize(
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

/// actually perform equalize. same interface is `equalize`. Just called in loops with a check for
/// maximum difference.
fn do_equalize<AccountId>(
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
