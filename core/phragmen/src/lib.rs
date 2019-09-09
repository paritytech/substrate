// Copyright 2019 Parity Technologies (UK) Ltd.
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

use rstd::{prelude::*, collections::btree_map::BTreeMap};
use sr_primitives::{helpers_128bit::safe_multiply_by_rational, Perbill, Rational128};
use sr_primitives::traits::{Zero, Convert, Member, SimpleArithmetic, Saturating};

/// A type in which performing operations on balances and stakes of candidates and voters are safe.
///
/// This module's functions expect a `Convert` type to convert all balances to u64. Hence, u128 is
/// a safe type for arithmetic operations over them.
///
/// Balance types converted to `ExtendedBalance` are referred to as `Votes`.
pub type ExtendedBalance = u128;

/// The accuracy of the ratio type used in [`PhragmenAssignment`].
const ACCURACY: ExtendedBalance = Perbill::accuracy() as ExtendedBalance;

/// The denominator used for loads. Since votes are collected as u64, the smallest ratio that we
/// might collect is `1/approval_stake` where approval stake is the sum of votes. Hence, some number
/// bigger than u64::max_value() is needed. For maximum accuracy we simply use u128;
const DEN: u128 = u128::max_value();

/// A candidate entity for phragmen election.
#[derive(Clone, Default)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Candidate<AccountId> {
	/// Identifier.
	pub who: AccountId,
	/// Intermediary value used to sort candidates.
	pub score: Rational128,
	/// Sum of the stake of this candidate based on received votes.
	approval_stake: ExtendedBalance,
	/// Flag for being elected.
	elected: bool,
}

/// A voter entity.
#[derive(Clone, Default)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Voter<AccountId> {
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
#[derive(Clone, Default)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Edge<AccountId> {
	/// Identifier.
	who: AccountId,
	/// Load of this vote.
	load: Rational128,
	/// Index of the candidate stored in the 'candidates' vector.
	candidate_index: usize,
}

/// Means a particular `AccountId` was backed by `Perbill`th of a nominator's stake.
pub type PhragmenAssignment<AccountId> = (AccountId, Perbill);

/// Means a particular `AccountId` was backed by `ExtendedBalance` of a nominator's stake.
pub type PhragmenStakedAssignment<AccountId> = (AccountId, ExtendedBalance);

/// Final result of the phragmen election.
pub struct PhragmenResult<AccountId> {
	/// Just winners.
	pub winners: Vec<AccountId>,
	/// Individual assignments. for each tuple, the first elements is a voter and the second
	/// is the list of candidates that it supports.
	pub assignments: Vec<(AccountId, Vec<PhragmenAssignment<AccountId>>)>
}

/// A structure to demonstrate the phragmen result from the perspective of the candidate, i.e. how
/// much support each candidate is receiving.
///
/// This complements the [`PhragmenResult`] and is needed to run the equalize post-processing.
///
/// This, at the current version, resembles the `Exposure` defined in the staking SRML module, yet
/// they do not necessarily have to be the same.
#[derive(Default)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Support<AccountId> {
	/// The amount of support as the effect of self-vote.
	pub own: ExtendedBalance,
	/// Total support.
	pub total: ExtendedBalance,
	/// Support from voters.
	pub others: Vec<PhragmenStakedAssignment<AccountId>>,
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
/// * `self_vote`. If true, then each candidate will automatically vote for themselves with the a
///   weight indicated by their stake. Note that when this is `true` candidates are filtered by
/// having at least some backed stake from themselves.
pub fn elect<AccountId, Balance, FS, C>(
	candidate_count: usize,
	minimum_candidate_count: usize,
	initial_candidates: Vec<AccountId>,
	initial_voters: Vec<(AccountId, Vec<AccountId>)>,
	stake_of: FS,
	self_vote: bool,
) -> Option<PhragmenResult<AccountId>> where
	AccountId: Default + Ord + Member,
	Balance: Default + Copy + SimpleArithmetic,
	for<'r> FS: Fn(&'r AccountId) -> Balance,
	C: Convert<Balance, u64> + Convert<u128, Balance>,
{
	let to_votes = |b: Balance| <C as Convert<Balance, u64>>::convert(b) as ExtendedBalance;

	// return structures
	let mut elected_candidates: Vec<AccountId>;
	let mut assigned: Vec<(AccountId, Vec<PhragmenAssignment<AccountId>>)>;

	// used to cache and access candidates index.
	let mut c_idx_cache = BTreeMap::<AccountId, usize>::new();

	// voters list.
	let num_voters = initial_candidates.len() + initial_voters.len();
	let mut voters: Vec<Voter<AccountId>> = Vec::with_capacity(num_voters);

	// collect candidates. self vote or filter might apply
	let mut candidates = if self_vote {
		// self vote. filter.
		initial_candidates.into_iter().map(|who| {
			let stake = stake_of(&who);
			Candidate { who, approval_stake: to_votes(stake), ..Default::default() }
		})
		.filter(|c| !c.approval_stake.is_zero())
		.enumerate()
		.map(|(i, c)| {
			voters.push(Voter {
				who: c.who.clone(),
				edges: vec![Edge { who: c.who.clone(), candidate_index: i, ..Default::default() }],
				budget: c.approval_stake,
				load: Rational128::zero(),
			});
			c_idx_cache.insert(c.who.clone(), i);
			c
		})
		.collect::<Vec<Candidate<AccountId>>>()
	} else {
		// no self vote. just collect.
		initial_candidates.into_iter()
			.enumerate()
			.map(|(idx, who)| {
				c_idx_cache.insert(who.clone(), idx);
				Candidate { who, ..Default::default() }
			})
			.collect::<Vec<Candidate<AccountId>>>()
	};

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
				// 1 / approval_stake == (DEN / approval_stake) / DEN
				c.score = Rational128::from(DEN / c.approval_stake, DEN);
			}
		}

		// loop 2: increment score
		for n in &voters {
			for e in &n.edges {
				let c = &mut candidates[e.candidate_index];
				if !c.elected && !c.approval_stake.is_zero() {
					let temp_n = safe_multiply_by_rational(n.load.n(), n.budget, c.approval_stake);
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
			elected_candidates.push(winner.who.clone());
		} else {
			break
		}
	} // end of all rounds

	// update backing stake of candidates and voters
	for n in &mut voters {
		let mut assignment = (n.who.clone(), vec![]);
		for e in &mut n.edges {
			if let Some(c) = elected_candidates.iter().cloned().find(|c| *c == e.who) {
				if c != n.who {
					let per_bill_parts =
					{
						if n.load == e.load {
							// Full support. No need to calculate.
							ACCURACY
						} else {
							if e.load.d() == n.load.d() {
								let nom = if let Some(x) = ACCURACY.checked_mul(e.load.n()) {
									// check if we can peacefully compute the desired accuracy
									x / n.load.n()
								} else {
									// Presumably both numbers are quite large. Shifting both
									// will preserve the ratio.
									let n_load = n.load.n() >> 32;
									let e_load = e.load.n() >> 32;
									// defensive only. This can never saturate.
									e_load.saturating_mul(ACCURACY) / n_load
								};
								nom
							} else {
								// defensive only. Both edge and nominator loads are built from
								// scores, hence MUST have the same denominator.
								Zero::zero()
							}
						}
					};
					let per_thing = Perbill::from_parts(per_bill_parts.min(ACCURACY) as u32);
					assignment.1.push((e.who.clone(), per_thing));
				}
			}
		}

		if assignment.1.len() > 0 {
			// To ensure an assertion indicating: no stake from the nominator going to waste,
			// we add a minimal post-processing to equally assign all of the leftover stake ratios.
			let vote_count = assignment.1.len() as u32;
			let len = assignment.1.len();
			let sum = assignment.1.iter()
				.map(|a| a.1.deconstruct())
				.sum::<u32>();
			let accuracy = Perbill::accuracy();
			let diff = accuracy.checked_sub(sum).unwrap_or(0);
			let diff_per_vote = (diff / vote_count).min(accuracy);

			if diff_per_vote > 0 {
				for i in 0..len {
					let current_ratio = assignment.1[i % len].1;
					let next_ratio = current_ratio.saturating_add(Perbill::from_parts(diff_per_vote));
					assignment.1[i % len].1 = next_ratio;
				}
			}

			// `remainder` is set to be less than maximum votes of a nominator (currently 16).
			// safe to cast it to usize.
			let remainder = diff - diff_per_vote * vote_count;
			for i in 0..remainder as usize {
				let current_ratio = assignment.1[i % len].1;
				let next_ratio = current_ratio.saturating_add(Perbill::from_parts(1));
				assignment.1[i % len].1 = next_ratio;
			}
			assigned.push(assignment);
		}
	}

	Some(PhragmenResult {
		winners: elected_candidates,
		assignments: assigned,
	})
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
	mut assignments: Vec<(AccountId, Vec<PhragmenStakedAssignment<AccountId>>)>,
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

		for (voter, assignment) in assignments.iter_mut() {
			let voter_budget = stake_of(&voter);

			let diff = do_equalize::<_, _, C>(
				voter,
				voter_budget,
				assignment,
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
	elected_edges: &mut Vec<PhragmenStakedAssignment<AccountId>>,
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
	// Defensive only. Assignment list should always be populated.
	if elected_edges.is_empty() { return 0; }

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
			support.others.retain(|i_support| i_support.0 != *voter);
		}
		e.1 = 0;
	});

	elected_edges.sort_unstable_by_key(|e|
		if let Some(e) = support_map.get(&e.0) { e.total } else { Zero::zero() }
	);

	let mut cumulative_stake: ExtendedBalance = 0;
	let mut last_index = elected_edges.len() - 1;
	elected_edges.iter_mut().enumerate().for_each(|(idx, e)| {
		if let Some(support) = support_map.get_mut(&e.0) {
			let stake: ExtendedBalance = support.total;
			let stake_mul = stake.saturating_mul(idx as ExtendedBalance);
			let stake_sub = stake_mul.saturating_sub(cumulative_stake);
			if stake_sub > budget {
				last_index = idx.checked_sub(1).unwrap_or(0);
				return
			}
			cumulative_stake = cumulative_stake.saturating_add(stake);
		}
	});

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
			support.others.push((voter.clone(), e.1));
		}
	});

	difference
}

#[cfg(test)]
mod tests {
	use super::{elect, PhragmenResult};
	use sr_primitives::traits::{Convert, Member, SaturatedConversion};
	use sr_primitives::Perbill;
	use rstd::collections::btree_map::BTreeMap;
	use support::assert_eq_uvec;

	pub struct C;
	impl Convert<u64, u64> for C {
		fn convert(x: u64) -> u64 { x }
	}
	impl Convert<u128, u64> for C {
		fn convert(x: u128) -> u64 { x.saturated_into() }
	}

	#[derive(Default, Debug)]
	struct _Candidate<AccountId> {
		who: AccountId,
		score: f64,
		approval_stake: f64,
		elected: bool,
	}

	#[derive(Default, Debug)]
	struct _Voter<AccountId> {
		who: AccountId,
		edges: Vec<_Edge<AccountId>>,
		budget: f64,
		load: f64,
	}

	#[derive(Default, Debug)]
	struct _Edge<AccountId> {
		who: AccountId,
		load: f64,
		candidate_index: usize,
	}

	type _PhragmenAssignment<AccountId> = (AccountId, f64);

	#[derive(Debug)]
	pub struct _PhragmenResult<AccountId> {
		pub winners: Vec<AccountId>,
		pub assignments: Vec<(AccountId, Vec<_PhragmenAssignment<AccountId>>)>
	}

	pub fn elect_poc<AccountId, FS>(
		candidate_count: usize,
		minimum_candidate_count: usize,
		initial_candidates: Vec<AccountId>,
		initial_voters: Vec<(AccountId, Vec<AccountId>)>,
		stake_of: FS,
		self_vote: bool,
	) -> Option<_PhragmenResult<AccountId>> where
		AccountId: Default + Ord + Member + Copy,
		for<'r> FS: Fn(&'r AccountId) -> u64,
	{
		let mut elected_candidates: Vec<AccountId>;
		let mut assigned: Vec<(AccountId, Vec<_PhragmenAssignment<AccountId>>)>;
		let mut c_idx_cache = BTreeMap::<AccountId, usize>::new();
		let num_voters = initial_candidates.len() + initial_voters.len();
		let mut voters: Vec<_Voter<AccountId>> = Vec::with_capacity(num_voters);

		let mut candidates = if self_vote {
			initial_candidates.into_iter().map(|who| {
				let stake = stake_of(&who) as f64;
				_Candidate { who, approval_stake: stake, ..Default::default() }
			})
			.filter(|c| c.approval_stake != 0f64)
			.enumerate()
			.map(|(i, c)| {
				let who = c.who;
				voters.push(_Voter {
					who: who.clone(),
					edges: vec![
						_Edge { who: who.clone(), candidate_index: i, ..Default::default() }
					],
					budget: c.approval_stake,
					load: 0f64,
				});
				c_idx_cache.insert(c.who.clone(), i);
				c
			})
			.collect::<Vec<_Candidate<AccountId>>>()
		} else {
			initial_candidates.into_iter()
				.enumerate()
				.map(|(idx, who)| {
					c_idx_cache.insert(who.clone(), idx);
					_Candidate { who, ..Default::default() }
				})
				.collect::<Vec<_Candidate<AccountId>>>()
		};

		if candidates.len() < minimum_candidate_count {
			return None;
		}

		voters.extend(initial_voters.into_iter().map(|(who, votes)| {
			let voter_stake = stake_of(&who) as f64;
			let mut edges: Vec<_Edge<AccountId>> = Vec::with_capacity(votes.len());
			for v in votes {
				if let Some(idx) = c_idx_cache.get(&v) {
					candidates[*idx].approval_stake = candidates[*idx].approval_stake + voter_stake;
					edges.push(
						_Edge { who: v.clone(), candidate_index: *idx, ..Default::default() }
					);
				}
			}
			_Voter {
				who,
				edges: edges,
				budget: voter_stake,
				load: 0f64,
			}
		}));

		let to_elect = candidate_count.min(candidates.len());
		elected_candidates = Vec::with_capacity(candidate_count);
		assigned = Vec::with_capacity(candidate_count);

		for _round in 0..to_elect {
			for c in &mut candidates {
				if !c.elected {
					c.score = 1.0 / c.approval_stake;
				}
			}
			for n in &voters {
				for e in &n.edges {
					let c = &mut candidates[e.candidate_index];
					if !c.elected && !(c.approval_stake == 0f64) {
						c.score += n.budget * n.load / c.approval_stake;
					}
				}
			}

			if let Some(winner) = candidates
				.iter_mut()
				.filter(|c| !c.elected)
				.min_by(|x, y| x.score.partial_cmp(&y.score).unwrap_or(rstd::cmp::Ordering::Equal))
			{
				winner.elected = true;
				for n in &mut voters {
					for e in &mut n.edges {
						if e.who == winner.who {
							e.load = winner.score - n.load;
							n.load = winner.score;
						}
					}
				}

				elected_candidates.push(winner.who.clone());
			} else {
				break
			}
		}

		for n in &mut voters {
			let mut assignment = (n.who.clone(), vec![]);
			for e in &mut n.edges {
				if let Some(c) = elected_candidates.iter().cloned().find(|c| *c == e.who) {
					if c != n.who {
						let ratio = e.load / n.load;
						assignment.1.push((e.who.clone(), ratio));
					}
				}
			}
			assigned.push(assignment);
		}

		Some(_PhragmenResult {
			winners: elected_candidates,
			assignments: assigned,
		})
	}

	fn per(p: f64) -> Perbill {
		Perbill::from_fraction(p)
	}

	#[test]
	fn float_poc_works() {
		let candidates = vec![1, 2, 3];
		let voters = vec![
			(10, vec![1, 2]),
			(20, vec![1, 3]),
			(30, vec![2, 3]),
		];
		let stake_of = |x: &u64| { if *x >= 10 { *x }  else { 0 }};
		let _PhragmenResult { winners, assignments } =
			elect_poc(2, 2, candidates, voters, stake_of, false).unwrap();

		assert_eq_uvec!(winners, vec![2, 3]);
		assert_eq_uvec!(
			assignments,
			vec![
				(10, vec![(2, 1.0)]),
				(20, vec![(3, 1.0)]),
				(30, vec![(2, 0.5), (3, 0.5)])
			]
		);
	}

	#[test]
	fn phragmen_works() {
		let candidates = vec![1, 2, 3];
		let voters = vec![
			(10, vec![1, 2]),
			(20, vec![1, 3]),
			(30, vec![2, 3]),
		];
		let stake_of = |x: &u64| { if *x >= 10 { *x }  else { 0 }};
		let PhragmenResult { winners, assignments } =
			elect::<_, _, _, C>(2, 2, candidates, voters, stake_of, false).unwrap();

		assert_eq_uvec!(winners, vec![2, 3]);
		assert_eq_uvec!(
			assignments,
			vec![
				(10, vec![(2, per(1.0))]),
				(20, vec![(3, per(1.0))]),
				(30, vec![(2, per(0.5)), (3, per(0.5))])
			]
		);
	}
}
