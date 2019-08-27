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

//! Rust implementation of the Phragmén election algorithm.

use rstd::{prelude::*, collections::btree_map::BTreeMap};
use crate::PerU128;
use crate::traits::{Zero, Convert, Member, SimpleArithmetic};

/// Type used as the fraction.
type Fraction = PerU128;
/// Wrapper around the type used as the _safe_ wrapper around a `balance`.
pub type ExtendedBalance = u128;

// this is only used while creating the candidate score. Due to reasons explained below
// The more accurate this is, the less likely we choose a wrong candidate.
const SCALE_FACTOR: ExtendedBalance = u32::max_value() as ExtendedBalance + 1;
/// These are used to expose a fixed accuracy to the caller function. The bigger they are,
/// the more accurate we get, but the more likely it is for us to overflow. The case of overflow
/// is handled but accuracy will be lost. 32 or 16 are reasonable values.
pub const ACCURACY: ExtendedBalance = u32::max_value() as ExtendedBalance + 1;

/// Wrapper around validation candidates some metadata.
#[derive(Clone, Default)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Candidate<AccountId> {
	/// The validator's account
	pub who: AccountId,
	/// Intermediary value used to sort candidates.
	pub score: Fraction,
	/// Accumulator of the stake of this candidate based on received votes.
	approval_stake: ExtendedBalance,
	/// Flag for being elected.
	elected: bool,
}

/// Wrapper around the nomination info of a single voter for a group of validators.
#[derive(Clone, Default)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Voter<AccountId> {
	/// The voter's account.
	who: AccountId,
	/// List of validators proposed by this voter.
	edges: Vec<Edge<AccountId>>,
	/// the stake amount proposed by the voter as a part of the vote.
	budget: ExtendedBalance,
	/// Incremented each time a nominee that this voter voted for has been elected.
	load: Fraction,
}

/// Wrapper around a voter's vote and the load of that vote.
#[derive(Clone, Default)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Edge<AccountId> {
	/// Account being voted for
	who: AccountId,
	/// Load of this vote.
	load: Fraction,
	/// Equal to `edge.load / nom.load`. Stored only to be used with post-processing.
	ratio: ExtendedBalance,
	/// Index of the candidate stored in the 'candidates' vector.
	candidate_index: usize,
}

/// A ratio of a voter's vote, indicated by `ExtendedBalance` / `ACCURACY`.
pub type PhragmenAssignment<AccountId> = (AccountId, ExtendedBalance);

/// Final result of the phragmen election.
pub struct PhragmenResult<AccountId> {
	/// Just winners.
	pub winners: Vec<AccountId>,
	/// individual assignments. for each tuple, the first elements is a voter and the second
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
	pub others: Vec<PhragmenAssignment<AccountId>>,
}

/// A linkage from a candidate and its [`Support`].
pub type SupportMap<A> = BTreeMap<A, Support<A>>;

/// Perform election based on Phragmén algorithm.
///
/// Reference implementation: https://github.com/w3f/consensus
///
/// Returns an `Option` the set of winners and their detailed support ratio from each voter if
/// enough candidates are provided. Returns `None` otherwise.
///
///
pub fn elect<AccountId, Balance, FS, C>(
	validator_count: usize,
	minimum_validator_count: usize,
	initial_candidates: Vec<AccountId>,
	initial_voters: Vec<(AccountId, Vec<AccountId>)>,
	slashable_balance_of: FS,
	self_vote: bool,
) -> Option<PhragmenResult<AccountId>> where
	AccountId: Default + Ord + Member,
	Balance: Default + Copy + SimpleArithmetic,
	for <'r> FS: Fn(&'r AccountId) -> Balance,
	C: Convert<Balance, u64> + Convert<u128, Balance>,
{
	let to_votes = |b: Balance|
		<C as Convert<Balance, u64>>::convert(b) as ExtendedBalance;

	// return structures
	let mut elected_candidates: Vec<AccountId>;
	let mut assigned: Vec<(AccountId, Vec<PhragmenAssignment<AccountId>>)>;

	let mut c_idx_cache = BTreeMap::<AccountId, usize>::new();

	// 1- Pre-process candidates and place them in a container, optimisation and add phantom votes.
	// Candidates who have 0 stake => have no votes or all null-votes. Kick them out not.
	let mut voters: Vec<Voter<AccountId>> = Vec::with_capacity(initial_candidates.len() + initial_voters.len());
	let mut candidates = if self_vote {
		initial_candidates.into_iter().map(|who| {
			let stake = slashable_balance_of(&who);
			Candidate { who, approval_stake: to_votes(stake), ..Default::default() }
		})
		.filter_map(|c| {
			if c.approval_stake.is_zero() {
				None
			} else {
				Some(c)
			}
		})
		.enumerate()
		.map(|(idx, c)| {
			voters.push(Voter {
				who: c.who.clone(),
				edges: vec![ Edge { who: c.who.clone(), candidate_index: idx, ..Default::default() }],
				budget: c.approval_stake,
				load: Fraction::zero(),
			});
			c_idx_cache.insert(c.who.clone(), idx);
			c
		})
		.collect::<Vec<Candidate<AccountId>>>()
	} else {
		initial_candidates.into_iter()
			.enumerate()
			.map(|(idx, who)| {
				c_idx_cache.insert(who.clone(), idx);
				Candidate { who, ..Default::default() }
			})
			.collect::<Vec<Candidate<AccountId>>>()
	};

	// 2- collect the voters with the associated votes.
	// Also collect approval stake along the way.
	voters.extend(initial_voters.into_iter().map(|(who, nominees)| {
		let voter_stake = slashable_balance_of(&who);
		let mut edges: Vec<Edge<AccountId>> = Vec::with_capacity(nominees.len());
		for n in nominees {
			if let Some(idx) = c_idx_cache.get(&n) {
				// This candidate is valid + already cached.
				candidates[*idx].approval_stake = candidates[*idx].approval_stake
					.saturating_add(to_votes(voter_stake));
				edges.push(Edge { who: n.clone(), candidate_index: *idx, ..Default::default() });
			} // else {} would be wrong votes. We don't really care about it.
		}
		Voter {
			who,
			edges: edges,
			budget: to_votes(voter_stake),
			load: Fraction::zero(),
		}
	}));

	// 4- If we have more candidates then needed, run Phragmén.
	if candidates.len() >= minimum_validator_count {
		let validator_count = validator_count.min(candidates.len());
		elected_candidates = Vec::with_capacity(validator_count);
		assigned = Vec::with_capacity(validator_count);

		// Main election loop
		for _round in 0..validator_count {
			// Loop 1: initialize score
			for c in &mut candidates {
				if !c.elected {
					c.score = Fraction::from_xth(c.approval_stake);
				}
			}
			// Loop 2: increment score.
			for n in &voters {
				for e in &n.edges {
					let c = &mut candidates[e.candidate_index];
					if !c.elected && !c.approval_stake.is_zero() {
						// Basic fixed-point shifting by 32.
						// `n.budget.saturating_mul(SCALE_FACTOR)` will never saturate
						// since n.budget cannot exceed u64,despite being stored in u128. yet,
						// `*n.load / SCALE_FACTOR` might collapse to zero. Hence, 32 or 16 bits are better scale factors.
						// Note that left-associativity in operators precedence is crucially important here.
						let temp =
							n.budget.saturating_mul(SCALE_FACTOR) / c.approval_stake
							* (*n.load / SCALE_FACTOR);
						c.score = Fraction::from_parts((*c.score).saturating_add(temp));
					}
				}
			}

			// Find the best
			if let Some(winner) = candidates
				.iter_mut()
				.filter(|c| !c.elected)
				.min_by_key(|c| *c.score)
			{
				// loop 3: update voter and edge load
				winner.elected = true;
				for n in &mut voters {
					for e in &mut n.edges {
						if e.who == winner.who {
							e.load = Fraction::from_parts(*winner.score - *n.load);
							n.load = winner.score;
						}
					}
				}

				elected_candidates.push(winner.who.clone());
			} else {
				break
			}
		} // end of all rounds

		// 4.1- Update backing stake of candidates and voters
		for n in &mut voters {
			let mut assignment = (n.who.clone(), vec![]);
			for e in &mut n.edges {
				if let Some(c) = elected_candidates.iter().cloned().find(|c| *c == e.who) {
					if c != n.who {
						let ratio = {
							// Full support. No need to calculate.
							if *n.load == *e.load { ACCURACY }
							else {
								// This should not saturate. Safest is to just check
								if let Some(r) = ACCURACY.checked_mul(*e.load) {
									r / n.load.max(1)
								} else {
									// Just a simple trick.
									*e.load / (n.load.max(1) / ACCURACY)
								}
							}
						};
						e.ratio = ratio;
						assignment.1.push((e.who.clone(), ratio));
					}
				}
			}

			if assignment.1.len() > 0 {
				// To ensure an assertion indicating: no stake from the voter going to waste, we add
				//  a minimal post-processing to equally assign all of the leftover stake ratios.
				let vote_count = assignment.1.len() as ExtendedBalance;
				let l = assignment.1.len();
				let sum = assignment.1.iter().map(|a| a.1).sum::<ExtendedBalance>();
				let diff = ACCURACY.checked_sub(sum).unwrap_or(0);
				let diff_per_vote= diff / vote_count;

				if diff_per_vote > 0 {
					for i in 0..l {
						assignment.1[i%l].1 =
							assignment.1[i%l].1
							.saturating_add(diff_per_vote);
					}
				}

				// `remainder` is set to be less than maximum votes of a voter (currently 16).
				// safe to cast it to usize.
				let remainder = diff - diff_per_vote * vote_count;
				for i in 0..remainder as usize {
					assignment.1[i%l].1 =
						assignment.1[i%l].1
						.saturating_add(1);
				}
				assigned.push(assignment);
			}
		}

	} else {
		// if we have less than minimum, use the previous validator set.
		return None
	}

	Some(PhragmenResult {
		winners: elected_candidates,
		assignments: assigned,
	})
}

/// Performs equalize post-processing to the output of the election algorithm
/// This function mutates the input parameters, most noticeably it updates the exposure of
/// the elected candidates.
///
/// No value is returned from the function and the `expo_map` parameter is updated.
pub fn equalize<Balance, AccountId, C, FS>(
	mut assignments: Vec<(AccountId, Vec<PhragmenAssignment<AccountId>>)>,
	supports: &mut SupportMap<AccountId>,
	tolerance: ExtendedBalance,
	iterations: usize,
	slashable_balance_of: FS,
) where
	C: Convert<Balance, u64> + Convert<u128, Balance>,
	for <'r> FS: Fn(&'r AccountId) -> Balance,
	AccountId: Ord + Clone,
{
	// prepare the data for equalise
	for _i in 0..iterations {
		let mut max_diff = 0;

		for (voter, assignment) in assignments.iter_mut() {
			let voter_budget = slashable_balance_of(&voter);

			let diff = do_equalize::<_, _, C>(
				voter,
				voter_budget,
				assignment,
				supports,
				tolerance
			);
			if diff > max_diff { max_diff = diff; }
		}

		if max_diff < tolerance {
			break;
		}
	}
}

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
