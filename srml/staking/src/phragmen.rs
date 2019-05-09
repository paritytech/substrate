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
use primitives::{PerU128};
use primitives::traits::{Zero, Convert, Saturating};
use parity_codec::{Encode, Decode};
use crate::{BalanceOf, Assignment, RawAssignment, ExpoMap, Trait, ValidatorPrefs};

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
#[derive(Clone, Encode, Decode, Default)]
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

/// Wrapper around the nomination info of a single nominator for a group of validators.
#[derive(Clone, Encode, Decode, Default)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Nominator<AccountId> {
	/// The nominator's account.
	who: AccountId,
	/// List of validators proposed by this nominator.
	edges: Vec<Edge<AccountId>>,
	/// the stake amount proposed by the nominator as a part of the vote.
	budget: ExtendedBalance,
	/// Incremented each time a nominee that this nominator voted for has been elected.
	load: Fraction,
}

/// Wrapper around a nominator vote and the load of that vote.
#[derive(Clone, Encode, Decode, Default)]
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

/// Perform election based on Phragmén algorithm.
///
/// Reference implementation: https://github.com/w3f/consensus
///
/// Returns an Option of elected candidates, if election is performed.
/// Returns None if not enough candidates exist.
///
/// The returned Option is a tuple consisting of:
///   - The list of elected candidates.
///   - The list of nominators and their associated vote weights.
pub fn elect<T: Trait + 'static, FV, FN, FS>(
	validator_count: usize,
	minimum_validator_count: usize,
	validator_iter: FV,
	nominator_iter: FN,
	stash_of: FS,
) -> Option<(Vec<T::AccountId>, Vec<(T::AccountId, Vec<RawAssignment<T>>)>)> where
	FV: Iterator<Item=(T::AccountId, ValidatorPrefs<BalanceOf<T>>)>,
	FN: Iterator<Item=(T::AccountId, Vec<T::AccountId>)>,
	for <'r> FS: Fn(&'r T::AccountId) -> BalanceOf<T>,
{
	let to_votes = |b: BalanceOf<T>| <T::CurrencyToVote as Convert<BalanceOf<T>, u64>>::convert(b) as ExtendedBalance;

	// return structures
	let mut elected_candidates: Vec<T::AccountId>;
	let mut assigned: Vec<(T::AccountId, Vec<RawAssignment<T>>)>;
	let mut c_idx_cache = BTreeMap::<T::AccountId, usize>::new();

	// 1- Pre-process candidates and place them in a container, optimisation and add phantom votes.
	// Candidates who have 0 stake => have no votes or all null-votes. Kick them out not.
	let mut nominators: Vec<Nominator<T::AccountId>> = Vec::with_capacity(validator_iter.size_hint().0 + nominator_iter.size_hint().0);
	let mut candidates = validator_iter.map(|(who, _)| {
			let stash_balance = stash_of(&who);
			(Candidate { who, ..Default::default() }, stash_balance)
		})
		.filter_map(|(mut c, s)| {
			c.approval_stake += to_votes(s);
			if c.approval_stake.is_zero() {
				None
			} else {
				Some((c, s))
			}
		})
		.enumerate()
		.map(|(idx, (c, s))| {
			nominators.push(Nominator {
				who: c.who.clone(),
				edges: vec![ Edge { who: c.who.clone(), candidate_index: idx, ..Default::default() }],
				budget: to_votes(s),
				load: Fraction::zero(),
			});
			c_idx_cache.insert(c.who.clone(), idx);
			c
		})
		.collect::<Vec<Candidate<T::AccountId>>>();

	// 2- Collect the nominators with the associated votes.
	// Also collect approval stake along the way.
	nominators.extend(nominator_iter.map(|(who, nominees)| {
		let nominator_stake = stash_of(&who);
		let mut edges: Vec<Edge<T::AccountId>> = Vec::with_capacity(nominees.len());
		for n in &nominees {
			if let Some(idx) = c_idx_cache.get(n) {
				// This candidate is valid + already cached.
				candidates[*idx].approval_stake = candidates[*idx].approval_stake
					.saturating_add(to_votes(nominator_stake));
				edges.push(Edge { who: n.clone(), candidate_index: *idx, ..Default::default() });
			} // else {} would be wrong votes. We don't really care about it.
		}
		Nominator {
			who,
			edges: edges,
			budget: to_votes(nominator_stake),
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
			for n in &nominators {
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
						c.score = Fraction::from_max_value((*c.score).saturating_add(temp));
					}
				}
			}

			// Find the best
			if let Some(winner) = candidates
				.iter_mut()
				.filter(|c| !c.elected)
				.min_by_key(|c| *c.score)
			{
				// loop 3: update nominator and edge load
				winner.elected = true;
				for n in &mut nominators {
					for e in &mut n.edges {
						if e.who == winner.who {
							e.load = Fraction::from_max_value(*winner.score - *n.load);
							n.load = winner.score;
						}
					}
				}

				elected_candidates.push(winner.who.clone());
			} else {
				break
			}
		} // end of all rounds

		// 4.1- Update backing stake of candidates and nominators
		for n in &mut nominators {
			let mut assignment = (n.who.clone(), vec![]);
			for e in &mut n.edges {
				if let Some(c) = elected_candidates.iter().find(|c| **c == e.who) {
					if *c != n.who {
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
				// To ensure an assertion indicating: no stake from the nominator going to waste,
				// we add a minimal post-processing to equally assign all of the leftover stake ratios.
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

				// `remainder` is set to be less than maximum votes of a nominator (currently 16).
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
	Some((elected_candidates, assigned))
}

/// Performs equalize post-processing to the output of the election algorithm
/// This function mutates the input parameters, most noticeably it updates the exposure of
/// the elected candidates.
///
/// No value is returned from the function and the `expo_map` parameter is updated.
pub fn equalize<T: Trait + 'static>(
	assignments: &mut Vec<(T::AccountId, BalanceOf<T>, Vec<Assignment<T>>)>,
	expo_map: &mut ExpoMap<T>,
	tolerance: ExtendedBalance,
	iterations: usize,
) {
	for _i in 0..iterations {
		let mut max_diff = 0;
		assignments.iter_mut().for_each(|(n, budget, assignment)| {
			let diff = do_equalize::<T>(&n, *budget, assignment, expo_map, tolerance);
			if diff > max_diff {
				max_diff = diff;
			}
		});
		if max_diff < tolerance {
			break;
		}
	}
}

fn do_equalize<T: Trait + 'static>(
	nominator: &T::AccountId,
	budget_balance: BalanceOf<T>,
	elected_edges_balance: &mut Vec<Assignment<T>>,
	expo_map: &mut ExpoMap<T>,
	tolerance: ExtendedBalance
) -> ExtendedBalance {
	let to_votes = |b: BalanceOf<T>| <T::CurrencyToVote as Convert<BalanceOf<T>, u64>>::convert(b) as ExtendedBalance;
	let to_balance = |v: ExtendedBalance| <T::CurrencyToVote as Convert<ExtendedBalance, BalanceOf<T>>>::convert(v);
	let budget = to_votes(budget_balance);

	// Convert all stakes to extended. Result is Vec<(Acc, Ratio, Balance)>
	let mut elected_edges = elected_edges_balance
		.into_iter()
		.map(|e| (e.0.clone(), e.1, to_votes(e.2)))
		.collect::<Vec<(T::AccountId, ExtendedBalance, ExtendedBalance)>>();

	let stake_used = elected_edges
		.iter()
		.fold(0 as ExtendedBalance, |s, e| s.saturating_add(e.2));

	let backed_stakes_iter = elected_edges
		.iter()
		.filter_map(|e| expo_map.get(&e.0))
		.map(|e| to_votes(e.total));

	let backing_backed_stake = elected_edges
		.iter()
		.filter(|e| e.2 > 0)
		.filter_map(|e| expo_map.get(&e.0))
		.map(|e| to_votes(e.total))
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

	// Undo updates to exposure
	elected_edges.iter_mut().for_each(|e| {
		if let Some(expo) = expo_map.get_mut(&e.0) {
			expo.total = expo.total.saturating_sub(to_balance(e.2));
		}
		e.2 = 0;
	});

	elected_edges.sort_unstable_by_key(|e| e.2);

	let mut cumulative_stake: ExtendedBalance = 0;
	let mut last_index = elected_edges.len() - 1;
	elected_edges.iter_mut().enumerate().for_each(|(idx, e)| {
		if let Some(expo) = expo_map.get_mut(&e.0) {
			let stake: ExtendedBalance = to_votes(expo.total);

			let stake_mul = stake.saturating_mul(idx as ExtendedBalance);
			let stake_sub = stake_mul.saturating_sub(cumulative_stake);
			if stake_sub > budget {
				last_index = idx.checked_sub(1).unwrap_or(0);
				return
			}
			cumulative_stake = cumulative_stake.saturating_add(stake);
		}
	});

	let last_stake = elected_edges[last_index].2;
	let split_ways = last_index + 1;
	let excess = budget
		.saturating_add(cumulative_stake)
		.saturating_sub(last_stake.saturating_mul(split_ways as ExtendedBalance));
	elected_edges.iter_mut().take(split_ways).for_each(|e| {
		if let Some(expo) = expo_map.get_mut(&e.0) {
			e.2 = (excess / split_ways as ExtendedBalance)
				.saturating_add(last_stake)
				.saturating_sub(to_votes(expo.total));
			expo.total = expo.total.saturating_add(to_balance(e.2));
			if let Some(i_expo) = expo.others.iter_mut().find(|i| i.who == nominator.clone()) {
				i_expo.value = to_balance(e.2);
			}
		}
	});

	// Store back the individual edge weights.
	elected_edges.iter().enumerate().for_each(|(idx, e)| elected_edges_balance[idx].2 = to_balance(e.2));

	difference
}
