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
use sr_primitives::{Perbill, Rational128};
use sr_primitives::traits::{Zero, Convert, Saturating};
use crate::{BalanceOf, ExpoMap, Trait, ValidatorPrefs, IndividualExposure};

/// Wrapper around the type used as the _safe_ wrapper around a `balance`.
pub type ExtendedBalance = u128;

/// An single assignment output of phragmen. Reads like: account `A` has a support ratio `Perbill`.
pub type PhragmenAssignment<A> = (A, Perbill);

/// The accuracy of the ratio type used in [`PhragmenAssignment`].
const ACCURACY: ExtendedBalance = Perbill::accuracy() as ExtendedBalance;

/// The denominator used for loads. Since votes are collected as u64, the smallest ratio that we
/// might collect is `1/approval_stake` where approval stake is the sum of votes. Hence, some number
/// bigger than u64::max_value() is needed. For maximum accuracy we simply use u128;
const DEN: u128 = u128::max_value();

/// Wrapper around validation candidates some metadata.
#[derive(Clone, Default)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Candidate<AccountId> {
	/// The validator's account
	pub who: AccountId,
	/// Intermediary value used to sort candidates.
	pub score: Rational128,
	/// Accumulator of the stake of this candidate based on received votes.
	approval_stake: ExtendedBalance,
	/// Flag for being elected.
	elected: bool,
}

/// Wrapper around the nomination info of a single nominator for a group of validators.
#[derive(Clone, Default)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Nominator<AccountId> {
	/// The nominator's account.
	who: AccountId,
	/// List of validators proposed by this nominator.
	edges: Vec<Edge<AccountId>>,
	/// the stake amount proposed by the nominator as a part of the vote.
	budget: ExtendedBalance,
	/// Incremented each time a nominee that this nominator voted for has been elected.
	load: Rational128,
}

/// Wrapper around a nominator vote and the load of that vote.
#[derive(Clone, Default)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Edge<AccountId> {
	/// Account being voted for
	who: AccountId,
	/// Load of this vote.
	load: Rational128,
	/// Equal to `edge.load / nom.load`. Stored only to be used with post-processing.
	ratio: Rational128,
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
) -> Option<(Vec<T::AccountId>, Vec<(T::AccountId, Vec<PhragmenAssignment<T::AccountId>>)>)> where
	FV: Iterator<Item=(T::AccountId, ValidatorPrefs<BalanceOf<T>>)>,
	FN: Iterator<Item=(T::AccountId, Vec<T::AccountId>)>,
	for <'r> FS: Fn(&'r T::AccountId) -> BalanceOf<T>,
{
	let to_votes = |b: BalanceOf<T>| <T::CurrencyToVote as Convert<BalanceOf<T>, u64>>::convert(b) as ExtendedBalance;

	// return structures
	let mut elected_candidates: Vec<T::AccountId>;
	let mut assigned: Vec<(T::AccountId, Vec<PhragmenAssignment<T::AccountId>>)>;
	let mut c_idx_cache = BTreeMap::<T::AccountId, usize>::new();

	// pre-process candidates and add phantom votes. Remove candidates with no approval stake.
	// also populates the `c_idx_cache` as a proof of candidacy and fast access.
	let mut nominators: Vec<Nominator<T::AccountId>> =
		Vec::with_capacity(validator_iter.size_hint().0 + nominator_iter.size_hint().0);
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
			load: Rational128::zero(),
		});
		c_idx_cache.insert(c.who.clone(), idx);
		c
	})
	.collect::<Vec<Candidate<T::AccountId>>>();

	// Collect the nominators with the associated votes. Also collect approval stake along the way.
	nominators.extend(nominator_iter.map(|(who, nominees)| {
		let nominator_stake = stash_of(&who);
		let mut edges: Vec<Edge<T::AccountId>> = Vec::with_capacity(nominees.len());
		for n in &nominees {
			if let Some(idx) = c_idx_cache.get(n) {
				// This candidate is valid + already cached.
				candidates[*idx].approval_stake = candidates[*idx].approval_stake
					.saturating_add(to_votes(nominator_stake));
				edges.push(Edge { who: n.clone(), candidate_index: *idx, ..Default::default() });
			} // else {} would be wrong votes (not a candidate). We don't really care about it.
		}
		Nominator {
			who,
			edges: edges,
			budget: to_votes(nominator_stake),
			load: Rational128::zero(),
		}
	}));

	//  if we have more candidates then needed, run Phragmén.
	if candidates.len() >= minimum_validator_count {
		let validator_count = validator_count.min(candidates.len());
		elected_candidates = Vec::with_capacity(validator_count);
		assigned = Vec::with_capacity(validator_count);
		// Main election loop
		for _round in 0..validator_count {
			// Loop 1: initialize score
			for c in &mut candidates {
				if !c.elected {
					// 1 / approval_stake == (DEN / approval_stake) / DEN
					c.score = Rational128::from(DEN / c.approval_stake, DEN);
				}
			}
			// Loop 2: increment score.
			for n in &nominators {
				for e in &n.edges {
					let c = &mut candidates[e.candidate_index];
					if !c.elected && !c.approval_stake.is_zero() {
						let temp_n = sr_primitives::safe_multiply_by_rational(n.load.n(), n.budget, c.approval_stake);
						let temp_d = n.load.d();
						let temp = Rational128::from(temp_n, temp_d);
						c.score = c.score.lazy_saturating_add(temp);
					}
				}
			}

			// Find the best
			if let Some(winner) = candidates
				.iter_mut()
				.filter(|c| !c.elected)
				.min_by_key(|c| c.score)
			{
				// loop 3: update nominator and edge load
				winner.elected = true;
				println!("winner = {:?}", winner);
				for n in &mut nominators {
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

		// 4.1- Update backing stake of candidates and nominators
		for n in &mut nominators {
			let mut assignment = (n.who.clone(), vec![]);
			for e in &mut n.edges {
				if let Some(c) = elected_candidates.iter().find(|c| **c == e.who) {
					if *c != n.who {
						let ratio = if n.load == e.load {
						// Full support. No need to calculate.
							Rational128::from(ACCURACY, ACCURACY)
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
								Rational128::from(nom, ACCURACY)
							} else {
								// defensive only. Both edge and nominator loads are built from
								// scores, hence MUST have the same denominator.
								panic!();
								Rational128::zero()
							}
						};
						e.ratio = ratio;
						// ratio is guaranteed to have denominator billion.
						let per_thing = Perbill::from_parts(ratio.n().min(ACCURACY) as u32);
						assignment.1.push((e.who.clone(), per_thing));
					}
				}
			}

			if assignment.1.len() > 0 {
				// To ensure an assertion indicating: no stake from the nominator going to waste,
				// we add a minimal post-processing to equally assign all of the leftover stake ratios.
				let vote_count = assignment.1.len() as u32;
				let l = assignment.1.len();
				let sum = assignment.1.iter()
					.map(|a| a.1.deconstruct())
					.sum::<u32>();
				let accuracy = Perbill::accuracy();
				let diff = accuracy.checked_sub(sum).unwrap_or(0);
				let diff_per_vote = (diff / vote_count).min(accuracy);

				if diff_per_vote > 0 {
					for i in 0..l {
						let new_parts = assignment.1[i%l].1.deconstruct().saturating_add(diff_per_vote);
						assignment.1[i%l].1 = Perbill::from_parts(new_parts);
					}
				}

				// `remainder` is set to be less than maximum votes of a nominator (currently 16).
				// safe to cast it to usize.
				let remainder = diff - diff_per_vote * vote_count;
				for i in 0..remainder as usize {
					// TODO: this can be written a bit nicer I assume.
					let new_parts = assignment.1[i%l].1.deconstruct().saturating_add(1);
					assignment.1[i%l].1 = Perbill::from_parts(new_parts);
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
	nominator_assignment: &mut Vec<(T::AccountId, BalanceOf<T>, Vec<(T::AccountId, ExtendedBalance)>)>,
	expo_map: &mut ExpoMap<T>,
	tolerance: ExtendedBalance,
	iterations: usize,
) {
	for _i in 0..iterations {
		let mut max_diff = 0;
		nominator_assignment.iter_mut().for_each(|(n, budget, assignments)| {
			let diff = do_equalize::<T>(&n, *budget, assignments, expo_map, tolerance);
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
	elected_edges: &mut Vec<(T::AccountId, ExtendedBalance)>,
	expo_map: &mut ExpoMap<T>,
	tolerance: ExtendedBalance
) -> ExtendedBalance {
	let to_votes = |b: BalanceOf<T>|
		<T::CurrencyToVote as Convert<BalanceOf<T>, u64>>::convert(b) as ExtendedBalance;
	let to_balance = |v: ExtendedBalance|
		<T::CurrencyToVote as Convert<ExtendedBalance, BalanceOf<T>>>::convert(v);
	let budget = to_votes(budget_balance);

	// Nothing to do. This nominator had nothing useful.
	// Defensive only. Assignment list should always be populated.
	if elected_edges.is_empty() { return 0; }

	let stake_used = elected_edges
		.iter()
		.fold(0 as ExtendedBalance, |s, e| s.saturating_add(e.1));

	let backed_stakes_iter = elected_edges
		.iter()
		.filter_map(|e| expo_map.get(&e.0))
		.map(|e| to_votes(e.total));

	let backing_backed_stake = elected_edges
		.iter()
		.filter(|e| e.1 > 0)
		.filter_map(|e| expo_map.get(&e.0))
		.map(|e| to_votes(e.total))
		.collect::<Vec<ExtendedBalance>>();

	let mut difference;
	if backing_backed_stake.len() > 0 && backed_stakes_iter.size_hint().0 > 0 {
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
			expo.total = expo.total.saturating_sub(to_balance(e.1));
			expo.others.retain(|i_expo| i_expo.who != *nominator);
		}
		e.1 = 0;
	});

	elected_edges.sort_unstable_by_key(|e|
		if let Some(e) = expo_map.get(&e.0) { e.total } else { Zero::zero() }
	);

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

	let last_stake = elected_edges[last_index].1;
	let split_ways = last_index + 1;
	let excess = budget
		.saturating_add(cumulative_stake)
		.saturating_sub(last_stake.saturating_mul(split_ways as ExtendedBalance));
	elected_edges.iter_mut().take(split_ways).for_each(|e| {
		if let Some(expo) = expo_map.get_mut(&e.0) {
			e.1 = (excess / split_ways as ExtendedBalance)
				.saturating_add(last_stake)
				.saturating_sub(to_votes(expo.total));
			expo.total = expo.total.saturating_add(to_balance(e.1));
			expo.others.push(IndividualExposure { who: nominator.clone(), value: to_balance(e.1)});
		}
	});

	difference
}
