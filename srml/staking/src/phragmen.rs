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

use rstd::prelude::*;
use primitives::PerU128;
use primitives::traits::{Zero, Saturating, Convert};
use parity_codec::{HasCompact, Encode, Decode};
use crate::{Exposure, BalanceOf, Trait, ValidatorPrefs, IndividualExposure};

type Fraction = PerU128;
type ExtendedBalance = u128;

/// Configure the behavior of the Phragmen election.
/// Might be deprecated.
pub struct ElectionConfig<Balance: HasCompact> {
	/// Perform equalize?.
	pub equalize: bool,
	/// Number of equalize iterations.
	pub iterations: usize,
	/// Tolerance of max change per equalize iteration.
	pub tolerance: Balance,
}

/// Wrapper around validation candidates some metadata.
#[derive(Clone, Encode, Decode, Default)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Candidate<AccountId, Balance: HasCompact> {
	/// The validator's account
	pub who: AccountId,
	/// Exposure struct, holding info about the value that the validator has in stake.
	pub exposure: Exposure<AccountId, Balance>,
	/// Intermediary value used to sort candidates.
	pub score: Fraction,
	/// Accumulator of the stake of this candidate based on received votes.
	approval_stake: ExtendedBalance,
	/// Flag for being elected.
	elected: bool,
	/// This is most often equal to `Exposure.total` but not always. Needed for [`equalize`]
	backing_stake: ExtendedBalance
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
	/// Final backing stake of this vote.
	backing_stake: ExtendedBalance,
	/// Index of the candidate stored in the 'candidates' vector
	candidate_index: usize,
	/// Index of the candidate stored in the 'elected_candidates' vector. Used only with equalize.
	elected_idx: usize,
	/// Indicates if this edge is a vote for an elected candidate. Used only with equalize.
	elected: bool,
}

/// Perform election based on Phragmén algorithm.
///
/// Reference implementation: https://github.com/w3f/consensus
///
/// Returns an Option of elected candidates, if election is performed.
/// Returns None if not enough candidates exist.
pub fn elect<T: Trait + 'static, FR, FN, FV, FS>(
		get_rounds: FR,
		get_validators: FV,
		get_nominators: FN,
		stash_of: FS,
		minimum_validator_count: usize,
		config: ElectionConfig<BalanceOf<T>>,
) -> Option<Vec<Candidate<T::AccountId, BalanceOf<T>>>> where
	FR: Fn() -> usize,
	FV: Fn() -> Box<dyn Iterator<
		Item =(T::AccountId, ValidatorPrefs<BalanceOf<T>>)
	>>,
	FN: Fn() -> Box<dyn Iterator<
		Item =(T::AccountId, Vec<T::AccountId>)
	>>,
	for <'r> FS: Fn(&'r T::AccountId) -> BalanceOf<T>,
{
	let expand = |b: BalanceOf<T>|    <T::CurrencyToVote as Convert<BalanceOf<T>, u64>>::convert(b) as ExtendedBalance;
	let shrink = |b: ExtendedBalance| <T::CurrencyToVote as Convert<ExtendedBalance, BalanceOf<T>>>::convert(b);
	let rounds = get_rounds();
	let mut elected_candidates;

	// 1- Pre-process candidates and place them in a container
	let mut candidates = get_validators().map(|(who, _)| {
		let stash_balance = stash_of(&who);
		Candidate {
			who,
			exposure: Exposure { total: stash_balance, own: stash_balance, others: vec![] },
			..Default::default()
		}
	}).collect::<Vec<Candidate<T::AccountId, BalanceOf<T>>>>();

	// 1.1- Add phantom votes.
	let mut nominators: Vec<Nominator<T::AccountId>> = Vec::with_capacity(candidates.len());
	candidates.iter_mut().enumerate().for_each(|(idx, c)| {
		c.approval_stake += expand(c.exposure.total);
		nominators.push(Nominator {
			who: c.who.clone(),
			edges: vec![ Edge { who: c.who.clone(), candidate_index: idx, ..Default::default() }],
			budget: expand(c.exposure.total),
			load: Fraction::zero(),
		})
	});

	// 2- Collect the nominators with the associated votes.
	// Also collect approval stake along the way.
	nominators.extend(get_nominators().map(|(who, nominees)| {
		let nominator_stake = stash_of(&who);
		let mut edges: Vec<Edge<T::AccountId>> = Vec::with_capacity(nominees.len());
		for n in &nominees {
			if let Some(idx) = candidates.iter_mut().position(|i| i.who == *n) {
				candidates[idx].approval_stake = candidates[idx].approval_stake
					.saturating_add(expand(nominator_stake));
				edges.push(Edge { who: n.clone(), candidate_index: idx, ..Default::default() });
			}
		}

		Nominator {
			who,
			edges: edges,
			budget: expand(nominator_stake),
			load: Fraction::zero(),
		}
	}));


	// 3- optimization:
	// Candidates who have 0 stake => have no votes or all null-votes. Kick them out not.
	let mut candidates = candidates.into_iter().filter(|c| c.approval_stake > 0)
		.collect::<Vec<Candidate<T::AccountId, BalanceOf<T>>>>();

	// 4- If we have more candidates then needed, run Phragmén.
	if candidates.len() >= rounds {
		elected_candidates = Vec::with_capacity(rounds);
		// Main election loop
		for _round in 0..rounds {
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
					if !c.elected {
						let temp = n.budget.saturating_mul(*n.load) / c.approval_stake;
						c.score = Fraction::from_max_value((*c.score).saturating_add(temp));
					}
				}
			}

			// Find the best
			let winner = candidates
				.iter_mut()
				.filter(|c| !c.elected)
				.min_by_key(|c| *c.score)
				.expect("candidates length is checked to be >0; qed");

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

			elected_candidates.push(winner.clone());
		} // end of all rounds

		// 4.1- Update backing stake of candidates and nominators
		for n in &mut nominators {
			for e in &mut n.edges {
				// if the target of this vote is among the winners, otherwise let go.
				if let Some(c) = elected_candidates.iter_mut().find(|c| c.who == e.who) {
					e.elected = true;
					// NOTE: for now, always divide last to avoid collapse to zero.
					e.backing_stake = n.budget.saturating_mul(*e.load) / *n.load;
					c.backing_stake = c.backing_stake.saturating_add(e.backing_stake);
					if c.who != n.who {
						// Only update the exposure if this vote is from some other account.
						c.exposure.total = c.exposure.total.saturating_add(shrink(e.backing_stake));
						c.exposure.others.push(
							IndividualExposure { who: n.who.clone(), value: shrink(e.backing_stake) }
						);
					}
				}
			}
		}

		// Optionally perform equalize post-processing.
		if config.equalize {
			let tolerance = config.tolerance;
			let equalize_iterations = config.iterations;

			// Fix indexes
			nominators.iter_mut().for_each(|n| {
				n.edges.iter_mut().for_each(|e| {
					if let Some(idx) = elected_candidates.iter().position(|c| c.who == e.who) {
						e.elected_idx = idx;
					}
				});
			});

			for _i in 0..equalize_iterations {
				let mut max_diff = <BalanceOf<T>>::zero();
				nominators.iter_mut().for_each(|mut n| {
					let diff = equalize::<T>(&mut n, &mut elected_candidates, tolerance);
					if diff > max_diff {
						max_diff = diff;
					}
				});
				if max_diff < tolerance {
					break;
				}
			}
		}
	} else {
		if candidates.len() > minimum_validator_count {
			// if we don't have enough candidates, just choose all that have some vote.
			elected_candidates = candidates;
			for n in &mut nominators {
				let nominator = n.who.clone();
				for e in &mut n.edges {
					if let Some(c) = elected_candidates.iter_mut().find(|c| c.who == e.who && c.who != nominator) {
						c.exposure.total = c.exposure.total.saturating_add(shrink(n.budget));
						c.exposure.others.push(
							IndividualExposure { who: n.who.clone(), value: shrink(n.budget) }
						);
					}
				}
			}
		} else {
			// if we have less than minimum, use the previous validator set.
			return None
		}
	}
	Some(elected_candidates)
}

/// Performs equalize post-processing to the output of the election algorithm
/// This function mutates the input parameters, most noticeably it updates the exposure of
/// the elected candidates.
/// The return value is to tolerance at which the function has stopped.
pub fn equalize<T: Trait + 'static>(
	nominator: &mut Nominator<T::AccountId>,
	elected_candidates: &mut Vec<Candidate<T::AccountId, BalanceOf<T>>>,
	_tolerance: BalanceOf<T>
) -> BalanceOf<T> {
	let expand = |b: BalanceOf<T>|    <T::CurrencyToVote as Convert<BalanceOf<T>, u64>>::convert(b) as ExtendedBalance;
	let shrink = |b: ExtendedBalance| <T::CurrencyToVote as Convert<ExtendedBalance, BalanceOf<T>>>::convert(b);
	let tolerance = expand(_tolerance);

	let mut elected_edges = nominator.edges
		.iter_mut()
		.filter(|e| e.elected)
		.collect::<Vec<&mut Edge<T::AccountId>>>();

	if elected_edges.len() == 0 {
		return <BalanceOf<T>>::zero();
	}

	let stake_used = elected_edges
		.iter()
		.fold(0, |s, e| s.saturating_add(e.backing_stake));
	let backed_stakes = elected_edges
		.iter()
		.map(|e| elected_candidates[e.elected_idx].backing_stake)
		.collect::<Vec<ExtendedBalance>>();
	let backing_backed_stake = elected_edges
		.iter()
		.filter(|e| e.backing_stake > 0)
		.map(|e| elected_candidates[e.elected_idx].backing_stake)
		.collect::<Vec<ExtendedBalance>>();

	let mut difference;
	if backing_backed_stake.len() > 0 {
		let max_stake = *backing_backed_stake
			.iter()
			.max()
			.expect("vector with positive length will have a max; qed");
		let min_stake = *backed_stakes
			.iter()
			.min()
			.expect("vector with positive length will have a min; qed");
		difference = max_stake.saturating_sub(min_stake);
		difference = difference.saturating_add(nominator.budget.saturating_sub(stake_used));
		if difference < tolerance {
			return shrink(difference);
		}
	} else {
		difference = nominator.budget;
	}

	// Undo updates to exposure
	elected_edges.iter_mut().for_each(|e| {
		// NOTE: no assertions in the runtime, but this should nonetheless be indicative.
		//assert_eq!(elected_candidates[e.elected_idx].who, e.who);
		elected_candidates[e.elected_idx].backing_stake -= e.backing_stake;
		elected_candidates[e.elected_idx].exposure.total -= shrink(e.backing_stake);
		e.backing_stake = 0;
	});

	elected_edges.sort_unstable_by_key(|e| elected_candidates[e.elected_idx].backing_stake);

	let mut cumulative_stake: ExtendedBalance = 0;
	let mut last_index = elected_edges.len() - 1;
	let budget = nominator.budget;
	elected_edges.iter_mut().enumerate().for_each(|(idx, e)| {
		let stake = elected_candidates[e.elected_idx].backing_stake;

		let stake_mul = stake.saturating_mul(idx as ExtendedBalance);
		let stake_sub = stake_mul.saturating_sub(cumulative_stake);
		if stake_sub > budget {
			last_index = idx.checked_sub(1).unwrap_or(0);
			return
		}
		cumulative_stake = cumulative_stake.saturating_add(stake);
	});

	let last_stake = elected_candidates[elected_edges[last_index].elected_idx].backing_stake;
	let split_ways = last_index + 1;
	let excess = nominator.budget
		.saturating_add(cumulative_stake)
		.saturating_sub(last_stake.saturating_mul(split_ways as ExtendedBalance));
	let nominator_address = nominator.who.clone();
	elected_edges.iter_mut().take(split_ways).for_each(|e| {
		let c = &mut elected_candidates[e.elected_idx];
		e.backing_stake = (excess / split_ways as ExtendedBalance)
			.saturating_add(last_stake)
			.saturating_sub(c.backing_stake);
		c.exposure.total = c.exposure.total.saturating_add(shrink(e.backing_stake));
		c.backing_stake = c.backing_stake.saturating_add(e.backing_stake);
		if let Some(i_expo) = c.exposure.others.iter_mut().find(|i| i.who == nominator_address) {
			i_expo.value = shrink(e.backing_stake);
		}
	});
	shrink(difference)
}
