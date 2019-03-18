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

use rstd::{prelude::*};
use primitives::Perquintill;
use primitives::traits::{Zero, As};
use parity_codec::{HasCompact, Encode, Decode};
use crate::{Exposure, BalanceOf, Trait, ValidatorPrefs, IndividualExposure};

// Wrapper around validation candidates some metadata.
#[derive(Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Default))]
pub struct Candidate<AccountId, Balance: HasCompact> {
	// The validator's account
	pub who: AccountId,
	// Exposure struct, holding info about the value that the validator has in stake.
	pub exposure: Exposure<AccountId, Balance>,
	// Intermediary value used to sort candidates.
	pub score: Perquintill,
	// Accumulator of the stake of this candidate based on received votes.
	approval_stake: Balance,
	// Flag for being elected.
	elected: bool,
	
}

// Wrapper around the nomination info of a single nominator for a group of validators.
#[derive(Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Nominations<AccountId, Balance: HasCompact> {
	// The nominator's account.
	who: AccountId,
	// List of validators proposed by this nominator.
	edges: Vec<Edge<AccountId, Balance>>,
	// the stake amount proposed by the nominator as a part of the vote.
	budget: Balance,
	// Incremented each time a nominee that this nominator voted for has been elected.
	load: Perquintill,
}

// Wrapper around a nominator vote and the load of that vote. 
#[derive(Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Default))]
pub struct Edge<AccountId, Balance: HasCompact> {
	// Account being voted for
	who: AccountId,
	// Load of this vote.
	load: Perquintill,
	// Final backing stake of this vote.
	backing_stake: Balance,
	// Index of the candidate stored in the 'candidates' vecotr
	candidate_idx: usize,
}

/// Perform election based on Phragmén algorithm.
///
/// Reference implementation: https://github.com/w3f/consensus
///
/// Returns a vector of elected candidates
pub fn elect<T: Trait + 'static, FR, FN, FV, FS>(
		get_rounds: FR,
		get_validators: FV,
		get_nominators: FN,
		stash_of: FS,
		minimum_validator_count: usize,
) -> Vec<Candidate<T::AccountId, BalanceOf<T>>> where
	FR: Fn() -> usize,
	FV: Fn() -> Box<dyn Iterator<
		Item =(T::AccountId, ValidatorPrefs<BalanceOf<T>>)
	>>,
	FN: Fn() -> Box<dyn Iterator<
		Item =(T::AccountId, Vec<T::AccountId>)
	>>,
	for <'r> FS: Fn(&'r T::AccountId) -> BalanceOf<T>,
{
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

	// Just to be used when we are below minimum validator count
	let original_candidates = candidates.clone();
	
	// 1.1- Add phantom votes.
	let mut nominations: Vec<Nominations<T::AccountId, BalanceOf<T>>> = Vec::with_capacity(candidates.len());
	candidates.iter_mut().enumerate().for_each(|(idx, c)| {
		c.approval_stake += c.exposure.total;
		nominations.push(Nominations {
			who: c.who.clone(),
			edges: vec![ Edge { who: c.who.clone(), candidate_idx: idx, ..Default::default() }],
			budget: c.exposure.total,
			load: Perquintill::zero(),
		})
	});

	// 2- Collect the nominators with the associated votes.
	// Also collect approval stake along the way.
	nominations.extend(get_nominators().map(|(who, nominees)| {
		let nominator_stake = stash_of(&who);
		let mut edges: Vec<Edge<T::AccountId, BalanceOf<T>>> = Vec::with_capacity(nominees.len());
		for n in &nominees {
			if let Some(idx) = candidates.iter_mut().position(|i| i.who == *n) {
				candidates[idx].approval_stake += nominator_stake;
				edges.push(Edge { who: n.clone(), candidate_idx: idx, ..Default::default() });
			}
		}
		
		Nominations {
			who,
			edges: edges, 
			budget: nominator_stake,
			load: Perquintill::zero(),
		}
	}));

	println!("Candidates : {:?}", candidates);
	println!("Nominations: {:?}", nominations);

	// 3- optimization:
	// Candidates who have 0 stake => have no votes or all null-votes. Kick them out not.
	let mut candidates = candidates.into_iter().filter(|c| c.approval_stake > BalanceOf::<T>::zero())
		.collect::<Vec<Candidate<T::AccountId, BalanceOf<T>>>>();

	// 4- If we have more candidates then needed, run Phragmén.
	if candidates.len() > rounds {
		elected_candidates = Vec::with_capacity(rounds);
		// Main election loop
		for _round in 0..rounds {
			// Loop 1: initialize score
			for nomination in &nominations {
				for edge in &nomination.edges {
					let c = &mut candidates[edge.candidate_idx];
					if !c.elected {
						c.score = Perquintill::from_xth(c.approval_stake.as_());
					}
				}
			}
			// Loop 2: increment score.
			for nomination in &nominations {
				for edge in &nomination.edges {
					let c = &mut candidates[edge.candidate_idx];
					let temp = nomination.budget.as_() * *nomination.load / c.approval_stake.as_();
					if !c.elected {
						c.score = Perquintill::from_quintillionths(*c.score + temp);
					}
				}
			}

			// Find the best
			let winner = candidates
				.iter_mut()	
				.filter(|c| !c.elected)
				.min_by_key(|c| *c.score)
				.expect("candidates length is checked to be >0; qed");

			// loop 3: update nominator and vote load
			winner.elected = true;
			for n in &mut nominations {
				for v in &mut n.edges {
					if v.who == winner.who {
						v.load = Perquintill::from_quintillionths(*winner.score - *n.load);
						n.load = winner.score;
					}
				}
			}

			elected_candidates.push(winner.clone());
		} // end of all rounds

		// 4.1- Update backing stake of candidates and nominators
		for n in &mut nominations {
			let nominator = n.who.clone();
			for e in &mut n.edges {
				// if the target of this vote is among the winners, otherwise let go.
				if let Some(c) = elected_candidates.iter_mut().find(|c| c.who == e.who && c.who != nominator) {
					e.backing_stake = <BalanceOf<T> as As<u64>>::sa(n.budget.as_() * *e.load / *n.load);
					c.exposure.total += e.backing_stake;
					// Update IndividualExposure of those who nominated and their vote won
					c.exposure.others.push(
						IndividualExposure { who: n.who.clone(), value: e.backing_stake }
					);
				}
			}
		}
	} else {
		if candidates.len() > minimum_validator_count {
			// if we don't have enough candidates, just choose all that have some vote.
			elected_candidates = candidates;
			// `Exposure.others` still needs an update
			for n in &mut nominations {
				let nominator = n.who.clone();
				for e in &mut n.edges {
					if let Some(c) = elected_candidates.iter_mut().find(|c| c.who == e.who && c.who != nominator) {
						c.exposure.total += n.budget;
						c.exposure.others.push(
							IndividualExposure { who: n.who.clone(), value: n.budget }
						);
					}
				}
			}
		} else {
			// if we have less than minimum, use the previous validator set.
			elected_candidates = original_candidates;
		}
	}
	
	println!("Elected : {:?}", elected_candidates);
	elected_candidates
}