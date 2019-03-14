// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Candidate<AccountId, Balance: HasCompact> {
	// The validator's account
	pub who: AccountId,
	// Exposure struct, holding info about the value that the validator has in stake.
	pub exposure: Exposure<AccountId, Balance>,
	// Accumulator of the stake of this candidate based on received votes.
	approval_stake: Balance,
	// Intermediary value used to sort candidates.
	// See Phragmén reference implementation.
	pub score: Perquintill,
}

// Wrapper around the nomination info of a single nominator for a group of validators.
#[derive(Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Nominations<AccountId, Balance: HasCompact> {
	// The nominator's account.
	who: AccountId,
	// List of validators proposed by this nominator.
	nominees: Vec<Vote<AccountId, Balance>>,
	// the stake amount proposed by the nominator as a part of the vote.
	// Same as `nom.budget` in Phragmén reference.
	stake: Balance,
	// Incremented each time a nominee that this nominator voted for has been elected.
	load: Perquintill,
}

// Wrapper around a nominator vote and the load of that vote.
// Referred to as 'edge' in the Phragmén reference implementation.
#[derive(Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Vote<AccountId, Balance: HasCompact> {
	// Account being voted for
	who: AccountId,
	// Load of this vote.
	load: Perquintill,
	// Final backing stake of this vote.
	backing_stake: Balance
}

/// Perform election based on Phragmén algorithm.
///
/// Reference implementation: https://github.com/w3f/consensus
///
/// @returns a vector of elected candidates
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
		FS: Fn(T::AccountId) -> BalanceOf<T>,
{
	let rounds = get_rounds();
	let mut elected_candidates = vec![];
	
	// 1- Pre-process candidates and place them in a container
	let mut candidates = get_validators().map(|(who, _)| {
		let stash_balance = stash_of(who.clone());
		Candidate {
			who,
			approval_stake: BalanceOf::<T>::zero(),
			score: Perquintill::zero(),
			exposure: Exposure { total: stash_balance, own: stash_balance, others: vec![] },
		}
	}).collect::<Vec<Candidate<T::AccountId, BalanceOf<T>>>>();

	// Just to be used when we are below minimum validator count
	let original_candidates = candidates.clone();
	
	// 2- Collect the nominators with the associated votes.
	// Also collect approval stake along the way.
	let mut nominations = get_nominators().map(|(who, nominees)| {
		let nominator_stake = stash_of(who.clone());
		for n in &nominees {
			candidates.iter_mut().filter(|i| i.who == *n).for_each(|c| {
				c.approval_stake += nominator_stake;
			});
		}

		Nominations {
			who,
			nominees: nominees.into_iter()
				.map(|n| Vote {who: n, load: Perquintill::zero(), backing_stake: BalanceOf::<T>::zero()})
				.collect::<Vec<Vote<T::AccountId, BalanceOf<T>>>>(),
			stake: nominator_stake,
			load : Perquintill::zero(),
		}
	}).collect::<Vec<Nominations<T::AccountId, BalanceOf<T>>>>();
	
	// 3- optimization:
	// Candidates who have 0 stake => have no votes or all null-votes. Kick them out not.
	let mut candidates = candidates.into_iter().filter(|c| c.approval_stake > BalanceOf::<T>::zero())
		.collect::<Vec<Candidate<T::AccountId, BalanceOf<T>>>>();

	// 4- If we have more candidates then needed, run Phragmén.
	if candidates.len() > rounds {
		// Main election loop
		for _round in 0..rounds {
			// Loop 1: initialize score
			for nominaotion in &nominations {
				for vote in &nominaotion.nominees {
					let candidate = &vote.who;
					if let Some(c) = candidates.iter_mut().find(|i| i.who == *candidate) {
						let approval_stake = c.approval_stake;
						c.score = Perquintill::from_xth(approval_stake.as_());
					}
				}
			}
			// Loop 2: increment score.
			for nominaotion in &nominations {
				for vote in &nominaotion.nominees {
					let candidate = &vote.who;
					if let Some(c) = candidates.iter_mut().find(|i| i.who == *candidate) {
						let approval_stake = c.approval_stake;
						let temp =
							nominaotion.stake.as_()
							* *nominaotion.load
							/ approval_stake.as_();
						c.score = Perquintill::from_quintillionths(*c.score + temp);
					}
				}
			}

			// Find the best
			let (winner_index, _) = candidates.iter().enumerate().min_by_key(|&(_i, c)| *c.score)
				.expect("candidates length is checked to be >0; qed");

			// loop 3: update nominator and vote load
			let winner = candidates.remove(winner_index);
			for n in &mut nominations {
				for v in &mut n.nominees {
					if v.who == winner.who {
						v.load =
							Perquintill::from_quintillionths(
								*winner.score
								- *n.load
							);
						n.load = winner.score;
					}
				}
			}

			elected_candidates.push(winner);

		} // end of all rounds

		// 4.1- Update backing stake of candidates and nominators
		for n in &mut nominations {
			for v in &mut n.nominees {
				// if the target of this vote is among the winners, otherwise let go.
				if let Some(c) = elected_candidates.iter_mut().find(|c| c.who == v.who) {
					v.backing_stake = <BalanceOf<T> as As<u64>>::sa(
						n.stake.as_()
						* *v.load
						/ *n.load
					);
					c.exposure.total += v.backing_stake;
					// Update IndividualExposure of those who nominated and their vote won
					c.exposure.others.push(
						IndividualExposure {who: n.who.clone(), value: v.backing_stake }
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
				for v in &mut n.nominees {
					if let Some(c) = elected_candidates.iter_mut().find(|c| c.who == v.who) {
						c.exposure.total += n.stake;
						c.exposure.others.push(
							IndividualExposure {who: n.who.clone(), value: n.stake }
						);
					}
				}
			}
		} else {
			// if we have less than minimum, use the previous validator set.
			elected_candidates = original_candidates;
		}
	}

	elected_candidates
}