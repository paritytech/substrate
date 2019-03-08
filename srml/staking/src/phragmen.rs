use primitives::Perquintill;
use primitives::traits::{Zero, As};
use parity_codec::{HasCompact, Encode, Decode};
use crate::{Exposure, BalanceOf, Trait, ValidatorPrefs, IndividualExposure};

// TODO: proper capitalization and comment line lengths

// a wrapper around validation candidates list and some metadata needed for election process.
#[derive(Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Candidate<AccountId, Balance: HasCompact> {
	// The validator's account
	pub who: AccountId,
	// Exposure struct, holding info about the value that the validator has in stake.
	pub exposure: Exposure<AccountId, Balance>,
	// Accumulator of the stake of this candidate based on received votes.
	approval_stake: Balance,
	// Intermediary value used to sort candidates. See phragmen reference implementation
	score: Perquintill,
}

// Wrapper around the nomination info of a single nominator for a group of validators.
#[derive(Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Nominations<AccountId, Balance: HasCompact> {
	// The nominator's account
	who: AccountId,
	// List of validators proposed by this nominator.
	nominees: Vec<Vote<AccountId, Balance>>,
	// the stake amount proposed by the nominator as a part of the vote.
    // Same as `nom.budget` in phragmen reference.
	stake: Balance,
	// Incremented each time a nominee that this nominator voted for has been elected.
	load: Perquintill,
}

// Wrapper around a nominator vote and the load of that vote. 
// Referred to as 'edge' in the phragmen reference implementation.
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

/// Perform election based on Phragmen algorithm.
pub fn elect<T: Trait, FR, FN, FV, FS>(
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
        T::AccountId: 'static,
        ValidatorPrefs<BalanceOf<T>>: 'static {   
    let rounds = get_rounds();
    let mut elected_candidates = vec![];
    
    // 1- Pre-process candidates and place them in a container
    let mut candidates = get_validators().map(|(who, _)| {
        let stash_balance = stash_of(who);
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
        let nominator_stake = stash_of(who);
        for n in &nominees {
            if let Some(index) = candidates.iter().position(|i| i.who == *n) {
                candidates[index].approval_stake += nominator_stake;
            }
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

    // 4- If we have more candidates then needed, run phragmen.
    if candidates.len() > rounds {
        // Main election loop
        for _round in 0..rounds {
            // Loop 1: initialize score
            for nominaotion in &nominations {
                for vote in &nominaotion.nominees {
                    let candidate = &vote.who;
                    if let Some(index) = candidates.iter().position(|i| i.who == *candidate) {
                        let approval_stake = candidates[index].approval_stake;
                        candidates[index].score = Perquintill::from_xth(approval_stake.as_());
                    }
                }
            }
            // Loop 2: increment score.
            for nominaotion in &nominations {
                for vote in &nominaotion.nominees {
                    let candidate = &vote.who;
                    if let Some(index) = candidates.iter().position(|i| i.who == *candidate) {
                        let approval_stake = candidates[index].approval_stake;
                        let temp =
                            nominaotion.stake.as_()
                            * nominaotion.load.extract()
                            / approval_stake.as_();
                        candidates[index].score = Perquintill::from_quintillionths(candidates[index].score.extract() + temp);
                    }
                }
            }

            // Find the best
            let (winner_index, _) = candidates.iter().enumerate().min_by_key(|&(_i, c)| c.score.extract())
                .expect("candidates length is checked to be >0; qed");

            // loop 3: update nominator and vote load
            let winner = candidates.remove(winner_index);
            for nominator_idx in 0..nominations.len() {
                for vote_idx in 0..nominations[nominator_idx].nominees.len() {
                    if nominations[nominator_idx].nominees[vote_idx].who == winner.who {
                        nominations[nominator_idx].nominees[vote_idx].load =
                            Perquintill::from_quintillionths(
                                winner.score.extract()
                                - nominations[nominator_idx].load.extract()
                            );
                        nominations[nominator_idx].load = winner.score;
                    }
                }
            }

            elected_candidates.push(winner);

        } // end of all rounds

        // 4.1- Update backing stake of candidates and nominators
        for nomination in &mut nominations {
            for vote in &mut nomination.nominees {
                // if the target of this vote is among the winners, otherwise let go.
                if let Some(index) = elected_candidates.iter().position(|c| c.who == vote.who) {
                    vote.backing_stake = <BalanceOf<T> as As<u64>>::sa(
                        nomination.stake.as_()
                        * vote.load.extract()
                        / nomination.load.extract()
                    );
                    elected_candidates[index].exposure.total += vote.backing_stake;
                    // Update IndividualExposure of those who nominated and their vote won
                    elected_candidates[index].exposure.others.push(
                        IndividualExposure {who: nomination.who.clone(), value: vote.backing_stake }
                    );
                }
            }
        }
    } // if candidates.len() > rounds 
    else {
        if candidates.len() > minimum_validator_count {
            // if we don't have enough candidates, just choose all that have some vote.
            elected_candidates = candidates;
        }
        else {
            // if we have less than minimum, use the previous validator set.
            elected_candidates = original_candidates;
        }
    }

    candidates
}