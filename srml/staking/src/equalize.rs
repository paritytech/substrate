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

//! Phragmen post-processing fot staking module.

// TODO: deprecate this file, decouple from staking primitives and move to sr_primitives.
#![cfg(feature = "equalize")]

use crate::{ExpoMap, Trait, BalanceOf, IndividualExposure};

use sr_primitives::traits::{Zero, Convert, Saturating};
use sr_primitives::phragmen::{ExtendedBalance};

/// Performs equalize post-processing to the output of the election algorithm
/// This function mutates the input parameters, most noticeably it updates the exposure of
/// the elected candidates.
///
/// No value is returned from the function and the `expo_map` parameter is updated.
pub fn equalize<T: Trait + 'static>(
	assignments: &mut Vec<(T::AccountId, BalanceOf<T>, Vec<(T::AccountId, ExtendedBalance, ExtendedBalance)>)>,
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
	elected_edges: &mut Vec<(T::AccountId, ExtendedBalance, ExtendedBalance)>,
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
			expo.others.retain(|i_expo| i_expo.who != *nominator);
		}
		e.2 = 0;
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
			expo.others.push(IndividualExposure { who: nominator.clone(), value: to_balance(e.2)});
		}
	});

	difference
}
