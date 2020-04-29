// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Helper methods for phragmen.

use crate::{Assignment, ExtendedBalance, VoteWeight, IdentifierT, StakedAssignment, WithApprovalOf};
use sp_arithmetic::PerThing;
use sp_std::prelude::*;

/// Converts a vector of ratio assignments into ones with absolute budget value.
pub fn assignment_ratio_to_staked<A: IdentifierT, T: PerThing, FS>(
	ratio: Vec<Assignment<A, T>>,
	stake_of: FS,
) -> Vec<StakedAssignment<A>>
where
	for<'r> FS: Fn(&'r A) -> VoteWeight,
	T: sp_std::ops::Mul<ExtendedBalance, Output = ExtendedBalance>,
	ExtendedBalance: From<<T as PerThing>::Inner>,
{
	ratio
		.into_iter()
		.map(|a| {
			let stake = stake_of(&a.who);
			a.into_staked(stake.into(), true)
		})
		.collect()
}

/// Converts a vector of staked assignments into ones with ratio values.
pub fn assignment_staked_to_ratio<A: IdentifierT, T: PerThing>(
	staked: Vec<StakedAssignment<A>>,
) -> Vec<Assignment<A, T>>
where
	ExtendedBalance: From<<T as PerThing>::Inner>,
{
	staked.into_iter().map(|a| a.into_assignment(true)).collect()
}

/// consumes a vector of winners with backing stake to just winners.
pub fn to_without_backing<A: IdentifierT>(winners: Vec<WithApprovalOf<A>>) -> Vec<A> {
	winners.into_iter().map(|(who, _)| who).collect::<Vec<A>>()
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_arithmetic::Perbill;

	#[test]
	fn into_staked_works() {
		let assignments = vec![
			Assignment {
				who: 1u32,
				distribution: vec![
					(10u32, Perbill::from_fraction(0.5)),
					(20, Perbill::from_fraction(0.5)),
				],
			},
			Assignment {
				who: 2u32,
				distribution: vec![
					(10, Perbill::from_fraction(0.33)),
					(20, Perbill::from_fraction(0.67)),
				],
			},
		];

		let stake_of = |_: &u32| -> VoteWeight { 100 };
		let staked = assignment_ratio_to_staked(assignments, stake_of);

		assert_eq!(
			staked,
			vec![
				StakedAssignment {
					who: 1u32,
					distribution: vec![(10u32, 50), (20, 50),]
				},
				StakedAssignment {
					who: 2u32,
					distribution: vec![(10u32, 33), (20, 67),]
				}
			]
		);
	}
}
