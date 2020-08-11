// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Tests for npos-elections.

use crate::mock::*;
use crate::{
	seq_phragmen, balance_solution, build_support_map, is_score_better, helpers::*,
	Support, StakedAssignment, Assignment, ElectionResult, ExtendedBalance,
};
use substrate_test_utils::assert_eq_uvec;
use sp_arithmetic::{Perbill, Permill, Percent, PerU16};

#[test]
fn float_phragmen_poc_works() {
	let candidates = vec![1, 2, 3];
	let voters = vec![
		(10, vec![1, 2]),
		(20, vec![1, 3]),
		(30, vec![2, 3]),
	];
	let stake_of = create_stake_of(&[(10, 10), (20, 20), (30, 30), (1, 0), (2, 0), (3, 0)]);
	let mut phragmen_result = elect_float(2, 2, candidates, voters, &stake_of).unwrap();
	let winners = phragmen_result.clone().winners;
	let assignments = phragmen_result.clone().assignments;

	assert_eq_uvec!(winners, vec![(2, 40), (3, 50)]);
	assert_eq_uvec!(
		assignments,
		vec![
			(10, vec![(2, 1.0)]),
			(20, vec![(3, 1.0)]),
			(30, vec![(2, 0.5), (3, 0.5)]),
		]
	);

	let mut support_map = build_support_map_float(&mut phragmen_result, &stake_of);

	assert_eq!(
		support_map.get(&2).unwrap(),
		&_Support { own: 0.0, total: 25.0, others: vec![(10u64, 10.0), (30u64, 15.0)]}
	);
	assert_eq!(
		support_map.get(&3).unwrap(),
		&_Support { own: 0.0, total: 35.0, others: vec![(20u64, 20.0), (30u64, 15.0)]}
	);

	equalize_float(phragmen_result.assignments, &mut support_map, 0.0, 2, stake_of);

	assert_eq!(
		support_map.get(&2).unwrap(),
		&_Support { own: 0.0, total: 30.0, others: vec![(10u64, 10.0), (30u64, 20.0)]}
	);
	assert_eq!(
		support_map.get(&3).unwrap(),
		&_Support { own: 0.0, total: 30.0, others: vec![(20u64, 20.0), (30u64, 10.0)]}
	);
}

#[test]
fn phragmen_poc_works() {
	let candidates = vec![1, 2, 3];
	let voters = vec![
		(10, vec![1, 2]),
		(20, vec![1, 3]),
		(30, vec![2, 3]),
	];

	let stake_of = create_stake_of(&[(10, 10), (20, 20), (30, 30)]);
	let ElectionResult { winners, assignments } = seq_phragmen::<_, Perbill>(
		2,
		2,
		candidates,
		voters.iter().map(|(ref v, ref vs)| (v.clone(), stake_of(v), vs.clone())).collect::<Vec<_>>(),
	).unwrap();

	assert_eq_uvec!(winners, vec![(2, 40), (3, 50)]);
	assert_eq_uvec!(
		assignments,
		vec![
			Assignment {
				who: 10u64,
				distribution: vec![(2, Perbill::from_percent(100))],
			},
			Assignment {
				who: 20,
				distribution: vec![(3, Perbill::from_percent(100))],
			},
			Assignment {
				who: 30,
				distribution: vec![
					(2, Perbill::from_percent(100/2)),
					(3, Perbill::from_percent(100/2)),
				],
			},
		]
	);

	let mut staked = assignment_ratio_to_staked(assignments, &stake_of);
	let winners = to_without_backing(winners);
	let mut support_map = build_support_map::<AccountId>(&winners, &staked).0;

	assert_eq_uvec!(
		staked,
		vec![
			StakedAssignment {
				who: 10u64,
				distribution: vec![(2, 10)],
			},
			StakedAssignment {
				who: 20,
				distribution: vec![(3, 20)],
			},
			StakedAssignment {
				who: 30,
				distribution: vec![
					(2, 15),
					(3, 15),
				],
			},
		]
	);

	assert_eq!(
		*support_map.get(&2).unwrap(),
		Support::<AccountId> { total: 25, voters: vec![(10, 10), (30, 15)] },
	);
	assert_eq!(
		*support_map.get(&3).unwrap(),
		Support::<AccountId> { total: 35, voters: vec![(20, 20), (30, 15)] },
	);

	balance_solution(
		&mut staked,
		&mut support_map,
		0,
		2,
	);

	assert_eq_uvec!(
		staked,
		vec![
			StakedAssignment {
				who: 10u64,
				distribution: vec![(2, 10)],
			},
			StakedAssignment {
				who: 20,
				distribution: vec![(3, 20)],
			},
			StakedAssignment {
				who: 30,
				distribution: vec![
					(2, 20),
					(3, 10),
				],
			},
		]
	);

	assert_eq!(
		*support_map.get(&2).unwrap(),
		Support::<AccountId> { total: 30, voters: vec![(10, 10), (30, 20)] },
	);
	assert_eq!(
		*support_map.get(&3).unwrap(),
		Support::<AccountId> { total: 30, voters: vec![(20, 20), (30, 10)] },
	);
}

#[test]
fn phragmen_poc_2_works() {
	let candidates = vec![10, 20, 30];
	let voters = vec![
		(2, vec![10, 20, 30]),
		(4, vec![10, 20, 40]),
	];
	let stake_of = create_stake_of(&[
		(10, 1000),
		(20, 1000),
		(30, 1000),
		(40, 1000),
		(2, 500),
		(4, 500),
	]);

	run_and_compare::<Perbill>(candidates.clone(), voters.clone(), &stake_of, 2, 2);
	run_and_compare::<Permill>(candidates.clone(), voters.clone(), &stake_of, 2, 2);
	run_and_compare::<Percent>(candidates.clone(), voters.clone(), &stake_of, 2, 2);
	run_and_compare::<PerU16>(candidates, voters, &stake_of, 2, 2);
}

#[test]
fn phragmen_poc_3_works() {
	let candidates = vec![10, 20, 30];
	let voters = vec![
		(2, vec![10, 20, 30]),
		(4, vec![10, 20, 40]),
	];
	let stake_of = create_stake_of(&[
		(10, 1000),
		(20, 1000),
		(30, 1000),
		(2, 50),
		(4, 1000),
	]);

	run_and_compare::<Perbill>(candidates.clone(), voters.clone(), &stake_of, 2, 2);
	run_and_compare::<Permill>(candidates.clone(), voters.clone(), &stake_of, 2, 2);
	run_and_compare::<Percent>(candidates.clone(), voters.clone(), &stake_of, 2, 2);
	run_and_compare::<PerU16>(candidates, voters, &stake_of, 2, 2);
}

#[test]
fn phragmen_accuracy_on_large_scale_only_validators() {
	// because of this particular situation we had per_u128 and now rational128. In practice, a
	// candidate can have the maximum amount of tokens, and also supported by the maximum.
	let candidates = vec![1, 2, 3, 4, 5];
	let stake_of = create_stake_of(&[
		(1, (u64::max_value() - 1).into()),
		(2, (u64::max_value() - 4).into()),
		(3, (u64::max_value() - 5).into()),
		(4, (u64::max_value() - 3).into()),
		(5, (u64::max_value() - 2).into()),
	]);

	let ElectionResult { winners, assignments } = seq_phragmen::<_, Perbill>(
		2,
		2,
		candidates.clone(),
		auto_generate_self_voters(&candidates)
			.iter()
			.map(|(ref v, ref vs)| (v.clone(), stake_of(v), vs.clone()))
			.collect::<Vec<_>>(),
	).unwrap();

	assert_eq_uvec!(winners, vec![(1, 18446744073709551614u128), (5, 18446744073709551613u128)]);
	assert_eq!(assignments.len(), 2);
	check_assignments_sum(assignments);
}

#[test]
fn phragmen_accuracy_on_large_scale_validators_and_nominators() {
	let candidates = vec![1, 2, 3, 4, 5];
	let mut voters = vec![
		(13, vec![1, 3, 5]),
		(14, vec![2, 4]),
	];
	voters.extend(auto_generate_self_voters(&candidates));
	let stake_of = create_stake_of(&[
		(1,  (u64::max_value() - 1).into()),
		(2,  (u64::max_value() - 4).into()),
		(3,  (u64::max_value() - 5).into()),
		(4,  (u64::max_value() - 3).into()),
		(5,  (u64::max_value() - 2).into()),
		(13, (u64::max_value() - 10).into()),
		(14, u64::max_value().into()),
	]);

	let ElectionResult { winners, assignments } = seq_phragmen::<_, Perbill>(
		2,
		2,
		candidates,
		voters.iter().map(|(ref v, ref vs)| (v.clone(), stake_of(v), vs.clone())).collect::<Vec<_>>(),
	).unwrap();

	assert_eq_uvec!(winners, vec![(2, 36893488147419103226u128), (1, 36893488147419103219u128)]);
	assert_eq!(
		assignments,
		vec![
			Assignment {
				who: 13u64,
				distribution: vec![(1, Perbill::one())],
			},
			Assignment {
				who: 14,
				distribution: vec![(2, Perbill::one())],
			},
			Assignment {
				who: 1,
				distribution: vec![(1, Perbill::one())],
			},
			Assignment {
				who: 2,
				distribution: vec![(2, Perbill::one())],
			},
		]
	);
	check_assignments_sum(assignments);
}

#[test]
fn phragmen_accuracy_on_small_scale_self_vote() {
	let candidates = vec![40, 10, 20, 30];
	let voters = auto_generate_self_voters(&candidates);
	let stake_of = create_stake_of(&[
		(40, 0),
		(10, 1),
		(20, 2),
		(30, 1),
	]);

	let ElectionResult { winners, assignments: _ } = seq_phragmen::<_, Perbill>(
		3,
		3,
		candidates,
		voters.iter().map(|(ref v, ref vs)| (v.clone(), stake_of(v), vs.clone())).collect::<Vec<_>>(),
	).unwrap();

	assert_eq_uvec!(winners, vec![(20, 2), (10, 1), (30, 1)]);
}

#[test]
fn phragmen_accuracy_on_small_scale_no_self_vote() {
	let candidates = vec![40, 10, 20, 30];
	let voters = vec![
		(1, vec![10]),
		(2, vec![20]),
		(3, vec![30]),
		(4, vec![40]),
	];
	let stake_of = create_stake_of(&[
		(40, 1000), // don't care
		(10, 1000), // don't care
		(20, 1000), // don't care
		(30, 1000), // don't care
		(4, 0),
		(1, 1),
		(2, 2),
		(3, 1),
	]);

	let ElectionResult { winners, assignments: _ } = seq_phragmen::<_, Perbill>(
		3,
		3,
		candidates,
		voters.iter().map(|(ref v, ref vs)| (v.clone(), stake_of(v), vs.clone())).collect::<Vec<_>>(),
	).unwrap();

	assert_eq_uvec!(winners, vec![(20, 2), (10, 1), (30, 1)]);
}

#[test]
fn phragmen_large_scale_test() {
	let candidates = vec![2, 4, 6, 8, 10, 12, 14, 16 ,18, 20, 22, 24];
	let mut voters = vec![
		(50, vec![2, 4, 6, 8, 10, 12, 14, 16 ,18, 20, 22, 24]),
	];
	voters.extend(auto_generate_self_voters(&candidates));
	let stake_of = create_stake_of(&[
		(2,  1),
		(4,  100),
		(6,  1000000),
		(8,  100000000001000),
		(10, 100000000002000),
		(12, 100000000003000),
		(14, 400000000000000),
		(16, 400000000001000),
		(18, 18000000000000000),
		(20, 20000000000000000),
		(22, 500000000000100000),
		(24, 500000000000200000),
		(50, 990000000000000000),
	]);

	let ElectionResult { winners, assignments } = seq_phragmen::<_, Perbill>(
		2,
		2,
		candidates,
		voters.iter().map(|(ref v, ref vs)| (v.clone(), stake_of(v), vs.clone())).collect::<Vec<_>>(),
	).unwrap();

	assert_eq_uvec!(winners, vec![(24, 1490000000000200000u128), (22, 1490000000000100000u128)]);
	check_assignments_sum(assignments);
}

#[test]
fn phragmen_large_scale_test_2() {
	let nom_budget: u64 = 1_000_000_000_000_000_000;
	let c_budget: u64 = 4_000_000;

	let candidates = vec![2, 4];
	let mut voters = vec![(50, vec![2, 4])];
	voters.extend(auto_generate_self_voters(&candidates));

	let stake_of = create_stake_of(&[
		(2,  c_budget.into()),
		(4,  c_budget.into()),
		(50, nom_budget.into()),
	]);

	let ElectionResult { winners, assignments } = seq_phragmen::<_, Perbill>(
		2,
		2,
		candidates,
		voters.iter().map(|(ref v, ref vs)| (v.clone(), stake_of(v), vs.clone())).collect::<Vec<_>>(),
	).unwrap();

	assert_eq_uvec!(winners, vec![(2, 1000000000004000000u128), (4, 1000000000004000000u128)]);
	assert_eq!(
		assignments,
		vec![
			Assignment {
				who: 50u64,
				distribution: vec![
					(2, Perbill::from_parts(500000001)),
					(4, Perbill::from_parts(499999999))
				],
			},
			Assignment {
				who: 2,
				distribution: vec![(2, Perbill::one())],
			},
			Assignment {
				who: 4,
				distribution: vec![(4, Perbill::one())],
			},
		],
	);
	check_assignments_sum(assignments);
}

#[test]
fn phragmen_linear_equalize() {
	let candidates = vec![11, 21, 31, 41, 51, 61, 71];
	let voters = vec![
		(2, vec![11]),
		(4, vec![11, 21]),
		(6, vec![21, 31]),
		(8, vec![31, 41]),
		(110, vec![41, 51]),
		(120, vec![51, 61]),
		(130, vec![61, 71]),
	];
	let stake_of = create_stake_of(&[
		(11, 1000),
		(21, 1000),
		(31, 1000),
		(41, 1000),
		(51, 1000),
		(61, 1000),
		(71, 1000),

		(2, 2000),
		(4, 1000),
		(6, 1000),
		(8, 1000),
		(110, 1000),
		(120, 1000),
		(130, 1000),
	]);

	run_and_compare::<Perbill>(candidates, voters, &stake_of, 2, 2);
}

#[test]
fn elect_has_no_entry_barrier() {
	let candidates = vec![10, 20, 30];
	let voters = vec![
		(1, vec![10]),
		(2, vec![20]),
	];
	let stake_of = create_stake_of(&[
		(1, 10),
		(2, 10),
	]);

	let ElectionResult { winners, assignments: _ } = seq_phragmen::<_, Perbill>(
		3,
		3,
		candidates,
		voters.iter().map(|(ref v, ref vs)| (v.clone(), stake_of(v), vs.clone())).collect::<Vec<_>>(),
	).unwrap();

	// 30 is elected with stake 0. The caller is responsible for stripping this.
	assert_eq_uvec!(winners, vec![
		(10, 10),
		(20, 10),
		(30, 0),
	]);
}

#[test]
fn minimum_to_elect_is_respected() {
	let candidates = vec![10, 20, 30];
	let voters = vec![
		(1, vec![10]),
		(2, vec![20]),
	];
	let stake_of = create_stake_of(&[
		(1, 10),
		(2, 10),
	]);

	let maybe_result = seq_phragmen::<_, Perbill>(
		10,
		10,
		candidates,
		voters.iter().map(|(ref v, ref vs)| (v.clone(), stake_of(v), vs.clone())).collect::<Vec<_>>(),
	);

	assert!(maybe_result.is_none());
}

#[test]
fn self_votes_should_be_kept() {
	let candidates = vec![5, 10, 20, 30];
	let voters = vec![
		(5, vec![5]),
		(10, vec![10]),
		(20, vec![20]),
		(1, vec![10, 20])
	];
	let stake_of = create_stake_of(&[
		(5, 5),
		(10, 10),
		(20, 20),
		(1, 8),
	]);

	let result = seq_phragmen::<_, Perbill>(
		2,
		2,
		candidates,
		voters.iter().map(|(ref v, ref vs)| (v.clone(), stake_of(v), vs.clone())).collect::<Vec<_>>(),
	).unwrap();

	assert_eq!(result.winners, vec![(20, 28), (10, 18)]);
	assert_eq!(
		result.assignments,
		vec![
			Assignment { who: 10, distribution: vec![(10, Perbill::from_percent(100))] },
			Assignment { who: 20, distribution: vec![(20, Perbill::from_percent(100))] },
			Assignment { who: 1, distribution: vec![
					(10, Perbill::from_percent(50)),
					(20, Perbill::from_percent(50))
				]
			},
		],
	);

	let mut staked_assignments = assignment_ratio_to_staked(result.assignments, &stake_of);
	let winners = to_without_backing(result.winners);

	let (mut supports, _) = build_support_map::<AccountId>(
		&winners,
		&staked_assignments,
	);

	assert_eq!(supports.get(&5u64), None);
	assert_eq!(
		supports.get(&10u64).unwrap(),
		&Support { total: 14u128, voters: vec![(10u64, 10u128), (1u64, 4u128)] },
	);
	assert_eq!(
		supports.get(&20u64).unwrap(),
		&Support { total: 24u128, voters: vec![(20u64, 20u128), (1u64, 4u128)] },
	);

	balance_solution(
		&mut staked_assignments,
		&mut supports,
		0,
		2usize,
	);

	assert_eq!(
		supports.get(&10u64).unwrap(),
		&Support { total: 18u128, voters: vec![(10u64, 10u128), (1u64, 8u128)] },
	);
	assert_eq!(
		supports.get(&20u64).unwrap(),
		&Support { total: 20u128, voters: vec![(20u64, 20u128)] },
	);
}

#[test]
fn duplicate_target_is_ignored() {
	let candidates = vec![1, 2, 3];
	let voters = vec![
		(10, 100, vec![1, 1, 2, 3]),
		(20, 100, vec![2, 3]),
		(30, 50, vec![1, 1, 2]),
	];

	let ElectionResult { winners, assignments } = seq_phragmen::<_, Perbill>(
		2,
		2,
		candidates,
		voters,
	).unwrap();
	let winners = to_without_backing(winners);

	assert_eq!(winners, vec![(2), (3)]);
	assert_eq!(
		assignments
			.into_iter()
			.map(|x| (x.who, x.distribution.into_iter().map(|(w, _)| w).collect::<Vec<_>>()))
			.collect::<Vec<_>>(),
		vec![
			(10, vec![2, 3]),
			(20, vec![2, 3]),
			(30, vec![2]),
		],
	);
}

#[test]
fn duplicate_target_is_ignored_when_winner() {
	let candidates = vec![1, 2, 3];
	let voters = vec![
		(10, 100, vec![1, 1, 2, 3]),
		(20, 100, vec![1, 2]),
	];

	let ElectionResult { winners, assignments } = seq_phragmen::<_, Perbill>(
		2,
		2,
		candidates,
		voters,
	).unwrap();
	let winners = to_without_backing(winners);

	assert_eq!(winners, vec![1, 2]);
	assert_eq!(
		assignments
			.into_iter()
			.map(|x| (x.who, x.distribution.into_iter().map(|(w, _)| w).collect::<Vec<_>>()))
			.collect::<Vec<_>>(),
		vec![
			(10, vec![1, 2]),
			(20, vec![1, 2]),
		],
	);
}

mod assignment_convert_normalize {
	use super::*;
	#[test]
	fn assignment_convert_works() {
		let staked = StakedAssignment {
			who: 1 as AccountId,
			distribution: vec![
				(20, 100 as ExtendedBalance),
				(30, 25),
			],
		};

		let assignment = staked.clone().into_assignment();
		assert_eq!(
			assignment,
			Assignment {
				who: 1,
				distribution: vec![
					(20, Perbill::from_percent(80)),
					(30, Perbill::from_percent(20)),
				]
			}
		);

		assert_eq!(
			assignment.into_staked(125),
			staked,
		);
	}

	#[test]
	fn assignment_convert_will_not_normalize() {
		assert_eq!(
			Assignment {
				who: 1,
				distribution: vec![
					(2, Perbill::from_percent(33)),
					(3, Perbill::from_percent(66)),
				]
			}.into_staked(100),
			StakedAssignment {
				who: 1,
				distribution: vec![
					(2, 33),
					(3, 66),
					// sum is not 100!
				],
			},
		);

		assert_eq!(
			StakedAssignment {
				who: 1,
				distribution: vec![
					(2, 333_333_333_333_333),
					(3, 333_333_333_333_333),
					(4, 666_666_666_666_333),
				],
			}.into_assignment(),
			Assignment {
				who: 1,
				distribution: vec![
					(2, Perbill::from_parts(250000000)),
					(3, Perbill::from_parts(250000000)),
					(4, Perbill::from_parts(499999999)),
					// sum is not 100%!
				]
			},
		)
	}

	#[test]
	fn assignment_can_normalize() {
		let mut a = Assignment {
			who: 1,
			distribution: vec![
				(2, Perbill::from_parts(330000000)),
				(3, Perbill::from_parts(660000000)),
				// sum is not 100%!
			]
		};
		a.try_normalize().unwrap();
		assert_eq!(
			a,
			Assignment {
				who: 1,
				distribution: vec![
					(2, Perbill::from_parts(340000000)),
					(3, Perbill::from_parts(660000000)),
				]
			},
		);
	}

	#[test]
	fn staked_assignment_can_normalize() {
		let mut a = StakedAssignment {
			who: 1,
			distribution: vec![
				(2, 33),
				(3, 66),
			]
		};
		a.try_normalize(100).unwrap();
		assert_eq!(
			a,
			StakedAssignment {
				who: 1,
				distribution: vec![
					(2, 34),
					(3, 66),
				]
			},
		);
	}
}

mod score {
	use super::*;
	#[test]
	fn score_comparison_is_lexicographical_no_epsilon() {
		let epsilon = Perbill::zero();
		// only better in the fist parameter, worse in the other two ✅
		assert_eq!(
			is_score_better([12, 10, 35], [10, 20, 30], epsilon),
			true,
		);

		// worse in the first, better in the other two ❌
		assert_eq!(
			is_score_better([9, 30, 10], [10, 20, 30], epsilon),
			false,
		);

		// equal in the first, the second one dictates.
		assert_eq!(
			is_score_better([10, 25, 40], [10, 20, 30], epsilon),
			true,
		);

		// equal in the first two, the last one dictates.
		assert_eq!(
			is_score_better([10, 20, 40], [10, 20, 30], epsilon),
			false,
		);
	}

	#[test]
	fn score_comparison_with_epsilon() {
		let epsilon = Perbill::from_percent(1);

		{
			// no more than 1 percent (10) better in the first param.
			assert_eq!(
				is_score_better([1009, 5000, 100000], [1000, 5000, 100000], epsilon),
				false,
			);

			// now equal, still not better.
			assert_eq!(
				is_score_better([1010, 5000, 100000], [1000, 5000, 100000], epsilon),
				false,
			);

			// now it is.
			assert_eq!(
				is_score_better([1011, 5000, 100000], [1000, 5000, 100000], epsilon),
				true,
			);
		}

		{
			// First score score is epsilon better, but first score is no longer `ge`. Then this is
			// still not a good solution.
			assert_eq!(
				is_score_better([999, 6000, 100000], [1000, 5000, 100000], epsilon),
				false,
			);
		}

		{
			// first score is equal or better, but not epsilon. Then second one is the determinant.
			assert_eq!(
				is_score_better([1005, 5000, 100000], [1000, 5000, 100000], epsilon),
				false,
			);

			assert_eq!(
				is_score_better([1005, 5050, 100000], [1000, 5000, 100000], epsilon),
				false,
			);

			assert_eq!(
				is_score_better([1005, 5051, 100000], [1000, 5000, 100000], epsilon),
				true,
			);
		}

		{
			// first score and second are equal or less than epsilon more, third is determinant.
			assert_eq!(
				is_score_better([1005, 5025, 100000], [1000, 5000, 100000], epsilon),
				false,
			);

			assert_eq!(
				is_score_better([1005, 5025, 99_000], [1000, 5000, 100000], epsilon),
				false,
			);

			assert_eq!(
				is_score_better([1005, 5025, 98_999], [1000, 5000, 100000], epsilon),
				true,
			);
		}
	}

	#[test]
	fn score_comparison_large_value() {
		// some random value taken from eras in kusama.
		let initial = [12488167277027543u128, 5559266368032409496, 118749283262079244270992278287436446];
		// this claim is 0.04090% better in the third component. It should be accepted as better if
		// epsilon is smaller than 5/10_0000
		let claim = [12488167277027543u128, 5559266368032409496, 118700736389524721358337889258988054];

		assert_eq!(
			is_score_better(
				claim.clone(),
				initial.clone(),
				Perbill::from_rational_approximation(1u32, 10_000),
			),
			true,
		);

		assert_eq!(
			is_score_better(
				claim.clone(),
				initial.clone(),
				Perbill::from_rational_approximation(2u32, 10_000),
			),
			true,
		);

		assert_eq!(
			is_score_better(
				claim.clone(),
				initial.clone(),
				Perbill::from_rational_approximation(3u32, 10_000),
			),
			true,
		);

		assert_eq!(
			is_score_better(
				claim.clone(),
				initial.clone(),
				Perbill::from_rational_approximation(4u32, 10_000),
			),
			true,
		);

		assert_eq!(
			is_score_better(
				claim.clone(),
				initial.clone(),
				Perbill::from_rational_approximation(5u32, 10_000),
			),
			false,
		);
	}
}

mod compact {
	use codec::{Decode, Encode};
	use super::AccountId;
	// these need to come from the same dev-dependency `sp-npos-elections`, not from the crate.
	use crate::{
		generate_compact_solution_type, VoteWeight, Assignment, StakedAssignment,
		Error as PhragmenError, ExtendedBalance,
	};
	use sp_std::{convert::{TryInto, TryFrom}, fmt::Debug};
	use sp_arithmetic::Percent;

	type Accuracy = Percent;

	generate_compact_solution_type!(TestCompact, 16);

	#[test]
	fn compact_struct_is_codec() {
		let compact = TestCompact::<_, _, _> {
			votes1: vec![(2u64, 20), (4, 40)],
			votes2: vec![
				(1, (10, Accuracy::from_percent(80)), 11),
				(5, (50, Accuracy::from_percent(85)), 51),
			],
			..Default::default()
		};

		let encoded = compact.encode();

		assert_eq!(
			compact,
			Decode::decode(&mut &encoded[..]).unwrap(),
		);
		assert_eq!(compact.len(), 4);
		assert_eq!(compact.edge_count(), 2 + 4);
	}

	fn basic_ratio_test_with<V, T>() where
		V: codec::Codec + Copy + Default + PartialEq + Eq + TryInto<usize> + TryFrom<usize> + From<u8> + Debug,
		T: codec::Codec + Copy + Default + PartialEq + Eq + TryInto<usize> + TryFrom<usize> + From<u8> + Debug,
		<V as TryFrom<usize>>::Error: std::fmt::Debug,
		<T as TryFrom<usize>>::Error: std::fmt::Debug,
		<V as TryInto<usize>>::Error: std::fmt::Debug,
		<T as TryInto<usize>>::Error: std::fmt::Debug,
	{
		let voters = vec![
			2 as AccountId,
			4,
			1,
			5,
			3,
		];
		let targets = vec![
			10 as AccountId,
			11,
			20, // 2
			30,
			31, // 4
			32,
			40, // 6
			50,
			51, // 8
		];

		let assignments = vec![
			Assignment {
				who: 2 as AccountId,
				distribution: vec![(20u64, Accuracy::from_percent(100))]
			},
			Assignment {
				who: 4,
				distribution: vec![(40, Accuracy::from_percent(100))],
			},
			Assignment {
				who: 1,
				distribution: vec![
					(10, Accuracy::from_percent(80)),
					(11, Accuracy::from_percent(20))
				],
			},
			Assignment {
				who: 5,
				distribution: vec![
					(50, Accuracy::from_percent(85)),
					(51, Accuracy::from_percent(15)),
				]
			},
			Assignment {
				who: 3,
				distribution: vec![
					(30, Accuracy::from_percent(50)),
					(31, Accuracy::from_percent(25)),
					(32, Accuracy::from_percent(25)),
				],
			},
		];

		let voter_index = |a: &AccountId| -> Option<V> {
			voters.iter().position(|x| x == a).map(TryInto::try_into).unwrap().ok()
		};
		let target_index = |a: &AccountId| -> Option<T> {
			targets.iter().position(|x| x == a).map(TryInto::try_into).unwrap().ok()
		};

		let compacted = <TestCompact<V, T, Percent>>::from_assignment(
			assignments.clone(),
			voter_index,
			target_index,
		).unwrap();

		// basically number of assignments that it is encoding.
		assert_eq!(compacted.len(), assignments.len());
		assert_eq!(
			compacted.edge_count(),
			assignments.iter().fold(0, |a, b| a + b.distribution.len()),
		);

		assert_eq!(
			compacted,
			TestCompact {
				votes1: vec![(V::from(0u8), T::from(2u8)), (V::from(1u8), T::from(6u8))],
				votes2: vec![
					(V::from(2u8), (T::from(0u8), Accuracy::from_percent(80)), T::from(1u8)),
					(V::from(3u8), (T::from(7u8), Accuracy::from_percent(85)), T::from(8u8)),
				],
				votes3: vec![
					(
						V::from(4),
						[(T::from(3u8), Accuracy::from_percent(50)), (T::from(4u8), Accuracy::from_percent(25))],
						T::from(5u8),
					),
				],
				..Default::default()
			}
		);

		let voter_at = |a: V| -> Option<AccountId> { voters.get(<V as TryInto<usize>>::try_into(a).unwrap()).cloned() };
		let target_at = |a: T| -> Option<AccountId> { targets.get(<T as TryInto<usize>>::try_into(a).unwrap()).cloned() };

		assert_eq!(
			compacted.into_assignment(voter_at, target_at).unwrap(),
			assignments,
		);
	}

	#[test]
	fn basic_from_and_into_compact_works_assignments() {
		basic_ratio_test_with::<u16, u16>();
		basic_ratio_test_with::<u16, u32>();
		basic_ratio_test_with::<u8, u32>();
	}

	#[test]
	fn basic_from_and_into_compact_works_staked_assignments() {
		let voters = vec![
			2 as AccountId,
			4,
			1,
			5,
			3,
		];
		let targets = vec![
			10 as AccountId, 11,
			20,
			30, 31, 32,
			40,
			50, 51,
		];

		let assignments = vec![
			StakedAssignment {
				who: 2 as AccountId,
				distribution: vec![(20, 100 as ExtendedBalance)]
			},
			StakedAssignment {
				who: 4,
				distribution: vec![(40, 100)],
			},
			StakedAssignment {
				who: 1,
				distribution: vec![
					(10, 80),
					(11, 20)
				],
			},
			StakedAssignment {
				who: 5, distribution:
				vec![
					(50, 85),
					(51, 15),
				]
			},
			StakedAssignment {
				who: 3,
				distribution: vec![
					(30, 50),
					(31, 25),
					(32, 25),
				],
			},
		];

		let voter_index = |a: &AccountId| -> Option<u16> {
			voters.iter().position(|x| x == a).map(TryInto::try_into).unwrap().ok()
		};
		let target_index = |a: &AccountId| -> Option<u16> {
			targets.iter().position(|x| x == a).map(TryInto::try_into).unwrap().ok()
		};

		let compacted = <TestCompact<u16, u16, ExtendedBalance>>::from_staked(
			assignments.clone(),
			voter_index,
			target_index,
		).unwrap();
		assert_eq!(compacted.len(), assignments.len());
		assert_eq!(
			compacted.edge_count(),
			assignments.iter().fold(0, |a, b| a + b.distribution.len()),
		);

		assert_eq!(
			compacted,
			TestCompact {
				votes1: vec![(0, 2), (1, 6)],
				votes2: vec![
					(2, (0, 80), 1),
					(3, (7, 85), 8),
				],
				votes3: vec![
					(4, [(3, 50), (4, 25)], 5),
				],
				..Default::default()
			}
		);

		let max_of_fn = |_: &AccountId| -> VoteWeight { 100 };
		let voter_at = |a: u16| -> Option<AccountId> { voters.get(a as usize).cloned() };
		let target_at = |a: u16| -> Option<AccountId> { targets.get(a as usize).cloned() };

		assert_eq!(
			compacted.into_staked(
				max_of_fn,
				voter_at,
				target_at,
			).unwrap(),
			assignments,
		);
	}

	#[test]
	fn compact_into_stake_must_report_overflow() {
		// The last edge which is computed from the rest should ALWAYS be positive.
		// in votes2
		let compact = TestCompact::<u16, u16, ExtendedBalance> {
			votes1: Default::default(),
			votes2: vec![(0, (1, 10), 2)],
			..Default::default()
		};

		let entity_at = |a: u16| -> Option<AccountId> { Some(a as AccountId) };
		let max_of = |_: &AccountId| -> VoteWeight { 5 };

		assert_eq!(
			compact.into_staked(&max_of, &entity_at, &entity_at).unwrap_err(),
			PhragmenError::CompactStakeOverflow,
		);

		// in votes3 onwards
		let compact = TestCompact::<u16, u16, ExtendedBalance> {
			votes1: Default::default(),
			votes2: Default::default(),
			votes3: vec![(0, [(1, 7), (2, 8)], 3)],
			..Default::default()
		};

		assert_eq!(
			compact.into_staked(&max_of, &entity_at, &entity_at).unwrap_err(),
			PhragmenError::CompactStakeOverflow,
		);

		// Also if equal
		let compact = TestCompact::<u16, u16, ExtendedBalance> {
			votes1: Default::default(),
			votes2: Default::default(),
			// 5 is total, we cannot leave none for 30 here.
			votes3: vec![(0, [(1, 3), (2, 2)], 3)],
			..Default::default()
		};

		assert_eq!(
			compact.into_staked(&max_of, &entity_at, &entity_at).unwrap_err(),
			PhragmenError::CompactStakeOverflow,
		);
	}

	#[test]
	fn compact_into_assignment_must_report_overflow() {
		// in votes2
		let compact = TestCompact::<u16, u16, Accuracy> {
			votes1: Default::default(),
			votes2: vec![(0, (1, Accuracy::from_percent(100)), 2)],
			..Default::default()
		};

		let entity_at = |a: u16| -> Option<AccountId> { Some(a as AccountId) };

		assert_eq!(
			compact.into_assignment(&entity_at, &entity_at).unwrap_err(),
			PhragmenError::CompactStakeOverflow,
		);

		// in votes3 onwards
		let compact = TestCompact::<u16, u16, Accuracy> {
			votes1: Default::default(),
			votes2: Default::default(),
			votes3: vec![(0, [(1, Accuracy::from_percent(70)), (2, Accuracy::from_percent(80))], 3)],
			..Default::default()
		};

		assert_eq!(
			compact.into_assignment(&entity_at, &entity_at).unwrap_err(),
			PhragmenError::CompactStakeOverflow,
		);
	}

	#[test]
	fn target_count_overflow_is_detected() {
		let assignments = vec![
			StakedAssignment {
				who: 1 as AccountId,
				distribution: (10..26).map(|i| (i as AccountId, i as ExtendedBalance)).collect::<Vec<_>>(),
			},
		];

		let entity_index = |a: &AccountId| -> Option<u16> { Some(*a as u16) };

		let compacted = <TestCompact<u16, u16, ExtendedBalance>>::from_staked(
			assignments.clone(),
			entity_index,
			entity_index,
		);

		assert!(compacted.is_ok());

		let assignments = vec![
			StakedAssignment {
				who: 1 as AccountId,
				distribution: (10..27).map(|i| (i as AccountId, i as ExtendedBalance)).collect::<Vec<_>>(),
			},
		];

		let compacted = <TestCompact<u16, u16, ExtendedBalance>>::from_staked(
			assignments.clone(),
			entity_index,
			entity_index,
		);

		assert_eq!(
			compacted.unwrap_err(),
			PhragmenError::CompactTargetOverflow,
		);

		let assignments = vec![
			Assignment {
				who: 1 as AccountId,
				distribution: (10..27).map(|i| (i as AccountId, Percent::from_parts(i as u8))).collect::<Vec<_>>(),
			},
		];

		let compacted = <TestCompact<u16, u16, Percent>>::from_assignment(
			assignments.clone(),
			entity_index,
			entity_index,
		);

		assert_eq!(
			compacted.unwrap_err(),
			PhragmenError::CompactTargetOverflow,
		);
	}

		#[test]
	fn zero_target_count_is_ignored() {
		let voters = vec![1 as AccountId, 2];
		let targets = vec![10 as AccountId, 11];

		let assignments = vec![
			StakedAssignment {
				who: 1 as AccountId,
				distribution: vec![(10, 100 as ExtendedBalance), (11, 100)]
			},
			StakedAssignment {
				who: 2,
				distribution: vec![],
			},
		];

		let voter_index = |a: &AccountId| -> Option<u16> {
			voters.iter().position(|x| x == a).map(TryInto::try_into).unwrap().ok()
		};
		let target_index = |a: &AccountId| -> Option<u16> {
			targets.iter().position(|x| x == a).map(TryInto::try_into).unwrap().ok()
		};

		let compacted = <TestCompact<u16, u16, ExtendedBalance>>::from_staked(
			assignments.clone(),
			voter_index,
			target_index,
		).unwrap();

		assert_eq!(
			compacted,
			TestCompact {
				votes1: Default::default(),
				votes2: vec![(0, (0, 100), 1)],
				..Default::default()
			}
		);
	}
}
