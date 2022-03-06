// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Tests for solution-type.

#![cfg(test)]

use crate::{mock::*, IndexAssignment, NposSolution};
use rand::SeedableRng;
use std::convert::TryInto;

mod solution_type {
	use super::*;
	use codec::{Decode, Encode};
	// these need to come from the same dev-dependency `sp-npos-elections`, not from the crate.
	use crate::{generate_solution_type, Assignment, Error as NposError, NposSolution};
	use sp_std::{convert::TryInto, fmt::Debug};

	#[allow(dead_code)]
	mod __private {
		// This is just to make sure that the solution can be generated in a scope without any
		// imports.
		use crate::generate_solution_type;
		generate_solution_type!(
			#[compact]
			struct InnerTestSolutionIsolated::<VoterIndex = u32, TargetIndex = u8, Accuracy = sp_runtime::Percent>(12)
		);
	}

	#[test]
	fn solution_struct_works_with_and_without_compact() {
		// we use u32 size to make sure compact is smaller.
		let without_compact = {
			generate_solution_type!(
				pub struct InnerTestSolution::<
					VoterIndex = u32,
					TargetIndex = u32,
					Accuracy = TestAccuracy,
				>(16)
			);
			let solution = InnerTestSolution {
				votes1: vec![(2, 20), (4, 40)],
				votes2: vec![(1, [(10, p(80))], 11), (5, [(50, p(85))], 51)],
				..Default::default()
			};

			solution.encode().len()
		};

		let with_compact = {
			generate_solution_type!(
				#[compact]
				pub struct InnerTestSolutionCompact::<
					VoterIndex = u32,
					TargetIndex = u32,
					Accuracy = TestAccuracy,
				>(16)
			);
			let compact = InnerTestSolutionCompact {
				votes1: vec![(2, 20), (4, 40)],
				votes2: vec![(1, [(10, p(80))], 11), (5, [(50, p(85))], 51)],
				..Default::default()
			};

			compact.encode().len()
		};

		assert!(with_compact < without_compact);
	}

	#[test]
	fn solution_struct_is_codec() {
		let solution = TestSolution {
			votes1: vec![(2, 20), (4, 40)],
			votes2: vec![(1, [(10, p(80))], 11), (5, [(50, p(85))], 51)],
			..Default::default()
		};

		let encoded = solution.encode();

		assert_eq!(solution, Decode::decode(&mut &encoded[..]).unwrap());
		assert_eq!(solution.voter_count(), 4);
		assert_eq!(solution.edge_count(), 2 + 4);
		assert_eq!(solution.unique_targets(), vec![10, 11, 20, 40, 50, 51]);
	}

	#[test]
	fn remove_voter_works() {
		let mut solution = TestSolution {
			votes1: vec![(0, 2), (1, 6)],
			votes2: vec![(2, [(0, p(80))], 1), (3, [(7, p(85))], 8)],
			votes3: vec![(4, [(3, p(50)), (4, p(25))], 5)],
			..Default::default()
		};

		assert!(!solution.remove_voter(11));
		assert!(solution.remove_voter(2));
		assert_eq!(
			solution,
			TestSolution {
				votes1: vec![(0, 2), (1, 6)],
				votes2: vec![(3, [(7, p(85))], 8)],
				votes3: vec![(4, [(3, p(50)), (4, p(25))], 5,)],
				..Default::default()
			},
		);

		assert!(solution.remove_voter(4));
		assert_eq!(
			solution,
			TestSolution {
				votes1: vec![(0, 2), (1, 6)],
				votes2: vec![(3, [(7, p(85))], 8)],
				..Default::default()
			},
		);

		assert!(solution.remove_voter(1));
		assert_eq!(
			solution,
			TestSolution {
				votes1: vec![(0, 2)],
				votes2: vec![(3, [(7, p(85))], 8),],
				..Default::default()
			},
		);
	}

	#[test]
	fn from_and_into_assignment_works() {
		let voters = vec![2 as AccountId, 4, 1, 5, 3];
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
			Assignment { who: 2 as AccountId, distribution: vec![(20u64, p(100))] },
			Assignment { who: 4, distribution: vec![(40, p(100))] },
			Assignment { who: 1, distribution: vec![(10, p(80)), (11, p(20))] },
			Assignment { who: 5, distribution: vec![(50, p(85)), (51, p(15))] },
			Assignment { who: 3, distribution: vec![(30, p(50)), (31, p(25)), (32, p(25))] },
		];

		let voter_index = |a: &AccountId| -> Option<u32> {
			voters.iter().position(|x| x == a).map(TryInto::try_into).unwrap().ok()
		};
		let target_index = |a: &AccountId| -> Option<u16> {
			targets.iter().position(|x| x == a).map(TryInto::try_into).unwrap().ok()
		};

		let solution =
			TestSolution::from_assignment(&assignments, voter_index, target_index).unwrap();

		// basically number of assignments that it is encoding.
		assert_eq!(solution.voter_count(), assignments.len());
		assert_eq!(
			solution.edge_count(),
			assignments.iter().fold(0, |a, b| a + b.distribution.len()),
		);

		assert_eq!(
			solution,
			TestSolution {
				votes1: vec![(0, 2), (1, 6)],
				votes2: vec![(2, [(0, p(80))], 1), (3, [(7, p(85))], 8)],
				votes3: vec![(4, [(3, p(50)), (4, p(25))], 5)],
				..Default::default()
			}
		);

		assert_eq!(solution.unique_targets(), vec![0, 1, 2, 3, 4, 5, 6, 7, 8]);

		let voter_at = |a: u32| -> Option<AccountId> {
			voters.get(<u32 as TryInto<usize>>::try_into(a).unwrap()).cloned()
		};
		let target_at = |a: u16| -> Option<AccountId> {
			targets.get(<u16 as TryInto<usize>>::try_into(a).unwrap()).cloned()
		};

		assert_eq!(solution.into_assignment(voter_at, target_at).unwrap(), assignments);
	}

	#[test]
	fn unique_targets_len_edge_count_works() {
		// we don't really care about voters here so all duplicates. This is not invalid per se.
		let solution = TestSolution {
			votes1: vec![(99, 1), (99, 2)],
			votes2: vec![(99, [(3, p(10))], 7), (99, [(4, p(10))], 8)],
			votes3: vec![(99, [(11, p(10)), (12, p(10))], 13)],
			// ensure the last one is also counted.
			votes16: vec![(
				99,
				[
					(66, p(10)),
					(66, p(10)),
					(66, p(10)),
					(66, p(10)),
					(66, p(10)),
					(66, p(10)),
					(66, p(10)),
					(66, p(10)),
					(66, p(10)),
					(66, p(10)),
					(66, p(10)),
					(66, p(10)),
					(66, p(10)),
					(66, p(10)),
					(66, p(10)),
				],
				67,
			)],
			..Default::default()
		};

		assert_eq!(solution.unique_targets(), vec![1, 2, 3, 4, 7, 8, 11, 12, 13, 66, 67]);
		assert_eq!(solution.edge_count(), 2 + (2 * 2) + 3 + 16);
		assert_eq!(solution.voter_count(), 6);

		// this one has some duplicates.
		let solution = TestSolution {
			votes1: vec![(99, 1), (99, 1)],
			votes2: vec![(99, [(3, p(10))], 7), (99, [(4, p(10))], 8)],
			votes3: vec![(99, [(11, p(10)), (11, p(10))], 13)],
			..Default::default()
		};

		assert_eq!(solution.unique_targets(), vec![1, 3, 4, 7, 8, 11, 13]);
		assert_eq!(solution.edge_count(), 2 + (2 * 2) + 3);
		assert_eq!(solution.voter_count(), 5);
	}

	#[test]
	fn solution_into_assignment_must_report_overflow() {
		// in votes2
		let solution = TestSolution {
			votes1: Default::default(),
			votes2: vec![(0, [(1, p(100))], 2)],
			..Default::default()
		};

		let voter_at = |a: u32| -> Option<AccountId> { Some(a as AccountId) };
		let target_at = |a: u16| -> Option<AccountId> { Some(a as AccountId) };

		assert_eq!(
			solution.into_assignment(&voter_at, &target_at).unwrap_err(),
			NposError::SolutionWeightOverflow,
		);

		// in votes3 onwards
		let solution = TestSolution {
			votes1: Default::default(),
			votes2: Default::default(),
			votes3: vec![(0, [(1, p(70)), (2, p(80))], 3)],
			..Default::default()
		};

		assert_eq!(
			solution.into_assignment(&voter_at, &target_at).unwrap_err(),
			NposError::SolutionWeightOverflow,
		);
	}

	#[test]
	fn target_count_overflow_is_detected() {
		let voter_index = |a: &AccountId| -> Option<u32> { Some(*a as u32) };
		let target_index = |a: &AccountId| -> Option<u16> { Some(*a as u16) };

		let assignments = vec![Assignment {
			who: 1 as AccountId,
			distribution: (10..27).map(|i| (i as AccountId, p(i as u8))).collect::<Vec<_>>(),
		}];

		let solution = TestSolution::from_assignment(&assignments, voter_index, target_index);
		assert_eq!(solution.unwrap_err(), NposError::SolutionTargetOverflow);
	}

	#[test]
	fn zero_target_count_is_ignored() {
		let voters = vec![1 as AccountId, 2];
		let targets = vec![10 as AccountId, 11];

		let assignments = vec![
			Assignment { who: 1 as AccountId, distribution: vec![(10, p(50)), (11, p(50))] },
			Assignment { who: 2, distribution: vec![] },
		];

		let voter_index = |a: &AccountId| -> Option<u32> {
			voters.iter().position(|x| x == a).map(TryInto::try_into).unwrap().ok()
		};
		let target_index = |a: &AccountId| -> Option<u16> {
			targets.iter().position(|x| x == a).map(TryInto::try_into).unwrap().ok()
		};

		let solution =
			TestSolution::from_assignment(&assignments, voter_index, target_index).unwrap();

		assert_eq!(
			solution,
			TestSolution {
				votes1: Default::default(),
				votes2: vec![(0, [(0, p(50))], 1)],
				..Default::default()
			}
		);
	}
}

#[test]
fn index_assignments_generate_same_solution_as_plain_assignments() {
	let rng = rand::rngs::SmallRng::seed_from_u64(0);

	let (voters, assignments, candidates) = generate_random_votes(1000, 2500, rng);
	let voter_index = make_voter_fn(&voters);
	let target_index = make_target_fn(&candidates);

	let solution =
		TestSolution::from_assignment(&assignments, &voter_index, &target_index).unwrap();

	let index_assignments = assignments
		.into_iter()
		.map(|assignment| IndexAssignment::new(&assignment, &voter_index, &target_index))
		.collect::<Result<Vec<_>, _>>()
		.unwrap();

	let index_compact = index_assignments.as_slice().try_into().unwrap();

	assert_eq!(solution, index_compact);
}
