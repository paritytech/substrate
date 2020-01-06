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

//! Tests for phragmen compact.

use crate::Assignment;
use sp_runtime::Perbill;
use phragmen_compact::generate_compact_solution_type;

generate_compact_solution_type!(TestCompact, 16);

#[test]
fn basic_from_and_into_compact_works() {
	let assignments = vec![
		Assignment {
			who: 2u32,
			distribution: vec![(20, Perbill::from_percent(100))]
		},
		Assignment {
			who: 4u32,
			distribution: vec![(40, Perbill::from_percent(100))],
		},
		Assignment {
			who: 1u32,
			distribution: vec![
				(10, Perbill::from_percent(80)),
				(11, Perbill::from_percent(20))
			],
		},
		Assignment {
			who: 5u32, distribution:
			vec![
				(50, Perbill::from_percent(85)),
				(51, Perbill::from_percent(15)),
			]
		},
		Assignment {
			who: 3u32,
			distribution: vec![
				(30, Perbill::from_percent(50)),
				(31, Perbill::from_percent(25)),
				(32, Perbill::from_percent(25)),
			],
		},
	];

	let compacted: TestCompact<u32> = assignments.clone().into();

	assert_eq!(
		compacted,
		TestCompact {
			votes1: vec![(2, 20), (4, 40)],
			votes2: vec![
				(1, (10, Perbill::from_percent(80)), 11),
				(5, (50, Perbill::from_percent(85)), 51),
			],
			votes3: vec![
				(3, [(30, Perbill::from_percent(50)), (31, Perbill::from_percent(25))], 32),
			],
			..Default::default()
		}
	);

	assert_eq!(
		<TestCompact<u32> as Into<Vec<Assignment<u32>>>>::into(compacted),
		assignments
	);
}

