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

//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0-rc6

#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};

impl crate::WeightInfo for () {
	fn vote(v: u32, ) -> Weight {
		(131640000 as Weight)
			.saturating_add((174000 as Weight).saturating_mul(v as Weight))
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn vote_update(v: u32, ) -> Weight {
		(82947000 as Weight)
			.saturating_add((710000 as Weight).saturating_mul(v as Weight))
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn remove_voter() -> Weight {
		(117312000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn report_defunct_voter_correct(c: u32, v: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((1649000 as Weight).saturating_mul(c as Weight))
			.saturating_add((35367000 as Weight).saturating_mul(v as Weight))
			.saturating_add(DbWeight::get().reads(6 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn report_defunct_voter_incorrect(c: u32, v: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((1683000 as Weight).saturating_mul(c as Weight))
			.saturating_add((35548000 as Weight).saturating_mul(v as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
	}
	fn submit_candidacy(c: u32, ) -> Weight {
		(99786000 as Weight)
			.saturating_add((289000 as Weight).saturating_mul(c as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn renounce_candidacy_candidate(c: u32, ) -> Weight {
		(65481000 as Weight)
			.saturating_add((173000 as Weight).saturating_mul(c as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn renounce_candidacy_members() -> Weight {
		(107379000 as Weight)
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(4 as Weight))
	}
	fn renounce_candidacy_runners_up() -> Weight {
		(65798000 as Weight)
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn remove_member_with_replacement() -> Weight {
		(101751000 as Weight)
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(5 as Weight))
	}
	fn remove_member_wrong_refund() -> Weight {
		(11328000 as Weight)
			.saturating_add(DbWeight::get().reads(1 as Weight))
	}
}
