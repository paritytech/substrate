// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Weights for pallet_elections_phragmen
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0
//! DATE: 2020-10-13, STEPS: [50], REPEAT: 20, LOW RANGE: [], HIGH RANGE: []

#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::Weight};
use sp_std::marker::PhantomData;

pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Trait> pallet_elections_phragmen::WeightInfo for WeightInfo<T> {
	fn vote(v: u32, ) -> Weight {
		(91_060_000 as Weight)
			.saturating_add((305_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn vote_update(v: u32, ) -> Weight {
		(57_469_000 as Weight)
			.saturating_add((444_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn remove_voter() -> Weight {
		(81_517_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn report_defunct_voter_correct(c: u32, v: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((1_734_000 as Weight).saturating_mul(c as Weight))
			.saturating_add((31_506_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(T::DbWeight::get().reads(6 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	fn report_defunct_voter_incorrect(c: u32, v: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((1_699_000 as Weight).saturating_mul(c as Weight))
			.saturating_add((31_489_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn submit_candidacy(c: u32, ) -> Weight {
		(73_383_000 as Weight)
			.saturating_add((326_000 as Weight).saturating_mul(c as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	fn renounce_candidacy_candidate(c: u32, ) -> Weight {
		(50_694_000 as Weight)
			.saturating_add((154_000 as Weight).saturating_mul(c as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	fn renounce_candidacy_members() -> Weight {
		(77_808_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(4 as Weight))
	}
	fn renounce_candidacy_runners_up() -> Weight {
		(48_452_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	fn remove_member_with_replacement() -> Weight {
		(75_784_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(5 as Weight))
	}
	fn remove_member_wrong_refund() -> Weight {
		(9_099_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
	}
}
