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

//! Default weights for the GRANDPA Pallet
//! This file was not auto-generated.

use frame_support::weights::{
	Weight, constants::{WEIGHT_PER_MICROS, WEIGHT_PER_NANOS, RocksDbWeight as DbWeight},
};

impl crate::WeightInfo for () {
	fn report_equivocation(validator_count: u32) -> Weight {
		// we take the validator set count from the membership proof to
		// calculate the weight but we set a floor of 100 validators.
		let validator_count = validator_count.max(100) as u64;

		// worst case we are considering is that the given offender
		// is backed by 200 nominators
		const MAX_NOMINATORS: u64 = 200;

		// checking membership proof
		(35 * WEIGHT_PER_MICROS)
			.saturating_add((175 * WEIGHT_PER_NANOS).saturating_mul(validator_count))
			.saturating_add(DbWeight::get().reads(5))
			// check equivocation proof
			.saturating_add(95 * WEIGHT_PER_MICROS)
			// report offence
			.saturating_add(110 * WEIGHT_PER_MICROS)
			.saturating_add(25 * WEIGHT_PER_MICROS * MAX_NOMINATORS)
			.saturating_add(DbWeight::get().reads(14 + 3 * MAX_NOMINATORS))
			.saturating_add(DbWeight::get().writes(10 + 3 * MAX_NOMINATORS))
			// fetching set id -> session index mappings
			.saturating_add(DbWeight::get().reads(2))
	}

	fn note_stalled() -> Weight {
		(3 * WEIGHT_PER_MICROS)
			.saturating_add(DbWeight::get().writes(1))
	}
}
