// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Default weights for the BEEFY Pallet
//! This file was not auto-generated.

use frame_support::weights::{
	constants::{RocksDbWeight as DbWeight, WEIGHT_REF_TIME_PER_MICROS, WEIGHT_REF_TIME_PER_NANOS},
	Weight,
};

impl crate::WeightInfo for () {
	fn report_equivocation(validator_count: u32, max_nominators_per_validator: u32) -> Weight {
		// we take the validator set count from the membership proof to
		// calculate the weight but we set a floor of 100 validators.
		let validator_count = validator_count.max(100) as u64;

		// checking membership proof
		Weight::from_parts(35u64 * WEIGHT_REF_TIME_PER_MICROS, 0)
			.saturating_add(
				Weight::from_parts(175u64 * WEIGHT_REF_TIME_PER_NANOS, 0)
					.saturating_mul(validator_count),
			)
			.saturating_add(DbWeight::get().reads(5))
			// check equivocation proof
			.saturating_add(Weight::from_parts(95u64 * WEIGHT_REF_TIME_PER_MICROS, 0))
			// report offence
			.saturating_add(Weight::from_parts(110u64 * WEIGHT_REF_TIME_PER_MICROS, 0))
			.saturating_add(Weight::from_parts(
				25u64 * WEIGHT_REF_TIME_PER_MICROS * max_nominators_per_validator as u64,
				0,
			))
			.saturating_add(DbWeight::get().reads(14 + 3 * max_nominators_per_validator as u64))
			.saturating_add(DbWeight::get().writes(10 + 3 * max_nominators_per_validator as u64))
			// fetching set id -> session index mappings
			.saturating_add(DbWeight::get().reads(2))
	}

	fn set_new_genesis() -> Weight {
		DbWeight::get().writes(1)
	}
}
