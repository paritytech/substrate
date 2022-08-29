// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

//! Default weights for the MMR Pallet
//! This file was not auto-generated.

use frame_support::weights::{
	constants::{RocksDbWeight as DbWeight, WEIGHT_PER_NANOS},
	Weight,
};

impl crate::WeightInfo for () {
	fn on_initialize(peaks: u64) -> Weight {
		// Reading the parent hash.
		let leaf_weight = DbWeight::get().reads(1);
		// Blake2 hash cost.
		let hash_weight = 2 * WEIGHT_PER_NANOS;
		// No-op hook.
		let hook_weight = Weight::zero();

		leaf_weight
			.saturating_add(hash_weight)
			.saturating_add(hook_weight)
			.saturating_add(DbWeight::get().reads_writes(2 + peaks, 2 + peaks))
	}
}
