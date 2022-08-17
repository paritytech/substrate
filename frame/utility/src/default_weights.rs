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

//! Weights for pallet_utility
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0
//! DATE: 2020-10-02, STEPS: [50], REPEAT: 20, LOW RANGE: [], HIGH RANGE: []

#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};

impl crate::WeightInfo for () {
	fn batch(c: u32, ) -> Weight {
		(20_803_000 as Weight)
			.saturating_add((1_984_000 as Weight).saturating_mul(c as Weight))
	}
	fn as_derivative() -> Weight {
		(5_853_000 as Weight)
	}
	fn batch_all(c: u32, ) -> Weight {
		(21_104_000 as Weight)
			.saturating_add((1_509_000 as Weight).saturating_mul(c as Weight))
	}
}
