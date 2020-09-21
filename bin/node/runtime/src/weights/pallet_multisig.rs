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

pub struct WeightInfo;
impl pallet_multisig::WeightInfo for WeightInfo {
	fn as_multi_threshold_1(z: u32, ) -> Weight {
		(14_749_000 as Weight)
			.saturating_add((1_000 as Weight).saturating_mul(z as Weight))
	}
	fn as_multi_create(s: u32, z: u32, ) -> Weight {
		(74_556_000 as Weight)
			.saturating_add((135_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((1_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn as_multi_create_store(s: u32, z: u32, ) -> Weight {
		(84_401_000 as Weight)
			.saturating_add((132_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((3_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn as_multi_approve(s: u32, z: u32, ) -> Weight {
		(45_680_000 as Weight)
			.saturating_add((137_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((1_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn as_multi_approve_store(s: u32, z: u32, ) -> Weight {
		(80_718_000 as Weight)
			.saturating_add((172_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((3_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn as_multi_complete(s: u32, z: u32, ) -> Weight {
		(91_869_000 as Weight)
			.saturating_add((274_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((6_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn approve_as_multi_create(s: u32, ) -> Weight {
		(74_413_000 as Weight)
			.saturating_add((143_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn approve_as_multi_approve(s: u32, ) -> Weight {
		(44_624_000 as Weight)
			.saturating_add((165_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn approve_as_multi_complete(s: u32, ) -> Weight {
		(169_412_000 as Weight)
			.saturating_add((283_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn cancel_as_multi(s: u32, ) -> Weight {
		(120_213_000 as Weight)
			.saturating_add((122_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
}
