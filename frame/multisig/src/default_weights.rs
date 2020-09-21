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
	fn as_multi_threshold_1(z: u32, ) -> Weight {
		(16_663_000 as Weight)
			.saturating_add((1_000 as Weight).saturating_mul(z as Weight))
	}
	fn as_multi_create(s: u32, z: u32, ) -> Weight {
		(80_524_000 as Weight)
			.saturating_add((95_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((1_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn as_multi_create_store(s: u32, z: u32, ) -> Weight {
		(91_837_000 as Weight)
			.saturating_add((87_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((3_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn as_multi_approve(s: u32, z: u32, ) -> Weight {
		(49_536_000 as Weight)
			.saturating_add((158_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((1_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn as_multi_approve_store(s: u32, z: u32, ) -> Weight {
		(89_275_000 as Weight)
			.saturating_add((172_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((3_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn as_multi_complete(s: u32, z: u32, ) -> Weight {
		(102_536_000 as Weight)
			.saturating_add((285_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((5_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	// WARNING! Some components were not used: ["z"]
	fn approve_as_multi_create(s: u32, ) -> Weight {
		(79_991_000 as Weight)
			.saturating_add((136_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	// WARNING! Some components were not used: ["z"]
	fn approve_as_multi_approve(s: u32, ) -> Weight {
		(48_513_000 as Weight)
			.saturating_add((161_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn approve_as_multi_complete(s: u32, ) -> Weight {
		(106_934_000 as Weight)
			.saturating_add((284_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn cancel_as_multi(s: u32, ) -> Weight {
		(99_028_000 as Weight)
			.saturating_add((129_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
}
