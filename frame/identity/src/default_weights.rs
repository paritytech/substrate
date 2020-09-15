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
	fn add_registrar(r: u32, ) -> Weight {
		(38525000 as Weight)
			.saturating_add((427000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_identity(r: u32, x: u32, ) -> Weight {
		(107872000 as Weight)
			.saturating_add((419000 as Weight).saturating_mul(r as Weight))
			.saturating_add((3013000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_subs_new(s: u32, ) -> Weight {
		(76452000 as Weight)
			.saturating_add((14836000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().reads((1 as Weight).saturating_mul(s as Weight)))
			.saturating_add(DbWeight::get().writes(1 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn set_subs_old(p: u32, ) -> Weight {
		(70274000 as Weight)
			.saturating_add((5518000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(p as Weight)))
	}
	fn add_sub(p: u32, ) -> Weight {
		(108119000 as Weight)
			.saturating_add((245000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn rename_sub(p: u32, ) -> Weight {
		(35829000 as Weight)
			.saturating_add((67000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn remove_sub(p: u32, ) -> Weight {
		(101562000 as Weight)
			.saturating_add((216000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn quit_sub(p: u32, ) -> Weight {
		(64745000 as Weight)
			.saturating_add((210000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn clear_identity(r: u32, s: u32, x: u32, ) -> Weight {
		(89640000 as Weight)
			.saturating_add((270000 as Weight).saturating_mul(r as Weight))
			.saturating_add((5488000 as Weight).saturating_mul(s as Weight))
			.saturating_add((1647000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn request_judgement(r: u32, x: u32, ) -> Weight {
		(108673000 as Weight)
			.saturating_add((491000 as Weight).saturating_mul(r as Weight))
			.saturating_add((3236000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn cancel_request(r: u32, x: u32, ) -> Weight {
		(94605000 as Weight)
			.saturating_add((341000 as Weight).saturating_mul(r as Weight))
			.saturating_add((3205000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_fee(r: u32, ) -> Weight {
		(15928000 as Weight)
			.saturating_add((377000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_account_id(r: u32, ) -> Weight {
		(17940000 as Weight)
			.saturating_add((388000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_fields(r: u32, ) -> Weight {
		(15781000 as Weight)
			.saturating_add((391000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn provide_judgement(r: u32, x: u32, ) -> Weight {
		(71415000 as Weight)
			.saturating_add((445000 as Weight).saturating_mul(r as Weight))
			.saturating_add((3212000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn kill_identity(r: u32, s: u32, x: u32, ) -> Weight {
		(115969000 as Weight)
			.saturating_add((161000 as Weight).saturating_mul(r as Weight))
			.saturating_add((5509000 as Weight).saturating_mul(s as Weight))
			.saturating_add((1635000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
}
