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
		(39969000 as Weight)
			.saturating_add((439000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_identity(r: u32, x: u32, ) -> Weight {
		(111358000 as Weight)
			.saturating_add((369000 as Weight).saturating_mul(r as Weight))
			.saturating_add((3031000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn set_subs(p: u32, s: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((8242000 as Weight).saturating_mul(p as Weight))
			.saturating_add((18352000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().reads((1 as Weight).saturating_mul(s as Weight)))
			.saturating_add(DbWeight::get().writes(102 as Weight))
	}
	fn add_sub(p: u32, ) -> Weight {
		(110769000 as Weight)
			.saturating_add((259000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn rename_sub(p: u32, ) -> Weight {
		(35953000 as Weight)
			.saturating_add((88000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn remove_sub(p: u32, ) -> Weight {
		(103039000 as Weight)
			.saturating_add((243000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn quit_sub(p: u32, ) -> Weight {
		(65845000 as Weight)
			.saturating_add((227000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn clear_identity(r: u32, s: u32, x: u32, ) -> Weight {
		(92381000 as Weight)
			.saturating_add((324000 as Weight).saturating_mul(r as Weight))
			.saturating_add((5638000 as Weight).saturating_mul(s as Weight))
			.saturating_add((1681000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn request_judgement(r: u32, x: u32, ) -> Weight {
		(109858000 as Weight)
			.saturating_add((600000 as Weight).saturating_mul(r as Weight))
			.saturating_add((3301000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn cancel_request(r: u32, x: u32, ) -> Weight {
		(95303000 as Weight)
			.saturating_add((417000 as Weight).saturating_mul(r as Weight))
			.saturating_add((3260000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn set_fee(r: u32, ) -> Weight {
		(16385000 as Weight)
			.saturating_add((406000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_account_id(r: u32, ) -> Weight {
		(18470000 as Weight)
			.saturating_add((420000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_fields(r: u32, ) -> Weight {
		(16495000 as Weight)
			.saturating_add((409000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn provide_judgement(r: u32, x: u32, ) -> Weight {
		(71172000 as Weight)
			.saturating_add((563000 as Weight).saturating_mul(r as Weight))
			.saturating_add((3304000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn kill_identity(r: u32, s: u32, x: u32, ) -> Weight {
		(118471000 as Weight)
			.saturating_add((241000 as Weight).saturating_mul(r as Weight))
			.saturating_add((5647000 as Weight).saturating_mul(s as Weight))
			.saturating_add((1684000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
}
