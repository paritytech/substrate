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
		(39_603_000 as Weight)
			.saturating_add((418_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_identity(r: u32, x: u32, ) -> Weight {
		(110_679_000 as Weight)
			.saturating_add((389_000 as Weight).saturating_mul(r as Weight))
			.saturating_add((2_985_000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_subs_new(s: u32, ) -> Weight {
		(78_697_000 as Weight)
			.saturating_add((15_225_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().reads((1 as Weight).saturating_mul(s as Weight)))
			.saturating_add(DbWeight::get().writes(1 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn set_subs_old(p: u32, ) -> Weight {
		(71_308_000 as Weight)
			.saturating_add((5_772_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(p as Weight)))
	}
	fn clear_identity(r: u32, s: u32, x: u32, ) -> Weight {
		(91_553_000 as Weight)
			.saturating_add((284_000 as Weight).saturating_mul(r as Weight))
			.saturating_add((5_749_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((1_621_000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn request_judgement(r: u32, x: u32, ) -> Weight {
		(110_856_000 as Weight)
			.saturating_add((496_000 as Weight).saturating_mul(r as Weight))
			.saturating_add((3_221_000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn cancel_request(r: u32, x: u32, ) -> Weight {
		(96_857_000 as Weight)
			.saturating_add((311_000 as Weight).saturating_mul(r as Weight))
			.saturating_add((3_204_000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_fee(r: u32, ) -> Weight {
		(16_276_000 as Weight)
			.saturating_add((381_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_account_id(r: u32, ) -> Weight {
		(18_530_000 as Weight)
			.saturating_add((391_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_fields(r: u32, ) -> Weight {
		(16_359_000 as Weight)
			.saturating_add((379_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn provide_judgement(r: u32, x: u32, ) -> Weight {
		(72_869_000 as Weight)
			.saturating_add((423_000 as Weight).saturating_mul(r as Weight))
			.saturating_add((3_187_000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn kill_identity(r: u32, s: u32, x: u32, ) -> Weight {
		(123_199_000 as Weight)
			.saturating_add((71_000 as Weight).saturating_mul(r as Weight))
			.saturating_add((5_730_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((2_000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn add_sub(s: u32, ) -> Weight {
		(110_070_000 as Weight)
			.saturating_add((262_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn rename_sub(s: u32, ) -> Weight {
		(37_130_000 as Weight)
			.saturating_add((79_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn remove_sub(s: u32, ) -> Weight {
		(103_295_000 as Weight)
			.saturating_add((235_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn quit_sub(s: u32, ) -> Weight {
		(65_716_000 as Weight)
			.saturating_add((227_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
}
