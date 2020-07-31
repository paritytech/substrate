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

//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0-rc5

use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};

pub struct WeightInfo;
impl pallet_collective::WeightInfo for WeightInfo {
	fn set_members(m: u32, n: u32, p: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((20267000 as Weight).saturating_mul(m as Weight))
			.saturating_add((176000 as Weight).saturating_mul(n as Weight))
			.saturating_add((26230000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().reads((1 as Weight).saturating_mul(p as Weight)))
			.saturating_add(DbWeight::get().writes(2 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(p as Weight)))
	}
	fn execute(b: u32, m: u32, ) -> Weight {
		(26278000 as Weight)
			.saturating_add((111000 as Weight).saturating_mul(m as Weight))
			.saturating_add((4000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
	}
	fn propose_execute(b: u32, m: u32, ) -> Weight {
		(31972000 as Weight)
			.saturating_add((218000 as Weight).saturating_mul(m as Weight))
			.saturating_add((4000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
	}
	fn propose_proposed(b: u32, m: u32, p: u32, ) -> Weight {
		(53435000 as Weight)
			.saturating_add((158000 as Weight).saturating_mul(m as Weight))
			.saturating_add((476000 as Weight).saturating_mul(p as Weight))
			.saturating_add((2000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(4 as Weight))
	}
	fn vote(m: u32, ) -> Weight {
		(46165000 as Weight)
			.saturating_add((264000 as Weight).saturating_mul(m as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	// WARNING! Some components were not used: ["b"]
	fn close_early_disapproved(m: u32, p: u32, ) -> Weight {
		(52896000 as Weight)
			.saturating_add((242000 as Weight).saturating_mul(m as Weight))
			.saturating_add((450000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn close_early_approved(b: u32, m: u32, p: u32, ) -> Weight {
		(73235000 as Weight)
			.saturating_add((247000 as Weight).saturating_mul(m as Weight))
			.saturating_add((456000 as Weight).saturating_mul(p as Weight))
			.saturating_add((1000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	// WARNING! Some components were not used: ["b"]
	fn close_disapproved(m: u32, p: u32, ) -> Weight {
		(56171000 as Weight)
			.saturating_add((250000 as Weight).saturating_mul(m as Weight))
			.saturating_add((462000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn close_approved(b: u32, m: u32, p: u32, ) -> Weight {
		(77594000 as Weight)
			.saturating_add((246000 as Weight).saturating_mul(m as Weight))
			.saturating_add((453000 as Weight).saturating_mul(p as Weight))
			.saturating_add((2000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn disapprove_proposal(p: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((490000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
}
