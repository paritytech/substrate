// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

#![allow(unused_parens)]

use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};

pub struct WeightInfo;
impl frame_system::WeightInfo for WeightInfo {
	// WARNING! Some components were not used: ["b"]
	fn remark() -> Weight {
		(1305000 as Weight)
	}
	fn set_heap_pages() -> Weight {
		(2023000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	// WARNING! Some components were not used: ["d"]
	fn set_changes_trie_config() -> Weight {
		(10026000 as Weight)
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn set_storage(i: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((656000 as Weight).saturating_mul(i as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(i as Weight)))
	}
	fn kill_storage(i: u32, ) -> Weight {
		(4327000 as Weight)
			.saturating_add((478000 as Weight).saturating_mul(i as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(i as Weight)))
	}
	fn kill_prefix(p: u32, ) -> Weight {
		(8349000 as Weight)
			.saturating_add((838000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(p as Weight)))
	}
	fn suicide() -> Weight {
		(29247000 as Weight)
	}
}
