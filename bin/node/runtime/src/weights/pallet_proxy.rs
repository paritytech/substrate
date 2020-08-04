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
impl pallet_proxy::WeightInfo for WeightInfo {
	fn proxy(p: u32, ) -> Weight {
		(27894000 as Weight)
			.saturating_add((196000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
	}
	fn announced_proxy(p: u32, ) -> Weight {
		(78353000 as Weight)
			.saturating_add((201000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn remove_announcement(p: u32, ) -> Weight {
		(60264000 as Weight)
			.saturating_add((4000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn reject_announcement(p: u32, ) -> Weight {
		(60141000 as Weight)
			.saturating_add((10000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn announce(p: u32, ) -> Weight {
		(74751000 as Weight)
			.saturating_add((208000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn add_proxy(p: u32, ) -> Weight {
		(36250000 as Weight)
			.saturating_add((223000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn remove_proxy(p: u32, ) -> Weight {
		(32843000 as Weight)
			.saturating_add((258000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn remove_proxies(p: u32, ) -> Weight {
		(31834000 as Weight)
			.saturating_add((203000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn anonymous(p: u32, ) -> Weight {
		(50947000 as Weight)
			.saturating_add((44000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn kill_anonymous(p: u32, ) -> Weight {
		(34213000 as Weight)
			.saturating_add((208000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
}
