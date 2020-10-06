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

//! Weights for frame_system
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0
//! DATE: 2020-10-06, STEPS: [50], REPEAT: 20, LOW RANGE: [], HIGH RANGE: []

#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::Weight};
use sp_std::marker::PhantomData;

pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Trait> frame_system::WeightInfo for WeightInfo<T> {
	// WARNING! Some components were not used: ["b"]
	fn remark() -> Weight {
		(2_374_000 as Weight)
	}
	fn set_heap_pages() -> Weight {
		(3_535_000 as Weight)
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	fn set_changes_trie_config(d: u32, ) -> Weight {
		(13_805_000 as Weight)
			.saturating_add((1_000 as Weight).saturating_mul(d as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn set_storage(i: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((1_226_000 as Weight).saturating_mul(i as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(i as Weight)))
	}
	fn kill_storage(i: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((890_000 as Weight).saturating_mul(i as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(i as Weight)))
	}
	fn kill_prefix(p: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((1_753_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(p as Weight)))
	}
	fn suicide() -> Weight {
		(50_915_000 as Weight)
	}
}
