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

//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0-rc6

#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};

pub struct WeightInfo;
impl pallet_im_online::WeightInfo for WeightInfo {
	fn validate_unsigned_and_then_heartbeat(k: u32, e: u32, ) -> Weight {
		(139830000 as Weight)
			.saturating_add((211000 as Weight).saturating_mul(k as Weight))
			.saturating_add((654000 as Weight).saturating_mul(e as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
}
