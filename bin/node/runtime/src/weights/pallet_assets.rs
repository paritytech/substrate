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

use frame_support::weights::Weight;
use sp_std::marker::PhantomData;

pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Trait> pallet_assets::WeightInfo for WeightInfo<T> {
	fn create() -> Weight { 0 as Weight }
	fn force_create() -> Weight { 0 as Weight }
	fn destroy() -> Weight { 0 as Weight }
	fn force_destroy() -> Weight { 0 as Weight }
	fn mint() -> Weight { 0 as Weight }
	fn burn() -> Weight { 0 as Weight }
	fn transfer() -> Weight { 0 as Weight }
	fn force_transfer() -> Weight { 0 as Weight }
	fn freeze() -> Weight { 0 as Weight }
	fn thaw() -> Weight { 0 as Weight }
	fn transfer_ownership() -> Weight { 0 as Weight }
	fn set_team() -> Weight { 0 as Weight }
	fn set_max_zombies() -> Weight { 0 as Weight }
}
