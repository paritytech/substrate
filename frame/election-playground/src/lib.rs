// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! A pallet that adds no functionality but only provides end-to-end tests for the election
//! pipeline.
//!
//! Some tests are written as standalone tests using the [`mock`] module as the runtime. Some will
//! be written such that they can be used against any runtime. In other words, anu runtime that
//! fulfills [`ElectionRuntime`].
//!
//! It will also expose some functions as runtime APIs. This allows a test client (e.g. try-runtime)
//! to call into these functions from wasm.

use frame_support::pallet_prelude::*;
use sp_runtime::traits::One;

#[cfg(test)]
mod mock;

pub trait ElectionRuntime:
	pallet_election_provider_multi_phase::Config + pallet_staking::Config + pallet_bags_list::Config
{
}
impl<
		T: pallet_election_provider_multi_phase::Config
			+ pallet_staking::Config
			+ pallet_bags_list::Config,
	> ElectionRuntime for T
{
}

pub fn roll_to<T: ElectionRuntime>(n: T::BlockNumber, foo: u32) {
	let now = frame_system::Pallet::<T>::block_number();
	for i in now + One::one()..=n {
		frame_system::Pallet::<T>::set_block_number(i);
		pallet_bags_list::Pallet::<T>::on_initialize(i);
		pallet_election_provider_multi_phase::Pallet::<T>::on_initialize(i);
		pallet_staking::Pallet::<T>::on_initialize(i);
	}
}

pub fn roll_to_with_ocw<T: ElectionRuntime>(n: T::BlockNumber) {
	let now = frame_system::Pallet::<T>::block_number();
	for i in now + One::one()..=n {
		frame_system::Pallet::<T>::set_block_number(i);
		pallet_bags_list::Pallet::<T>::on_initialize(i);
		pallet_election_provider_multi_phase::Pallet::<T>::on_initialize(i);
		pallet_election_provider_multi_phase::Pallet::<T>::offchain_worker(i);
		pallet_staking::Pallet::<T>::on_initialize(i);
	}
}
