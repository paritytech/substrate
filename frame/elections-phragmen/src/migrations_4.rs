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

//! Migrations to version [`4.0.0`], as denoted by the changelog.

use codec::{Encode, Decode, FullCodec};
use sp_std::prelude::*;
use frame_support::{
	RuntimeDebug, weights::Weight, Twox64Concat,
	storage::types::{StorageMap, StorageValue},
	traits::{GetPalletVersion, PalletVersion},
};

/// Migrate the entire storage of this pallet to a new prefix.
///
/// This new prefix must be the same as the one set in construct_runtime. For safety, use
/// `PalletInfo` to get it, as:
/// `<Runtime as frame_system::Config>::PalletInfo::name::<ElectionsPhragmenPallet>`.
///
/// The old storage prefix, `PhragmenElection` is hardcoded in the migration code.
pub fn migrate<T: frame_system::Config, N: AsRef<str>>(new_pallet_name: N) -> Weight {
	frame_support::migrations::move_pallet(
		b"PhragmenElection",
		new_pallet_name.as_ref().as_bytes(),
	);
	<T as frame_system::Config>::BlockWeights::get().max_block
}
