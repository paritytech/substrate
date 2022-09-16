// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

use crate::{Config, Weight, CurrentSchedule, Pallet, Schedule};
use frame_support::traits::{GetPalletVersion, PalletVersion, Get};

pub fn migrate<T: Config>() -> Weight {
	let mut weight: Weight = 0;

	match <Pallet<T>>::storage_version() {
		// Replace the schedule with the new default and increment its version.
		Some(version) if version == PalletVersion::new(3, 0, 0) => {
			weight = weight.saturating_add(T::DbWeight::get().reads_writes(1, 1));
			let _ = <CurrentSchedule<T>>::translate::<u32, _>(|version| {
				version.map(|version| Schedule {
						version: version.saturating_add(1),
						// Default limits were not decreased. Therefore it is OK to overwrite
						// the schedule with the new defaults.
						.. Default::default()
					})
			});
		}
		_ => (),
	}

	weight
}
