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

use crate::{Config, Weight, Pallet, Schedule};
use frame_support::{
	storage::StorageValue,
	traits::{GetPalletVersion, PalletVersion, Get},
};

pub fn migrate<T: Config>() -> Weight {
	let mut weight: Weight = 0;

	match <Pallet<T>>::storage_version() {
		Some(version) if version == PalletVersion::new(3, 0, 0) => {
			weight = weight.saturating_add(T::DbWeight::get().writes(1));
			v3_0_0::CurrentSchedule::<T>::kill();
		}
		_ => (),
	}

	weight
}

mod v3_0_0 {
	use super::*;

	struct Pallet<T: Config>(sp_std::marker::PhantomData<T>);

	frame_support::decl_storage! {
		trait Store for Pallet<T: Config> as Contracts {
			pub CurrentSchedule: Schedule<T>;
		}
	}
}
