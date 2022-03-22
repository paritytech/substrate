// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

//! The migrations of this pallet.

use frame_support::traits::OnRuntimeUpgrade;

/// A struct that does not migration, but only checks that the counter prefix exists and is correct.
pub struct CheckCounterPrefix<T: crate::Config>(sp_std::marker::PhantomData<T>);
impl<T: crate::Config> OnRuntimeUpgrade for CheckCounterPrefix<T> {
	fn on_runtime_upgrade() -> frame_support::weights::Weight {
		0
	}

	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<(), &'static str> {
		use frame_support::ensure;
		// The old explicit storage item.
		frame_support::generate_storage_alias!(BagsList, CounterForListNodes => Value<u32>);

		// ensure that a value exists in the counter struct.
		ensure!(
			crate::ListNodes::<T>::count() == CounterForListNodes::get().unwrap(),
			"wrong list node counter"
		);

		crate::log!(
			info,
			"checked bags-list prefix to be correct and have {} nodes",
			crate::ListNodes::<T>::count()
		);

		Ok(())
	}
}
