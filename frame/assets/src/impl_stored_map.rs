// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Assets pallet's `StoredMap` implementation.

use super::*;

impl<T: Config> StoredMap<(T::AssetId, T::AccountId), T::Extra> for Pallet<T> {
	fn get(id_who: &(T::AssetId, T::AccountId)) -> T::Extra {
		let &(id, ref who) = id_who;
		if Account::<T>::contains_key(id, who) {
			Account::<T>::get(id, who).extra
		} else {
			Default::default()
		}
	}

	fn try_mutate_exists<R, E: From<StoredMapError>>(
		id_who: &(T::AssetId, T::AccountId),
		f: impl FnOnce(&mut Option<T::Extra>) -> Result<R, E>,
	) -> Result<R, E> {
		let &(id, ref who) = id_who;
		let mut maybe_extra = Some(Account::<T>::get(id, who).extra);
		let r = f(&mut maybe_extra)?;
		// They want to write some value or delete it.
		// If the account existed and they want to write a value, then we write.
		// If the account didn't exist and they want to delete it, then we let it pass.
		// Otherwise, we fail.
		Account::<T>::try_mutate_exists(id, who, |maybe_account| {
			if let Some(extra) = maybe_extra {
				// They want to write a value. Let this happen only if the account actually exists.
				if let Some(ref mut account) = maybe_account {
					account.extra = extra;
				} else {
					Err(StoredMapError::NoProviders)?;
				}
			} else {
				// They want to delete it. Let this pass if the item never existed anyway.
				ensure!(maybe_account.is_none(), StoredMapError::ConsumerRemaining);
			}
			Ok(r)
		})
	}
}
