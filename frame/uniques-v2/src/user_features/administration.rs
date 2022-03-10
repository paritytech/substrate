// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use crate::*;
use enumflags2::BitFlags;
use frame_support::pallet_prelude::*;

impl<T: Config> Pallet<T> {
	pub fn do_set_admin(
		id: CollectionIdOf<T>,
		config: TokenConfig,
		maybe_caller: Option<T::AccountId>,
		new_admin: T::AccountId,
	) -> DispatchResult {
		let user_features: BitFlags<UserFeatures> = config.user_features.into();
		ensure!(user_features.contains(UserFeatures::Administration), Error::<T>::NotConfigured);
		Admins::<T>::try_mutate(id, |maybe_admin| -> DispatchResult {
			if let Some(caller) = maybe_caller {
				if let Some(admin) = maybe_admin {
					ensure!(admin == &caller, Error::<T>::NotAuthorized);
				}
			}

			*maybe_admin = Some(new_admin);
			Ok(())
		})?;
		Ok(())
	}
}
