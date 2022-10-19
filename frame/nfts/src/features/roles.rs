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
use sp_std::collections::btree_map::BTreeMap;

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	pub(crate) fn has_role(
		collection_id: &T::CollectionId,
		account_id: &T::AccountId,
		role: CollectionRole,
	) -> bool {
		CollectionRoleOf::<T, I>::get(&collection_id, &account_id)
			.map_or(false, |roles| roles.has_role(role))
	}

	/// Groups provided roles by account, given one account could have multiple roles.
	///
	/// - `input`: A vector of (Account, Role) tuples.
	///
	/// Returns a grouped vector.
	pub fn group_roles_by_account(
		input: Vec<(T::AccountId, CollectionRole)>,
	) -> Vec<(T::AccountId, CollectionRoles)> {
		let mut result = BTreeMap::new();
		for (account, role) in input.into_iter() {
			let roles = result.entry(account).or_insert(CollectionRoles::none());
			roles.add_role(role);
		}
		result.into_iter().collect()
	}
}
