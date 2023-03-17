// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
use frame_support::pallet_prelude::*;
use sp_std::collections::btree_map::BTreeMap;

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	pub(crate) fn do_set_team(
		maybe_check_owner: Option<T::AccountId>,
		collection: T::CollectionId,
		issuer: T::AccountId,
		admin: T::AccountId,
		freezer: T::AccountId,
	) -> DispatchResult {
		Collection::<T, I>::try_mutate(collection, |maybe_details| {
			let details = maybe_details.as_mut().ok_or(Error::<T, I>::UnknownCollection)?;
			if let Some(check_origin) = maybe_check_owner {
				ensure!(check_origin == details.owner, Error::<T, I>::NoPermission);
			}

			// delete previous values
			Self::clear_roles(&collection)?;

			let account_to_role = Self::group_roles_by_account(vec![
				(issuer.clone(), CollectionRole::Issuer),
				(admin.clone(), CollectionRole::Admin),
				(freezer.clone(), CollectionRole::Freezer),
			]);
			for (account, roles) in account_to_role {
				CollectionRoleOf::<T, I>::insert(&collection, &account, roles);
			}

			Self::deposit_event(Event::TeamChanged { collection, issuer, admin, freezer });
			Ok(())
		})
	}

	/// Clears all the roles in a specified collection.
	///
	/// - `collection_id`: A collection to clear the roles in.
	///
	/// Throws an error if some of the roles were left in storage.
	/// This means the `CollectionRoles::max_roles()` needs to be adjusted.
	pub(crate) fn clear_roles(collection_id: &T::CollectionId) -> Result<(), DispatchError> {
		let res = CollectionRoleOf::<T, I>::clear_prefix(
			&collection_id,
			CollectionRoles::max_roles() as u32,
			None,
		);
		ensure!(res.maybe_cursor.is_none(), Error::<T, I>::RolesNotCleared);
		Ok(())
	}

	/// Returns true if a specified account has a provided role within that collection.
	///
	/// - `collection_id`: A collection to check the role in.
	/// - `account_id`: An account to check the role for.
	/// - `role`: A role to validate.
	///
	/// Returns boolean.
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
			result.entry(account).or_insert(CollectionRoles::none()).add_role(role);
		}
		result.into_iter().collect()
	}
}
