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

//! This module contains helper methods to configure account roles for existing collections.

use crate::*;
use frame_support::pallet_prelude::*;
use sp_std::collections::btree_map::BTreeMap;

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Set the team roles for a specific collection.
	///
	/// - `maybe_check_owner`: An optional account ID used to check ownership permission. If `None`,
	///   it is considered as the root.
	/// - `collection`: The ID of the collection for which to set the team roles.
	/// - `issuer`: An optional account ID representing the issuer role.
	/// - `admin`: An optional account ID representing the admin role.
	/// - `freezer`: An optional account ID representing the freezer role.
	///
	/// This function allows the owner or the root (when `maybe_check_owner` is `None`) to set the
	/// team roles for a specific collection. The root can change the role from `None` to
	/// `Some(account)`, but other roles can only be updated by the root or an account with an
	/// existing role in the collection.
	pub(crate) fn do_set_team(
		maybe_check_owner: Option<T::AccountId>,
		collection: T::CollectionId,
		issuer: Option<T::AccountId>,
		admin: Option<T::AccountId>,
		freezer: Option<T::AccountId>,
	) -> DispatchResult {
		Collection::<T, I>::try_mutate(collection, |maybe_details| {
			let details = maybe_details.as_mut().ok_or(Error::<T, I>::UnknownCollection)?;
			let is_root = maybe_check_owner.is_none();
			if let Some(check_origin) = maybe_check_owner {
				ensure!(check_origin == details.owner, Error::<T, I>::NoPermission);
			}

			let roles_map = [
				(issuer.clone(), CollectionRole::Issuer),
				(admin.clone(), CollectionRole::Admin),
				(freezer.clone(), CollectionRole::Freezer),
			];

			// only root can change the role from `None` to `Some(account)`
			if !is_root {
				for (account, role) in roles_map.iter() {
					if account.is_some() {
						ensure!(
							Self::find_account_by_role(&collection, *role).is_some(),
							Error::<T, I>::NoPermission
						);
					}
				}
			}

			let roles = roles_map
				.into_iter()
				.filter_map(|(account, role)| account.map(|account| (account, role)))
				.collect();

			let account_to_role = Self::group_roles_by_account(roles);

			// Delete the previous records.
			Self::clear_roles(&collection)?;

			// Insert new records.
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
	/// This function clears all the roles associated with the given `collection_id`. It throws an
	/// error if some of the roles were left in storage, indicating that the maximum number of roles
	/// may need to be adjusted.
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
	/// Returns `true` if the account has the specified role, `false` otherwise.
	pub(crate) fn has_role(
		collection_id: &T::CollectionId,
		account_id: &T::AccountId,
		role: CollectionRole,
	) -> bool {
		CollectionRoleOf::<T, I>::get(&collection_id, &account_id)
			.map_or(false, |roles| roles.has_role(role))
	}

	/// Finds the account by a provided role within a collection.
	///
	/// - `collection_id`: A collection to check the role in.
	/// - `role`: A role to find the account for.
	///
	/// Returns `Some(T::AccountId)` if the record was found, `None` otherwise.
	pub(crate) fn find_account_by_role(
		collection_id: &T::CollectionId,
		role: CollectionRole,
	) -> Option<T::AccountId> {
		CollectionRoleOf::<T, I>::iter_prefix(&collection_id).into_iter().find_map(
			|(account, roles)| if roles.has_role(role) { Some(account.clone()) } else { None },
		)
	}

	/// Groups provided roles by account, given one account could have multiple roles.
	///
	/// - `input`: A vector of (Account, Role) tuples.
	///
	/// Returns a grouped vector of `(Account, Roles)` tuples.
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
