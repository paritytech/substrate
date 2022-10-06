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
use itertools::Itertools;

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	pub fn has_role(
		collection_id: &T::CollectionId,
		account_id: &T::AccountId,
		role: CollectionRole,
	) -> bool {
		CollectionRoleOf::<T, I>::get(&collection_id, &account_id)
			.map_or(false, |roles| roles.values().contains(role))
	}

	pub fn group_roles_by_account(
		input: Vec<(T::AccountId, CollectionRole)>,
	) -> Vec<(T::AccountId, CollectionRoles)> {
		let mut sorted_by_account = input.clone();
		sorted_by_account.sort_by(|a, b| a.0.cmp(&b.0));

		let mut result = vec![];
		for (account, group) in &sorted_by_account.into_iter().group_by(|elt| elt.0.clone()) {
			let mut roles = CollectionRoles::empty().values();
			for (_, role) in group.collect::<Vec<(T::AccountId, CollectionRole)>>() {
				roles.insert(role);
			}
			result.push((account, CollectionRoles(roles)));
		}
		result
	}
}
