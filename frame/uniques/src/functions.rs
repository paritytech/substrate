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

//! Various pieces of common functionality.

use super::*;
use frame_support::{ensure, traits::Get};
use sp_runtime::{DispatchResult, DispatchError};

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	pub(crate) fn do_transfer(
		class: T::ClassId,
		instance: T::InstanceId,
		dest: T::AccountId,
		with_details: impl FnOnce(
			&ClassDetailsFor<T, I>,
			&mut InstanceDetailsFor<T, I>,
		) -> DispatchResult,
	) -> DispatchResult {
		let class_details = Class::<T, I>::get(&class).ok_or(Error::<T, I>::Unknown)?;
		ensure!(!class_details.is_frozen, Error::<T, I>::Frozen);

		let mut details = Asset::<T, I>::get(&class, &instance).ok_or(Error::<T, I>::Unknown)?;
		ensure!(!details.is_frozen, Error::<T, I>::Frozen);
		with_details(&class_details, &mut details)?;

		Account::<T, I>::remove((&details.owner, &class, &instance));
		Account::<T, I>::insert((&dest, &class, &instance), ());
		let origin = details.owner;
		details.owner = dest;
		Asset::<T, I>::insert(&class, &instance, &details);

		Self::deposit_event(Event::Transferred(class, instance, origin, details.owner));
		Ok(())
	}

	pub(super) fn do_mint(
		class: T::ClassId,
		instance: T::InstanceId,
		owner: T::AccountId,
		with_details: impl FnOnce(
			&ClassDetailsFor<T, I>,
		) -> DispatchResult,
	) -> DispatchResult {
		ensure!(!Asset::<T, I>::contains_key(class, instance), Error::<T, I>::AlreadyExists);

		Class::<T, I>::try_mutate(&class, |maybe_class_details| -> DispatchResult {
			let class_details = maybe_class_details.as_mut().ok_or(Error::<T, I>::Unknown)?;

			with_details(&class_details)?;

			let instances = class_details.instances.checked_add(1)
				.ok_or(ArithmeticError::Overflow)?;
			class_details.instances = instances;

			let deposit = match class_details.free_holding {
				true => Zero::zero(),
				false => T::InstanceDeposit::get(),
			};
			T::Currency::reserve(&class_details.owner, deposit)?;
			class_details.total_deposit += deposit;

			let owner = owner.clone();
			Account::<T, I>::insert((&owner, &class, &instance), ());
			let details = InstanceDetails { owner, approved: None, is_frozen: false, deposit};
			Asset::<T, I>::insert(&class, &instance, details);
			Ok(())
		})?;

		Self::deposit_event(Event::Issued(class, instance, owner));
		Ok(())
	}

	pub(super) fn do_burn(
		class: T::ClassId,
		instance: T::InstanceId,
		with_details: impl FnOnce(
			&ClassDetailsFor<T, I>,
			&InstanceDetailsFor<T, I>,
		) -> DispatchResult,
	) -> DispatchResult {
		let owner = Class::<T, I>::try_mutate(&class, |maybe_class_details| -> Result<T::AccountId, DispatchError> {
			let class_details = maybe_class_details.as_mut().ok_or(Error::<T, I>::Unknown)?;
			let details = Asset::<T, I>::get(&class, &instance)
				.ok_or(Error::<T, I>::Unknown)?;
			with_details(&class_details, &details)?;

			// Return the deposit.
			T::Currency::unreserve(&class_details.owner, details.deposit);
			class_details.total_deposit.saturating_reduce(details.deposit);
			class_details.instances.saturating_dec();
			Ok(details.owner)
		})?;

		Asset::<T, I>::remove(&class, &instance);
		Account::<T, I>::remove((&owner, &class, &instance));

		Self::deposit_event(Event::Burned(class, instance, owner));
		Ok(())
	}
}
