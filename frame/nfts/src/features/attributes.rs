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

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	pub(crate) fn do_set_attribute(
		origin: T::AccountId,
		collection: T::CollectionId,
		maybe_item: Option<T::ItemId>,
		namespace: AttributeNamespace<T::AccountId>,
		key: BoundedVec<u8, T::KeyLimit>,
		value: BoundedVec<u8, T::ValueLimit>,
		depositor: T::AccountId,
	) -> DispatchResult {
		ensure!(
			Self::is_pallet_feature_enabled(PalletFeature::Attributes),
			Error::<T, I>::MethodDisabled
		);

		let mut collection_details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;

		ensure!(
			Self::is_valid_namespace(
				&origin,
				&namespace,
				&collection,
				&collection_details.owner,
				&maybe_item,
			)?,
			Error::<T, I>::NoPermission
		);

		let collection_config = Self::get_collection_config(&collection)?;
		// for the `CollectionOwner` namespace we need to check if the collection/item is not locked
		match namespace {
			AttributeNamespace::CollectionOwner => match maybe_item {
				None => {
					ensure!(
						collection_config.is_setting_enabled(CollectionSetting::UnlockedAttributes),
						Error::<T, I>::LockedCollectionAttributes
					)
				},
				Some(item) => {
					let maybe_is_locked = Self::get_item_config(&collection, &item)
						.map(|c| c.has_disabled_setting(ItemSetting::UnlockedAttributes))?;
					ensure!(!maybe_is_locked, Error::<T, I>::LockedItemAttributes);
				},
			},
			_ => (),
		}

		let attribute = Attribute::<T, I>::get((collection, maybe_item, &namespace, &key));
		let attribute_exists = attribute.is_some();
		if !attribute_exists {
			collection_details.attributes.saturating_inc();
		}

		let old_deposit =
			attribute.map_or(AttributeDeposit { account: None, amount: Zero::zero() }, |m| m.1);

		let mut deposit = Zero::zero();
		// disabled DepositRequired setting only affects the CollectionOwner namespace
		if collection_config.is_setting_enabled(CollectionSetting::DepositRequired) ||
			namespace != AttributeNamespace::CollectionOwner
		{
			deposit = T::DepositPerByte::get()
				.saturating_mul(((key.len() + value.len()) as u32).into())
				.saturating_add(T::AttributeDepositBase::get());
		}

		let is_collection_owner_namespace = namespace == AttributeNamespace::CollectionOwner;
		let is_depositor_collection_owner =
			is_collection_owner_namespace && collection_details.owner == depositor;

		// NOTE: in the CollectionOwner namespace if the depositor is `None` that means the deposit
		// was paid by the collection's owner.
		let old_depositor =
			if is_collection_owner_namespace && old_deposit.account.is_none() && attribute_exists {
				Some(collection_details.owner.clone())
			} else {
				old_deposit.account
			};
		let depositor_has_changed = old_depositor != Some(depositor.clone());

		// NOTE: when we transfer an item, we don't move attributes in the ItemOwner namespace.
		// When the new owner updates the same attribute, we will update the depositor record
		// and return the deposit to the previous owner.
		if depositor_has_changed {
			if let Some(old_depositor) = old_depositor {
				T::Currency::unreserve(&old_depositor, old_deposit.amount);
			}
			T::Currency::reserve(&depositor, deposit)?;
		} else if deposit > old_deposit.amount {
			T::Currency::reserve(&depositor, deposit - old_deposit.amount)?;
		} else if deposit < old_deposit.amount {
			T::Currency::unreserve(&depositor, old_deposit.amount - deposit);
		}

		if is_depositor_collection_owner {
			if !depositor_has_changed {
				collection_details.owner_deposit.saturating_reduce(old_deposit.amount);
			}
			collection_details.owner_deposit.saturating_accrue(deposit);
		}

		let new_deposit_owner = match is_depositor_collection_owner {
			true => None,
			false => Some(depositor),
		};
		Attribute::<T, I>::insert(
			(&collection, maybe_item, &namespace, &key),
			(&value, AttributeDeposit { account: new_deposit_owner, amount: deposit }),
		);

		Collection::<T, I>::insert(collection, &collection_details);
		Self::deposit_event(Event::AttributeSet { collection, maybe_item, key, value, namespace });
		Ok(())
	}

	pub(crate) fn do_force_set_attribute(
		set_as: Option<T::AccountId>,
		collection: T::CollectionId,
		maybe_item: Option<T::ItemId>,
		namespace: AttributeNamespace<T::AccountId>,
		key: BoundedVec<u8, T::KeyLimit>,
		value: BoundedVec<u8, T::ValueLimit>,
	) -> DispatchResult {
		let mut collection_details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;

		let attribute = Attribute::<T, I>::get((collection, maybe_item, &namespace, &key));
		if let Some((_, deposit)) = attribute {
			if deposit.account != set_as && deposit.amount != Zero::zero() {
				if let Some(deposit_account) = deposit.account {
					T::Currency::unreserve(&deposit_account, deposit.amount);
				}
			}
		} else {
			collection_details.attributes.saturating_inc();
		}

		Attribute::<T, I>::insert(
			(&collection, maybe_item, &namespace, &key),
			(&value, AttributeDeposit { account: set_as, amount: Zero::zero() }),
		);
		Collection::<T, I>::insert(collection, &collection_details);
		Self::deposit_event(Event::AttributeSet { collection, maybe_item, key, value, namespace });
		Ok(())
	}

	pub(crate) fn do_set_attributes_pre_signed(
		origin: T::AccountId,
		data: PreSignedAttributesOf<T, I>,
		signer: T::AccountId,
	) -> DispatchResult {
		let PreSignedAttributes { collection, item, attributes, namespace, deadline } = data;

		ensure!(
			attributes.len() <= T::MaxAttributesPerCall::get() as usize,
			Error::<T, I>::MaxAttributesLimitReached
		);

		let now = frame_system::Pallet::<T>::block_number();
		ensure!(deadline >= now, Error::<T, I>::DeadlineExpired);

		let item_details =
			Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownItem)?;
		ensure!(item_details.owner == origin, Error::<T, I>::NoPermission);

		// Only the CollectionOwner and Account() namespaces could be updated in this way.
		// For the Account() namespace we check and set the approval if it wasn't set before.
		match &namespace {
			AttributeNamespace::CollectionOwner => {},
			AttributeNamespace::Account(account) => {
				ensure!(account == &signer, Error::<T, I>::NoPermission);
				let approvals = ItemAttributesApprovalsOf::<T, I>::get(&collection, &item);
				if !approvals.contains(account) {
					Self::do_approve_item_attributes(
						origin.clone(),
						collection,
						item,
						account.clone(),
					)?;
				}
			},
			_ => return Err(Error::<T, I>::WrongNamespace.into()),
		}

		for (key, value) in attributes {
			Self::do_set_attribute(
				signer.clone(),
				collection,
				Some(item),
				namespace.clone(),
				Self::construct_attribute_key(key)?,
				Self::construct_attribute_value(value)?,
				origin.clone(),
			)?;
		}
		Self::deposit_event(Event::PreSignedAttributesSet { collection, item, namespace });
		Ok(())
	}

	pub(crate) fn do_clear_attribute(
		maybe_check_owner: Option<T::AccountId>,
		collection: T::CollectionId,
		maybe_item: Option<T::ItemId>,
		namespace: AttributeNamespace<T::AccountId>,
		key: BoundedVec<u8, T::KeyLimit>,
	) -> DispatchResult {
		let (_, deposit) = Attribute::<T, I>::take((collection, maybe_item, &namespace, &key))
			.ok_or(Error::<T, I>::AttributeNotFound)?;
		let mut collection_details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;

		if let Some(check_owner) = &maybe_check_owner {
			// validate the provided namespace when it's not a root call and the caller is not
			// the same as the `deposit.account` (e.g. the deposit was paid by different account)
			if deposit.account != maybe_check_owner {
				ensure!(
					Self::is_valid_namespace(
						&check_owner,
						&namespace,
						&collection,
						&collection_details.owner,
						&maybe_item,
					)?,
					Error::<T, I>::NoPermission
				);
			}

			// can't clear `CollectionOwner` type attributes if the collection/item is locked
			match namespace {
				AttributeNamespace::CollectionOwner => match maybe_item {
					None => {
						let collection_config = Self::get_collection_config(&collection)?;
						ensure!(
							collection_config
								.is_setting_enabled(CollectionSetting::UnlockedAttributes),
							Error::<T, I>::LockedCollectionAttributes
						)
					},
					Some(item) => {
						// NOTE: if the item was previously burned, the ItemConfigOf record
						// might not exist. In that case, we allow to clear the attribute.
						let maybe_is_locked = Self::get_item_config(&collection, &item)
							.map_or(None, |c| {
								Some(c.has_disabled_setting(ItemSetting::UnlockedAttributes))
							});
						match maybe_is_locked {
							Some(is_locked) => {
								// when item exists, then only the collection's owner can clear that
								// attribute
								ensure!(
									check_owner == &collection_details.owner,
									Error::<T, I>::NoPermission
								);
								ensure!(!is_locked, Error::<T, I>::LockedItemAttributes);
							},
							None => (),
						}
					},
				},
				_ => (),
			};
		}

		collection_details.attributes.saturating_dec();

		match deposit.account {
			Some(deposit_account) => {
				T::Currency::unreserve(&deposit_account, deposit.amount);
			},
			None if namespace == AttributeNamespace::CollectionOwner => {
				collection_details.owner_deposit.saturating_reduce(deposit.amount);
				T::Currency::unreserve(&collection_details.owner, deposit.amount);
			},
			_ => (),
		}

		Collection::<T, I>::insert(collection, &collection_details);
		Self::deposit_event(Event::AttributeCleared { collection, maybe_item, key, namespace });

		Ok(())
	}

	pub(crate) fn do_approve_item_attributes(
		check_origin: T::AccountId,
		collection: T::CollectionId,
		item: T::ItemId,
		delegate: T::AccountId,
	) -> DispatchResult {
		ensure!(
			Self::is_pallet_feature_enabled(PalletFeature::Attributes),
			Error::<T, I>::MethodDisabled
		);

		let details = Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownItem)?;
		ensure!(check_origin == details.owner, Error::<T, I>::NoPermission);

		ItemAttributesApprovalsOf::<T, I>::try_mutate(collection, item, |approvals| {
			approvals
				.try_insert(delegate.clone())
				.map_err(|_| Error::<T, I>::ReachedApprovalLimit)?;

			Self::deposit_event(Event::ItemAttributesApprovalAdded { collection, item, delegate });
			Ok(())
		})
	}

	pub(crate) fn do_cancel_item_attributes_approval(
		check_origin: T::AccountId,
		collection: T::CollectionId,
		item: T::ItemId,
		delegate: T::AccountId,
		witness: CancelAttributesApprovalWitness,
	) -> DispatchResult {
		ensure!(
			Self::is_pallet_feature_enabled(PalletFeature::Attributes),
			Error::<T, I>::MethodDisabled
		);

		let details = Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownItem)?;
		ensure!(check_origin == details.owner, Error::<T, I>::NoPermission);

		ItemAttributesApprovalsOf::<T, I>::try_mutate(collection, item, |approvals| {
			approvals.remove(&delegate);

			let mut attributes: u32 = 0;
			let mut deposited: DepositBalanceOf<T, I> = Zero::zero();
			for (_, (_, deposit)) in Attribute::<T, I>::drain_prefix((
				&collection,
				Some(item),
				AttributeNamespace::Account(delegate.clone()),
			)) {
				attributes.saturating_inc();
				deposited = deposited.saturating_add(deposit.amount);
			}
			ensure!(attributes <= witness.account_attributes, Error::<T, I>::BadWitness);

			if !deposited.is_zero() {
				T::Currency::unreserve(&delegate, deposited);
			}

			Self::deposit_event(Event::ItemAttributesApprovalRemoved {
				collection,
				item,
				delegate,
			});
			Ok(())
		})
	}

	fn is_valid_namespace(
		origin: &T::AccountId,
		namespace: &AttributeNamespace<T::AccountId>,
		collection: &T::CollectionId,
		collection_owner: &T::AccountId,
		maybe_item: &Option<T::ItemId>,
	) -> Result<bool, DispatchError> {
		let mut result = false;
		match namespace {
			AttributeNamespace::CollectionOwner => result = origin == collection_owner,
			AttributeNamespace::ItemOwner =>
				if let Some(item) = maybe_item {
					let item_details =
						Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownItem)?;
					result = origin == &item_details.owner
				},
			AttributeNamespace::Account(account_id) =>
				if let Some(item) = maybe_item {
					let approvals = ItemAttributesApprovalsOf::<T, I>::get(&collection, &item);
					result = account_id == origin && approvals.contains(&origin)
				},
			_ => (),
		};
		Ok(result)
	}

	/// A helper method to construct attribute's key.
	pub fn construct_attribute_key(
		key: Vec<u8>,
	) -> Result<BoundedVec<u8, T::KeyLimit>, DispatchError> {
		Ok(BoundedVec::try_from(key).map_err(|_| Error::<T, I>::IncorrectData)?)
	}

	/// A helper method to construct attribute's value.
	pub fn construct_attribute_value(
		value: Vec<u8>,
	) -> Result<BoundedVec<u8, T::ValueLimit>, DispatchError> {
		Ok(BoundedVec::try_from(value).map_err(|_| Error::<T, I>::IncorrectData)?)
	}
}
