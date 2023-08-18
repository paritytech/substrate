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

//! This module contains helper methods to configure attributes for items and collections in the
//! NFTs pallet.
//! The bitflag [`PalletFeature::Attributes`] needs to be set in [`Config::Features`] for NFTs
//! to have the functionality defined in this module.

use crate::*;
use frame_support::pallet_prelude::*;

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Sets the attribute of an item or a collection.
	///
	/// This function is used to set an attribute for an item or a collection. It checks the
	/// provided `namespace` and verifies the permission of the caller to perform the action. The
	/// `collection` and `maybe_item` parameters specify the target for the attribute.
	///
	/// - `origin`: The account attempting to set the attribute.
	/// - `collection`: The identifier of the collection to which the item belongs, or the
	///   collection itself if setting a collection attribute.
	/// - `maybe_item`: The identifier of the item to which the attribute belongs, or `None` if
	///   setting a collection attribute.
	/// - `namespace`: The namespace in which the attribute is being set. It can be either
	///   `CollectionOwner`, `ItemOwner`, or `Account` (pre-approved external address).
	/// - `key`: The key of the attribute. It should be a vector of bytes within the limits defined
	///   by `T::KeyLimit`.
	/// - `value`: The value of the attribute. It should be a vector of bytes within the limits
	///   defined by `T::ValueLimit`.
	/// - `depositor`: The account that is paying the deposit for the attribute.
	///
	/// Note: For the `CollectionOwner` namespace, the collection/item must have the
	/// `UnlockedAttributes` setting enabled.
	/// The deposit for setting an attribute is based on the `T::DepositPerByte` and
	/// `T::AttributeDepositBase` configuration.
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

		ensure!(
			Self::is_valid_namespace(&origin, &namespace, &collection, &maybe_item)?,
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

		let mut collection_details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;

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

	/// Sets the attribute of an item or a collection without performing deposit checks.
	///
	/// This function is used to force-set an attribute for an item or a collection without
	/// performing the deposit checks. It bypasses the deposit requirement and should only be used
	/// in specific situations where deposit checks are not necessary or handled separately.
	///
	/// - `set_as`: The account that would normally pay for the deposit.
	/// - `collection`: The identifier of the collection to which the item belongs, or the
	///   collection itself if setting a collection attribute.
	/// - `maybe_item`: The identifier of the item to which the attribute belongs, or `None` if
	///   setting a collection attribute.
	/// - `namespace`: The namespace in which the attribute is being set. It can be either
	///   `CollectionOwner`, `ItemOwner`, or `Account` (pre-approved external address).
	/// - `key`: The key of the attribute. It should be a vector of bytes within the limits defined
	///   by `T::KeyLimit`.
	/// - `value`: The value of the attribute. It should be a vector of bytes within the limits
	///   defined by `T::ValueLimit`.
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

	/// Sets multiple attributes for an item or a collection.
	///
	/// This function checks the pre-signed data is valid and updates the attributes of an item or
	/// collection. It is limited by [`Config::MaxAttributesPerCall`] to prevent excessive storage
	/// consumption in a single transaction.
	///
	/// - `origin`: The account initiating the transaction.
	/// - `data`: The data containing the details of the pre-signed attributes to be set.
	/// - `signer`: The account of the pre-signed attributes signer.
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

	/// Clears an attribute of an item or a collection.
	///
	/// This function allows clearing an attribute from an item or a collection. It verifies the
	/// permission of the caller to perform the action based on the provided `namespace` and
	/// `depositor` account. The deposit associated with the attribute, if any, will be unreserved.
	///
	/// - `maybe_check_origin`: An optional account that acts as an additional security check when
	/// clearing the attribute. This can be `None` if no additional check is required.
	/// - `collection`: The identifier of the collection to which the item belongs, or the
	///   collection itself if clearing a collection attribute.
	/// - `maybe_item`: The identifier of the item to which the attribute belongs, or `None` if
	///   clearing a collection attribute.
	/// - `namespace`: The namespace in which the attribute is being cleared. It can be either
	///   `CollectionOwner`, `ItemOwner`, or `Account`.
	/// - `key`: The key of the attribute to be cleared. It should be a vector of bytes within the
	///   limits defined by `T::KeyLimit`.
	pub(crate) fn do_clear_attribute(
		maybe_check_origin: Option<T::AccountId>,
		collection: T::CollectionId,
		maybe_item: Option<T::ItemId>,
		namespace: AttributeNamespace<T::AccountId>,
		key: BoundedVec<u8, T::KeyLimit>,
	) -> DispatchResult {
		let (_, deposit) = Attribute::<T, I>::take((collection, maybe_item, &namespace, &key))
			.ok_or(Error::<T, I>::AttributeNotFound)?;

		if let Some(check_origin) = &maybe_check_origin {
			// validate the provided namespace when it's not a root call and the caller is not
			// the same as the `deposit.account` (e.g. the deposit was paid by different account)
			if deposit.account != maybe_check_origin {
				ensure!(
					Self::is_valid_namespace(&check_origin, &namespace, &collection, &maybe_item)?,
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
						if let Some(is_locked) = maybe_is_locked {
							ensure!(!is_locked, Error::<T, I>::LockedItemAttributes);
							// Only the collection's admin can clear attributes in that namespace.
							// e.g. in off-chain mints, the attribute's depositor will be the item's
							// owner, that's why we need to do this extra check.
							ensure!(
								Self::has_role(&collection, &check_origin, CollectionRole::Admin),
								Error::<T, I>::NoPermission
							);
						}
					},
				},
				_ => (),
			};
		}

		let mut collection_details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;

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

	/// Approves a delegate to set attributes on behalf of the item's owner.
	///
	/// This function allows the owner of an item to approve a delegate to set attributes in the
	/// `Account(delegate)` namespace. The maximum number of approvals is determined by
	/// the configuration `T::MaxAttributesApprovals`.
	///
	/// - `check_origin`: The account of the item's owner attempting to approve the delegate.
	/// - `collection`: The identifier of the collection to which the item belongs.
	/// - `item`: The identifier of the item for which the delegate is being approved.
	/// - `delegate`: The account that is being approved to set attributes on behalf of the item's
	///   owner.
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

	/// Cancels the approval of an item's attributes by a delegate.
	///
	/// This function allows the owner of an item to cancel the approval of a delegate to set
	/// attributes in the `Account(delegate)` namespace. The delegate's approval is removed, in
	/// addition to attributes the `delegate` previously created, and any unreserved deposit
	/// is returned. The number of attributes that the delegate has set for the item must
	/// not exceed the `account_attributes` provided in the `witness`.
	/// This function is used to prevent unintended or malicious cancellations.
	///
	/// - `check_origin`: The account of the item's owner attempting to cancel the delegate's
	///   approval.
	/// - `collection`: The identifier of the collection to which the item belongs.
	/// - `item`: The identifier of the item for which the delegate's approval is being canceled.
	/// - `delegate`: The account whose approval is being canceled.
	/// - `witness`: The witness containing the number of attributes set by the delegate for the
	///   item.
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

	/// A helper method to check whether an attribute namespace is valid.
	fn is_valid_namespace(
		origin: &T::AccountId,
		namespace: &AttributeNamespace<T::AccountId>,
		collection: &T::CollectionId,
		maybe_item: &Option<T::ItemId>,
	) -> Result<bool, DispatchError> {
		let mut result = false;
		match namespace {
			AttributeNamespace::CollectionOwner =>
				result = Self::has_role(&collection, &origin, CollectionRole::Admin),
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

	/// A helper method to construct an attribute's key.
	///
	/// # Errors
	///
	/// This function returns an [`IncorrectData`](crate::Error::IncorrectData) error if the
	/// provided attribute `key` is too long.
	pub fn construct_attribute_key(
		key: Vec<u8>,
	) -> Result<BoundedVec<u8, T::KeyLimit>, DispatchError> {
		Ok(BoundedVec::try_from(key).map_err(|_| Error::<T, I>::IncorrectData)?)
	}

	/// A helper method to construct an attribute's value.
	///
	/// # Errors
	///
	/// This function returns an [`IncorrectData`](crate::Error::IncorrectData) error if the
	/// provided `value` is too long.
	pub fn construct_attribute_value(
		value: Vec<u8>,
	) -> Result<BoundedVec<u8, T::ValueLimit>, DispatchError> {
		Ok(BoundedVec::try_from(value).map_err(|_| Error::<T, I>::IncorrectData)?)
	}

	/// A helper method to check whether a system attribute is set for a given item.
	///
	/// # Errors
	///
	/// This function returns an [`IncorrectData`](crate::Error::IncorrectData) error if the
	/// provided pallet attribute is too long.
	pub fn has_system_attribute(
		collection: &T::CollectionId,
		item: &T::ItemId,
		attribute_key: PalletAttributes<T::CollectionId>,
	) -> Result<bool, DispatchError> {
		let attribute = (
			&collection,
			Some(item),
			AttributeNamespace::Pallet,
			&Self::construct_attribute_key(attribute_key.encode())?,
		);
		Ok(Attribute::<T, I>::contains_key(attribute))
	}
}
