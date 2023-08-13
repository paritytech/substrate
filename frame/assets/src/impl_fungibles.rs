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

//! Implementations for fungibles trait.

use frame_support::{
	defensive,
	traits::tokens::{
		Fortitude,
		Precision::{self, BestEffort},
		Preservation::{self, Expendable},
		Provenance::{self, Minted},
	},
};

use super::*;

impl<T: Config<I>, I: 'static> fungibles::Inspect<<T as SystemConfig>::AccountId> for Pallet<T, I> {
	type AssetId = T::AssetId;
	type Balance = T::Balance;

	fn total_issuance(asset: Self::AssetId) -> Self::Balance {
		Asset::<T, I>::get(asset).map(|x| x.supply).unwrap_or_else(Zero::zero)
	}

	fn minimum_balance(asset: Self::AssetId) -> Self::Balance {
		Asset::<T, I>::get(asset).map(|x| x.min_balance).unwrap_or_else(Zero::zero)
	}

	fn balance(asset: Self::AssetId, who: &<T as SystemConfig>::AccountId) -> Self::Balance {
		Pallet::<T, I>::balance(asset, who)
	}

	fn total_balance(asset: Self::AssetId, who: &<T as SystemConfig>::AccountId) -> Self::Balance {
		Pallet::<T, I>::balance(asset, who)
	}

	fn reducible_balance(
		asset: Self::AssetId,
		who: &<T as SystemConfig>::AccountId,
		preservation: Preservation,
		_: Fortitude,
	) -> Self::Balance {
		Pallet::<T, I>::reducible_balance(asset, who, !matches!(preservation, Expendable))
			.unwrap_or(Zero::zero())
	}

	fn can_deposit(
		asset: Self::AssetId,
		who: &<T as SystemConfig>::AccountId,
		amount: Self::Balance,
		provenance: Provenance,
	) -> DepositConsequence {
		Pallet::<T, I>::can_increase(asset, who, amount, provenance == Minted)
	}

	fn can_withdraw(
		asset: Self::AssetId,
		who: &<T as SystemConfig>::AccountId,
		amount: Self::Balance,
	) -> WithdrawConsequence<Self::Balance> {
		Pallet::<T, I>::can_decrease(asset, who, amount, false)
	}

	fn asset_exists(asset: Self::AssetId) -> bool {
		Asset::<T, I>::contains_key(asset)
	}
}

impl<T: Config<I>, I: 'static> fungibles::Mutate<<T as SystemConfig>::AccountId> for Pallet<T, I> {
	fn done_mint_into(
		asset_id: Self::AssetId,
		beneficiary: &<T as SystemConfig>::AccountId,
		amount: Self::Balance,
	) {
		Self::deposit_event(Event::Issued { asset_id, owner: beneficiary.clone(), amount })
	}

	fn done_burn_from(
		asset_id: Self::AssetId,
		target: &<T as SystemConfig>::AccountId,
		balance: Self::Balance,
	) {
		Self::deposit_event(Event::Burned { asset_id, owner: target.clone(), balance });
	}

	fn done_transfer(
		asset_id: Self::AssetId,
		source: &<T as SystemConfig>::AccountId,
		dest: &<T as SystemConfig>::AccountId,
		amount: Self::Balance,
	) {
		Self::deposit_event(Event::Transferred {
			asset_id,
			from: source.clone(),
			to: dest.clone(),
			amount,
		});
	}
}

impl<T: Config<I>, I: 'static> fungibles::Balanced<<T as SystemConfig>::AccountId>
	for Pallet<T, I>
{
	type OnDropCredit = fungibles::DecreaseIssuance<T::AccountId, Self>;
	type OnDropDebt = fungibles::IncreaseIssuance<T::AccountId, Self>;
}

impl<T: Config<I>, I: 'static> fungibles::Unbalanced<T::AccountId> for Pallet<T, I> {
	fn handle_raw_dust(_: Self::AssetId, _: Self::Balance) {}
	fn handle_dust(_: fungibles::Dust<T::AccountId, Self>) {
		defensive!("`decrease_balance` and `increase_balance` have non-default impls; nothing else calls this; qed");
	}
	fn write_balance(
		_: Self::AssetId,
		_: &T::AccountId,
		_: Self::Balance,
	) -> Result<Option<Self::Balance>, DispatchError> {
		defensive!("write_balance is not used if other functions are impl'd");
		Err(DispatchError::Unavailable)
	}
	fn set_total_issuance(id: T::AssetId, amount: Self::Balance) {
		Asset::<T, I>::mutate_exists(id, |maybe_asset| {
			if let Some(ref mut asset) = maybe_asset {
				asset.supply = amount
			}
		});
	}
	fn decrease_balance(
		asset: T::AssetId,
		who: &T::AccountId,
		amount: Self::Balance,
		precision: Precision,
		preservation: Preservation,
		_: Fortitude,
	) -> Result<Self::Balance, DispatchError> {
		let f = DebitFlags {
			keep_alive: preservation != Expendable,
			best_effort: precision == BestEffort,
		};
		Self::decrease_balance(asset, who, amount, f, |_, _| Ok(()))
	}
	fn increase_balance(
		asset: T::AssetId,
		who: &T::AccountId,
		amount: Self::Balance,
		_: Precision,
	) -> Result<Self::Balance, DispatchError> {
		Self::increase_balance(asset, who, amount, |_| Ok(()))?;
		Ok(amount)
	}

	// TODO: #13196 implement deactivate/reactivate once we have inactive balance tracking.
}

impl<T: Config<I>, I: 'static> fungibles::Create<T::AccountId> for Pallet<T, I> {
	fn create(
		id: T::AssetId,
		admin: T::AccountId,
		is_sufficient: bool,
		min_balance: Self::Balance,
	) -> DispatchResult {
		Self::do_force_create(id, admin, is_sufficient, min_balance)
	}
}

impl<T: Config<I>, I: 'static> fungibles::Destroy<T::AccountId> for Pallet<T, I> {
	fn start_destroy(id: T::AssetId, maybe_check_owner: Option<T::AccountId>) -> DispatchResult {
		Self::do_start_destroy(id, maybe_check_owner)
	}

	fn destroy_accounts(id: T::AssetId, max_items: u32) -> Result<u32, DispatchError> {
		Self::do_destroy_accounts(id, max_items)
	}

	fn destroy_approvals(id: T::AssetId, max_items: u32) -> Result<u32, DispatchError> {
		Self::do_destroy_approvals(id, max_items)
	}

	fn finish_destroy(id: T::AssetId) -> DispatchResult {
		Self::do_finish_destroy(id)
	}
}

impl<T: Config<I>, I: 'static> fungibles::metadata::Inspect<<T as SystemConfig>::AccountId>
	for Pallet<T, I>
{
	fn name(asset: T::AssetId) -> Vec<u8> {
		Metadata::<T, I>::get(asset).name.to_vec()
	}

	fn symbol(asset: T::AssetId) -> Vec<u8> {
		Metadata::<T, I>::get(asset).symbol.to_vec()
	}

	fn decimals(asset: T::AssetId) -> u8 {
		Metadata::<T, I>::get(asset).decimals
	}
}

impl<T: Config<I>, I: 'static> fungibles::metadata::Mutate<<T as SystemConfig>::AccountId>
	for Pallet<T, I>
{
	fn set(
		asset: T::AssetId,
		from: &<T as SystemConfig>::AccountId,
		name: Vec<u8>,
		symbol: Vec<u8>,
		decimals: u8,
	) -> DispatchResult {
		Self::do_set_metadata(asset, from, name, symbol, decimals)
	}
}

impl<T: Config<I>, I: 'static>
	fungibles::metadata::MetadataDeposit<
		<T::Currency as Currency<<T as SystemConfig>::AccountId>>::Balance,
	> for Pallet<T, I>
{
	fn calc_metadata_deposit(
		name: &[u8],
		symbol: &[u8],
	) -> <T::Currency as Currency<<T as SystemConfig>::AccountId>>::Balance {
		Self::calc_metadata_deposit(&name, &symbol)
	}
}

impl<T: Config<I>, I: 'static> fungibles::approvals::Inspect<<T as SystemConfig>::AccountId>
	for Pallet<T, I>
{
	// Check the amount approved to be spent by an owner to a delegate
	fn allowance(
		asset: T::AssetId,
		owner: &<T as SystemConfig>::AccountId,
		delegate: &<T as SystemConfig>::AccountId,
	) -> T::Balance {
		Approvals::<T, I>::get((asset, &owner, &delegate))
			.map(|x| x.amount)
			.unwrap_or_else(Zero::zero)
	}
}

impl<T: Config<I>, I: 'static> fungibles::approvals::Mutate<<T as SystemConfig>::AccountId>
	for Pallet<T, I>
{
	// Approve spending tokens from a given account
	fn approve(
		asset: T::AssetId,
		owner: &<T as SystemConfig>::AccountId,
		delegate: &<T as SystemConfig>::AccountId,
		amount: T::Balance,
	) -> DispatchResult {
		Self::do_approve_transfer(asset, owner, delegate, amount)
	}

	fn transfer_from(
		asset: T::AssetId,
		owner: &<T as SystemConfig>::AccountId,
		delegate: &<T as SystemConfig>::AccountId,
		dest: &<T as SystemConfig>::AccountId,
		amount: T::Balance,
	) -> DispatchResult {
		Self::do_transfer_approved(asset, owner, delegate, dest, amount)
	}
}

impl<T: Config<I>, I: 'static> fungibles::roles::Inspect<<T as SystemConfig>::AccountId>
	for Pallet<T, I>
{
	fn owner(asset: T::AssetId) -> Option<<T as SystemConfig>::AccountId> {
		Asset::<T, I>::get(asset).map(|x| x.owner)
	}

	fn issuer(asset: T::AssetId) -> Option<<T as SystemConfig>::AccountId> {
		Asset::<T, I>::get(asset).map(|x| x.issuer)
	}

	fn admin(asset: T::AssetId) -> Option<<T as SystemConfig>::AccountId> {
		Asset::<T, I>::get(asset).map(|x| x.admin)
	}

	fn freezer(asset: T::AssetId) -> Option<<T as SystemConfig>::AccountId> {
		Asset::<T, I>::get(asset).map(|x| x.freezer)
	}
}

impl<T: Config<I>, I: 'static> fungibles::InspectEnumerable<T::AccountId> for Pallet<T, I> {
	type AssetsIterator = KeyPrefixIterator<<T as Config<I>>::AssetId>;

	/// Returns an iterator of the assets in existence.
	///
	/// NOTE: iterating this list invokes a storage read per item.
	fn asset_ids() -> Self::AssetsIterator {
		Asset::<T, I>::iter_keys()
	}
}
