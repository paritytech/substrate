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

//! Various basic types for use in the assets pallet.

use super::*;
use frame_support::{
	pallet_prelude::*,
	traits::{fungible, tokens::ConversionToAssetBalance},
};
use sp_runtime::{traits::Convert, FixedPointNumber, FixedPointOperand, FixedU128};

pub(super) type DepositBalanceOf<T, I = ()> =
	<<T as Config<I>>::Currency as Currency<<T as SystemConfig>::AccountId>>::Balance;
pub(super) type AssetAccountOf<T, I> =
	AssetAccount<<T as Config<I>>::Balance, DepositBalanceOf<T, I>, <T as Config<I>>::Extra>;

/// AssetStatus holds the current state of the asset. It could either be Live and available for use,
/// or in a Destroying state.
#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, MaxEncodedLen, TypeInfo)]
pub(super) enum AssetStatus {
	/// The asset is active and able to be used.
	Live,
	/// Whether the asset is frozen for non-admin transfers.
	Frozen,
	/// The asset is currently being destroyed, and all actions are no longer permitted on the
	/// asset. Once set to `Destroying`, the asset can never transition back to a `Live` state.
	Destroying,
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, MaxEncodedLen, TypeInfo)]
pub struct AssetDetails<Balance, AccountId, DepositBalance> {
	/// Can change `owner`, `issuer`, `freezer` and `admin` accounts.
	pub(super) owner: AccountId,
	/// Can mint tokens.
	pub(super) issuer: AccountId,
	/// Can thaw tokens, force transfers and burn tokens from any account.
	pub(super) admin: AccountId,
	/// Can freeze tokens.
	pub(super) freezer: AccountId,
	/// The total supply across all accounts.
	pub(super) supply: Balance,
	/// The balance deposited for this asset. This pays for the data stored here.
	pub(super) deposit: DepositBalance,
	/// The ED for virtual accounts.
	pub(super) min_balance: Balance,
	/// If `true`, then any account with this asset is given a provider reference. Otherwise, it
	/// requires a consumer reference.
	pub(super) is_sufficient: bool,
	/// The total number of accounts.
	pub(super) accounts: u32,
	/// The total number of accounts for which we have placed a self-sufficient reference.
	pub(super) sufficients: u32,
	/// The total number of approvals.
	pub(super) approvals: u32,
	/// The status of the asset
	pub(super) status: AssetStatus,
}

/// Data concerning an approval.
#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default, MaxEncodedLen, TypeInfo)]
pub struct Approval<Balance, DepositBalance> {
	/// The amount of funds approved for the balance transfer from the owner to some delegated
	/// target.
	pub(super) amount: Balance,
	/// The amount reserved on the owner's account to hold this item in storage.
	pub(super) deposit: DepositBalance,
}

#[test]
fn ensure_bool_decodes_to_consumer_or_sufficient() {
	assert_eq!(false.encode(), ExistenceReason::<()>::Consumer.encode());
	assert_eq!(true.encode(), ExistenceReason::<()>::Sufficient.encode());
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, MaxEncodedLen, TypeInfo)]
pub enum ExistenceReason<Balance> {
	#[codec(index = 0)]
	Consumer,
	#[codec(index = 1)]
	Sufficient,
	#[codec(index = 2)]
	DepositHeld(Balance),
	#[codec(index = 3)]
	DepositRefunded,
}

impl<Balance> ExistenceReason<Balance> {
	pub(crate) fn take_deposit(&mut self) -> Option<Balance> {
		if !matches!(self, ExistenceReason::DepositHeld(_)) {
			return None
		}
		if let ExistenceReason::DepositHeld(deposit) =
			sp_std::mem::replace(self, ExistenceReason::DepositRefunded)
		{
			Some(deposit)
		} else {
			None
		}
	}
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, MaxEncodedLen, TypeInfo)]
pub struct AssetAccount<Balance, DepositBalance, Extra> {
	/// The balance.
	pub(super) balance: Balance,
	/// Whether the account is frozen.
	pub(super) is_frozen: bool,
	/// The reason for the existence of the account.
	pub(super) reason: ExistenceReason<DepositBalance>,
	/// Additional "sidecar" data, in case some other pallet wants to use this storage item.
	pub(super) extra: Extra,
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, Default, RuntimeDebug, MaxEncodedLen, TypeInfo)]
pub struct AssetMetadata<DepositBalance, BoundedString> {
	/// The balance deposited for this metadata.
	///
	/// This pays for the data stored in this struct.
	pub(super) deposit: DepositBalance,
	/// The user friendly name of this asset. Limited in length by `StringLimit`.
	pub(super) name: BoundedString,
	/// The ticker symbol for this asset. Limited in length by `StringLimit`.
	pub(super) symbol: BoundedString,
	/// The number of decimals this asset uses to represent one unit.
	pub(super) decimals: u8,
	/// Whether the asset metadata may be changed by a non Force origin.
	pub(super) is_frozen: bool,
}

/// Trait for allowing a minimum balance on the account to be specified, beyond the
/// `minimum_balance` of the asset. This is additive - the `minimum_balance` of the asset must be
/// met *and then* anything here in addition.
pub trait FrozenBalance<AssetId, AccountId, Balance> {
	/// Return the frozen balance.
	///
	/// Generally, the balance of every account must be at least the sum of this (if `Some`) and
	/// the asset's `minimum_balance` (the latter since there may be complications to destroying an
	/// asset's account completely).
	///
	/// Under normal behaviour, the account balance should not go below the sum of this (if `Some`)
	/// and the asset's minimum balance. However, the account balance may reasonably begin below
	/// this sum (e.g. if less than the sum had ever been transferred into the account).
	///
	/// In special cases (privileged intervention) the account balance may also go below the sum.
	///
	/// If `None` is returned, then nothing special is enforced.
	fn frozen_balance(asset: AssetId, who: &AccountId) -> Option<Balance>;

	/// Called after an account has been removed.
	///
	/// NOTE: It is possible that the asset does no longer exist when this hook is called.
	fn died(asset: AssetId, who: &AccountId);
}

impl<AssetId, AccountId, Balance> FrozenBalance<AssetId, AccountId, Balance> for () {
	fn frozen_balance(_: AssetId, _: &AccountId) -> Option<Balance> {
		None
	}
	fn died(_: AssetId, _: &AccountId) {}
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub(super) struct TransferFlags {
	/// The debited account must stay alive at the end of the operation; an error is returned if
	/// this cannot be achieved legally.
	pub(super) keep_alive: bool,
	/// Less than the amount specified needs be debited by the operation for it to be considered
	/// successful. If `false`, then the amount debited will always be at least the amount
	/// specified.
	pub(super) best_effort: bool,
	/// Any additional funds debited (due to minimum balance requirements) should be burned rather
	/// than credited to the destination account.
	pub(super) burn_dust: bool,
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub(super) struct DebitFlags {
	/// The debited account must stay alive at the end of the operation; an error is returned if
	/// this cannot be achieved legally.
	pub(super) keep_alive: bool,
	/// Less than the amount specified needs be debited by the operation for it to be considered
	/// successful. If `false`, then the amount debited will always be at least the amount
	/// specified.
	pub(super) best_effort: bool,
}

impl From<TransferFlags> for DebitFlags {
	fn from(f: TransferFlags) -> Self {
		Self { keep_alive: f.keep_alive, best_effort: f.best_effort }
	}
}

/// Possible errors when converting between external and asset balances.
#[derive(Eq, PartialEq, Copy, Clone, RuntimeDebug, Encode, Decode)]
pub enum ConversionError {
	/// The external minimum balance must not be zero.
	MinBalanceZero,
	/// The asset is not present in storage.
	AssetMissing,
	/// The asset is not sufficient and thus does not have a reliable `min_balance` so it cannot be
	/// converted.
	AssetNotSufficient,
}

// Type alias for `frame_system`'s account id.
type AccountIdOf<T> = <T as frame_system::Config>::AccountId;
// This pallet's asset id and balance type.
type AssetIdOf<T, I> = <T as Config<I>>::AssetId;
type AssetBalanceOf<T, I> = <T as Config<I>>::Balance;
// Generic fungible balance type.
type BalanceOf<F, T> = <F as fungible::Inspect<AccountIdOf<T>>>::Balance;

/// Converts a balance value into an asset balance based on the ratio between the fungible's
/// minimum balance and the minimum asset balance.
pub struct BalanceToAssetBalance<F, T, CON, I = ()>(PhantomData<(F, T, CON, I)>);
impl<F, T, CON, I> ConversionToAssetBalance<BalanceOf<F, T>, AssetIdOf<T, I>, AssetBalanceOf<T, I>>
	for BalanceToAssetBalance<F, T, CON, I>
where
	F: fungible::Inspect<AccountIdOf<T>>,
	T: Config<I>,
	I: 'static,
	CON: Convert<BalanceOf<F, T>, AssetBalanceOf<T, I>>,
	BalanceOf<F, T>: FixedPointOperand + Zero,
	AssetBalanceOf<T, I>: FixedPointOperand + Zero,
{
	type Error = ConversionError;

	/// Convert the given balance value into an asset balance based on the ratio between the
	/// fungible's minimum balance and the minimum asset balance.
	///
	/// Will return `Err` if the asset is not found, not sufficient or the fungible's minimum
	/// balance is zero.
	fn to_asset_balance(
		balance: BalanceOf<F, T>,
		asset_id: AssetIdOf<T, I>,
	) -> Result<AssetBalanceOf<T, I>, ConversionError> {
		let asset = Asset::<T, I>::get(asset_id).ok_or(ConversionError::AssetMissing)?;
		// only sufficient assets have a min balance with reliable value
		ensure!(asset.is_sufficient, ConversionError::AssetNotSufficient);
		let min_balance = CON::convert(F::minimum_balance());
		// make sure we don't divide by zero
		ensure!(!min_balance.is_zero(), ConversionError::MinBalanceZero);
		let balance = CON::convert(balance);
		// balance * asset.min_balance / min_balance
		Ok(FixedU128::saturating_from_rational(asset.min_balance, min_balance)
			.saturating_mul_int(balance))
	}
}
