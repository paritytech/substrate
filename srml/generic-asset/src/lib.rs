// Copyright 2019
//     by  Centrality Investments Ltd.
//     and Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! # Generic Asset Module
//!
//! The Generic Asset module provides functionality for handling accounts and asset balances.
//!
//! ## Overview
//!
//! The Generic Asset module provides functions for:
//!
//! - Creating a new kind of asset.
//! - Setting permissions of an asset.
//! - Getting and setting free balances.
//! - Retrieving total, reserved and unreserved balances.
//! - Repatriating a reserved balance to a beneficiary account.
//! - Transferring a balance between accounts (when not reserved).
//! - Slashing an account balance.
//! - Managing total issuance.
//! - Setting and managing locks.
//!
//! ### Terminology
//!
//! - **Staking Asset:** The asset for staking, to participate as Validators in the network.
//! - **Spending Asset:** The asset for payment, such as paying transfer fees, gas fees, etc.
//! - **Permissions:** A set of rules for a kind of asset, defining the allowed operations to the asset, and which
//! accounts are allowed to possess it.
//! - **Total Issuance:** The total number of units in existence in a system.
//! - **Free Balance:** The portion of a balance that is not reserved. The free balance is the only balance that matters
//! for most operations. When this balance falls below the existential deposit, most functionality of the account is
//! removed. When both it and the reserved balance are deleted, then the account is said to be dead.
//! - **Reserved Balance:** Reserved balance still belongs to the account holder, but is suspended. Reserved balance
//! can still be slashed, but only after all the free balance has been slashed. If the reserved balance falls below the
//! existential deposit then it and any related functionality will be deleted. When both it and the free balance are
//! deleted, then the account is said to be dead.
//! - **Imbalance:** A condition when some assets were credited or debited without equal and opposite accounting
//! (i.e. a difference between total issuance and account balances). Functions that result in an imbalance will
//! return an object of the `Imbalance` trait that can be managed within your runtime logic. (If an imbalance is
//! simply dropped, it should automatically maintain any book-keeping such as total issuance.)
//! - **Lock:** A freeze on a specified amount of an account's free balance until a specified block number. Multiple
//! locks always operate over the same funds, so they "overlay" rather than "stack".
//!
//! ### Implementations
//!
//! The Generic Asset module provides `AssetCurrency`, which implements the following traits. If these traits provide
//! the functionality that you need, you can avoid coupling with the Generic Asset module.
//!
//! - `Currency`: Functions for dealing with a fungible assets system.
//! - `ReservableCurrency`: Functions for dealing with assets that can be reserved from an account.
//! - `LockableCurrency`: Functions for dealing with accounts that allow liquidity restrictions.
//! - `Imbalance`: Functions for handling imbalances between total issuance in the system and account balances.
//! Must be used when a function creates new assets (e.g. a reward) or destroys some assets (e.g. a system fee).
//!
//! The Generic Asset module provides two types of `AssetCurrency` as follows.
//!
//! - `StakingAssetCurrency`: Currency for staking.
//! - `SpendingAssetCurrency`: Currency for payments such as transfer fee, gas fee.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! - `create`: Create a new kind of asset.
//! - `transfer`: Transfer some liquid free balance to another account.
//! - `update_permission`: Updates permission for a given `asset_id` and an account. The origin of this call
//! must have update permissions.
//! - `mint`: Mint an asset, increases its total issuance. The origin of this call must have mint permissions.
//! - `burn`: Burn an asset, decreases its total issuance. The origin of this call must have burn permissions.
//! - `create_reserved`: Create a new kind of reserved asset. The origin of this call must be root.
//!
//! ### Public Functions
//!
//! - `total_balance`: Get an account's total balance of an asset kind.
//! - `free_balance`: Get an account's free balance of an asset kind.
//! - `reserved_balance`: Get an account's reserved balance of an asset kind.
//! - `create_asset`: Creates an asset.
//! - `make_transfer`: Transfer some liquid free balance from one account to another.
//! This will not emit the `Transferred` event.
//! - `make_transfer_with_event`: Transfer some liquid free balance from one account to another.
//! This will emit the `Transferred` event.
//! - `reserve`: Moves an amount from free balance to reserved balance.
//! - `unreserve`: Move up to an amount from reserved balance to free balance. This function cannot fail.
//! - `slash`: Deduct up to an amount from the combined balance of `who`, preferring to deduct from the
//!	free balance. This function cannot fail.
//! - `reward`: Add up to an amount to the free balance of an account.
//! - `slash_reserved`: Deduct up to an amount from reserved balance of an account. This function cannot fail.
//! - `repatriate_reserved`: Move up to an amount from reserved balance of an account to free balance of another
//! account.
//! - `check_permission`: Check permission to perform burn, mint or update.
//! - `ensure_can_withdraw`: Check if the account is able to make a withdrawal of the given amount
//!	for the given reason.
//!
//! ### Usage
//!
//! The following examples show how to use the Generic Asset module in your custom module.
//!
//! ### Examples from the PRML
//!
//! The Fees module uses the `Currency` trait to handle fee charge/refund, and its types inherit from `Currency`:
//!
//! ```
//! use support::{
//! 	traits::{Currency, ExistenceRequirement, WithdrawReason},
//! 	dispatch::Result,
//! };
//! # pub trait Trait: system::Trait {
//! # 	type Currency: Currency<Self::AccountId>;
//! # }
//! type AssetOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;
//!
//! fn charge_fee<T: Trait>(transactor: &T::AccountId, amount: AssetOf<T>) -> Result {
//! 	// ...
//! 	T::Currency::withdraw(
//! 		transactor,
//! 		amount,
//! 		WithdrawReason::TransactionPayment,
//! 		ExistenceRequirement::KeepAlive,
//! 	)?;
//! 	// ...
//! 	Ok(())
//! }
//!
//! fn refund_fee<T: Trait>(transactor: &T::AccountId, amount: AssetOf<T>) -> Result {
//! 	// ...
//! 	T::Currency::deposit_into_existing(transactor, amount)?;
//! 	// ...
//! 	Ok(())
//! }
//!
//! # fn main() {}
//! ```
//!
//! ## Genesis config
//!
//! The Generic Asset module depends on the [`GenesisConfig`](./struct.GenesisConfig.html).

#![cfg_attr(not(feature = "std"), no_std)]

use parity_codec::{Decode, Encode, HasCompact, Input, Output};

use primitives::traits::{
	CheckedAdd, CheckedSub, MaybeSerializeDebug, Member, One, Saturating, SimpleArithmetic, Zero, Bounded
};

use rstd::prelude::*;
use rstd::{cmp, result};
use support::dispatch::Result;
use support::{
	decl_event, decl_module, decl_storage, ensure,
	traits::{
		Currency, ExistenceRequirement, Imbalance, LockIdentifier, LockableCurrency, ReservableCurrency,
		SignedImbalance, UpdateBalanceOutcome, WithdrawReason, WithdrawReasons,
	},
	Parameter, StorageDoubleMap, StorageMap, StorageValue,
};
use system::{ensure_signed, ensure_root};

mod mock;
mod tests;

pub use self::imbalances::{NegativeImbalance, PositiveImbalance};

pub trait Trait: system::Trait {
	type Balance: Parameter
		+ Member
		+ SimpleArithmetic
		+ Default
		+ Copy
		+ MaybeSerializeDebug;
	type AssetId: Parameter + Member + SimpleArithmetic + Default + Copy;
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

pub trait Subtrait: system::Trait {
	type Balance: Parameter
		+ Member
		+ SimpleArithmetic
		+ Default
		+ Copy
		+ MaybeSerializeDebug;
	type AssetId: Parameter + Member + SimpleArithmetic + Default + Copy;
}

impl<T: Trait> Subtrait for T {
	type Balance = T::Balance;
	type AssetId = T::AssetId;
}

/// Asset creation options.
#[cfg_attr(feature = "std", derive(Debug))]
#[derive(Clone, Encode, Decode, PartialEq, Eq)]
pub struct AssetOptions<Balance: HasCompact, AccountId> {
	/// Initial issuance of this asset. All deposit to the creater of the asset.
	#[codec(compact)]
	pub initial_issuance: Balance,
	/// Which accounts are allowed to possess this asset.
	pub permissions: PermissionLatest<AccountId>,
}

/// Owner of an asset.
#[cfg_attr(feature = "std", derive(Debug))]
#[derive(Clone, Encode, Decode, PartialEq, Eq)]
pub enum Owner<AccountId> {
	/// No owner.
	None,
	/// Owned by an AccountId
	Address(AccountId),
}

impl<AccountId> Default for Owner<AccountId> {
	fn default() -> Self {
		Owner::None
	}
}

/// Asset permissions
#[cfg_attr(feature = "std", derive(Debug))]
#[derive(Clone, Encode, Decode, PartialEq, Eq)]
pub struct PermissionsV1<AccountId> {
	/// Who have permission to update asset permission
	pub update: Owner<AccountId>,
	/// Who have permission to mint new asset
	pub mint: Owner<AccountId>,
	/// Who have permission to burn asset
	pub burn: Owner<AccountId>,
}

#[cfg_attr(feature = "std", derive(Debug))]
#[derive(Clone, Encode, Decode, PartialEq, Eq)]
#[repr(u8)]
enum PermissionVersionNumber {
	V1 = 0,
}

/// Versioned asset permission
#[cfg_attr(feature = "std", derive(Debug))]
#[derive(Clone, PartialEq, Eq)]
pub enum PermissionVersions<AccountId> {
	V1(PermissionsV1<AccountId>),
}

/// Asset permission types
pub enum PermissionType {
	/// Permission to update asset permission
	Burn,
	/// Permission to mint new asset
	Mint,
	/// Permission to burn asset
	Update,
}

/// Alias to latest asset permissions
pub type PermissionLatest<AccountId> = PermissionsV1<AccountId>;

impl<AccountId> Default for PermissionVersions<AccountId> {
	fn default() -> Self {
		PermissionVersions::V1(Default::default())
	}
}

impl<AccountId: Encode> Encode for PermissionVersions<AccountId> {
	fn encode_to<T: Output>(&self, dest: &mut T) {
		match self {
			PermissionVersions::V1(payload) => {
				dest.push(&PermissionVersionNumber::V1);
				dest.push(payload);
			},
		}
	}
}

impl<AccountId: Decode> Decode for PermissionVersions<AccountId> {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		let version = PermissionVersionNumber::decode(input)?;
		Some(
			match version {
				PermissionVersionNumber::V1 => PermissionVersions::V1(Decode::decode(input)?)
			}
		)
	}
}

impl<AccountId> Default for PermissionsV1<AccountId> {
	fn default() -> Self {
		PermissionsV1 {
			update: Owner::None,
			mint: Owner::None,
			burn: Owner::None,
		}
	}
}

impl<AccountId> Into<PermissionLatest<AccountId>> for PermissionVersions<AccountId> {
	fn into(self) -> PermissionLatest<AccountId> {
		match self {
			PermissionVersions::V1(v1) => v1,
		}
	}
}

/// Converts the latest permission to other version.
impl<AccountId> Into<PermissionVersions<AccountId>> for PermissionLatest<AccountId> {
	fn into(self) -> PermissionVersions<AccountId> {
		PermissionVersions::V1(self)
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event<T>() = default;

		/// Create a new kind of asset.
		fn create(origin, options: AssetOptions<T::Balance, T::AccountId>) -> Result {
			let origin = ensure_signed(origin)?;
			let id = Self::next_asset_id();

			let permissions: PermissionVersions<T::AccountId> = options.permissions.clone().into();

			// The last available id serves as the overflow mark and won't be used.
			let next_id = id.checked_add(&One::one()).ok_or_else(|| "No new assets id available.")?;

			<NextAssetId<T>>::put(next_id);
			<TotalIssuance<T>>::insert(id, &options.initial_issuance);
			<FreeBalance<T>>::insert(&id, &origin, options.initial_issuance);
			<Permissions<T>>::insert(&id, permissions);

			Self::deposit_event(RawEvent::Created(id, origin, options));

			Ok(())
		}

		/// Transfer some liquid free balance to another account.
		pub fn transfer(origin, #[compact] asset_id: T::AssetId, to: T::AccountId, #[compact] amount: T::Balance) {
			let origin = ensure_signed(origin)?;
			ensure!(!amount.is_zero(), "cannot transfer zero amount");
			Self::make_transfer_with_event(&asset_id, &origin, &to, amount)?;
		}

		/// Updates permission for a given `asset_id` and an account.
		///
		/// The `origin` must have `update` permission.
		fn update_permission(
			origin,
			#[compact] asset_id: T::AssetId,
			new_permission: PermissionLatest<T::AccountId>
		) -> Result {
			let origin = ensure_signed(origin)?;

			let permissions: PermissionVersions<T::AccountId> = new_permission.into();

			if Self::check_permission(&asset_id, &origin, &PermissionType::Update) {
				<Permissions<T>>::insert(asset_id, &permissions);

				Self::deposit_event(RawEvent::PermissionUpdated(asset_id, permissions.into()));

				Ok(())
			} else {
				Err("Origin does not have enough permission to update permissions.")
			}
		}

		/// Mints an asset, increases its total issuance.
		/// The origin must have `mint` permissions.
		fn mint(origin, #[compact] asset_id: T::AssetId, to: T::AccountId, amount: T::Balance) -> Result {
			let origin = ensure_signed(origin)?;
			if Self::check_permission(&asset_id, &origin, &PermissionType::Mint) {
				let original_free_balance = Self::free_balance(&asset_id, &to);
				let current_total_issuance = <TotalIssuance<T>>::get(asset_id);
				let new_total_issuance = current_total_issuance.checked_add(&amount)
					.ok_or_else(|| "total_issuance got overflow after minting.")?;
				let value = original_free_balance.checked_add(&amount)
					.ok_or_else(|| "free balance got overflow after minting.")?;

				<TotalIssuance<T>>::insert(asset_id, new_total_issuance);
				Self::set_free_balance(&asset_id, &to, value);

				Self::deposit_event(RawEvent::Minted(asset_id, to, amount));

				Ok(())
			} else {
				Err("The origin does not have permission to mint an asset.")
			}
		}

		/// Burns an asset, decreases its total issuance.
		///
		/// The `origin` must have `burn` permissions.
		fn burn(origin, #[compact] asset_id: T::AssetId, to: T::AccountId, amount: T::Balance) -> Result {
			let origin = ensure_signed(origin)?;

			if Self::check_permission(&asset_id, &origin, &PermissionType::Burn) {
				let original_free_balance = Self::free_balance(&asset_id, &to);

				let current_total_issuance = <TotalIssuance<T>>::get(asset_id);
				let new_total_issuance = current_total_issuance.checked_sub(&amount)
					.ok_or_else(|| "total_issuance got underflow after burning")?;
				let value = original_free_balance.checked_sub(&amount)
					.ok_or_else(|| "free_balance got underflow after burning")?;

				<TotalIssuance<T>>::insert(asset_id, new_total_issuance);

				Self::set_free_balance(&asset_id, &to, value);

				Self::deposit_event(RawEvent::Burned(asset_id, to, amount));

				Ok(())
			} else {
				Err("The origin does not have permission to burn an asset.")
			}
		}

		/// Can be used to create reserved tokens.
		/// Requires Root call.
		fn create_reserved(origin, asset_id: T::AssetId, options: AssetOptions<T::Balance, T::AccountId>) -> Result {
			ensure_root(origin)?;
			Self::create_asset(Some(asset_id), None, options)
		}
	}
}

#[derive(Encode, Decode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct BalanceLock<Balance, BlockNumber> {
	pub id: LockIdentifier,
	pub amount: Balance,
	pub until: BlockNumber,
	pub reasons: WithdrawReasons,
}

decl_storage! {
	trait Store for Module<T: Trait> as GenericAsset {
		/// Total issuance of a given asset.
		pub TotalIssuance get(total_issuance) build(|config: &GenesisConfig<T>| {
			let issuance = config.initial_balance * (config.endowed_accounts.len() as u32).into();
			config.assets.iter().map(|id| (id.clone(), issuance)).collect::<Vec<_>>()
		}): map T::AssetId => T::Balance;

		/// The free balance of a given asset under an account.
		pub FreeBalance: double_map T::AssetId, twox_128(T::AccountId) => T::Balance;

		/// The reserved balance of a given asset under an account.
		pub ReservedBalance: double_map T::AssetId, twox_128(T::AccountId) => T::Balance;

		/// Next available ID for user-created asset.
		pub NextAssetId get(next_asset_id) config(): T::AssetId;

		/// Permission options for a given asset.
		pub Permissions get(get_permission): map T::AssetId => PermissionVersions<T::AccountId>;

		/// Any liquidity locks on some account balances.
		pub Locks get(locks): map T::AccountId => Vec<BalanceLock<T::Balance, T::BlockNumber>>;

		/// The identity of the asset which is the one that is designated for the chain's staking system.
		pub StakingAssetId get(staking_asset_id) config(): T::AssetId;

		/// The identity of the asset which is the one that is designated for paying the chain's transaction fee.
		pub SpendingAssetId get(spending_asset_id) config(): T::AssetId;
	}
	add_extra_genesis {
		config(assets): Vec<T::AssetId>;
		config(initial_balance): T::Balance;
		config(endowed_accounts): Vec<T::AccountId>;

		build(|
			storage: &mut primitives::StorageOverlay,
			_: &mut primitives::ChildrenStorageOverlay,
			config: &GenesisConfig<T>| {
			config.assets.iter().for_each(|asset_id| {
				config.endowed_accounts.iter().for_each(|account_id| {
					storage.insert(
						<FreeBalance<T>>::key_for(asset_id, account_id),
						<T::Balance as parity_codec::Encode>::encode(&config.initial_balance)
					);
				});
			});
		});
	}
}

decl_event!(
	pub enum Event<T> where
		<T as system::Trait>::AccountId,
		<T as Trait>::Balance,
		<T as Trait>::AssetId,
		AssetOptions = AssetOptions<<T as Trait>::Balance, <T as system::Trait>::AccountId>
	{
		/// Asset created (asset_id, creator, asset_options).
		Created(AssetId, AccountId, AssetOptions),
		/// Asset transfer succeeded (asset_id, from, to, amount).
		Transferred(AssetId, AccountId, AccountId, Balance),
		/// Asset permission updated (asset_id, new_permissions).
		PermissionUpdated(AssetId, PermissionLatest<AccountId>),
		/// New asset minted (asset_id, account, amount).
		Minted(AssetId, AccountId, Balance),
		/// Asset burned (asset_id, account, amount).
		Burned(AssetId, AccountId, Balance),
	}
);

impl<T: Trait> Module<T> {
	// PUBLIC IMMUTABLES

	/// Get an account's total balance of an asset kind.
	pub fn total_balance(asset_id: &T::AssetId, who: &T::AccountId) -> T::Balance {
		Self::free_balance(asset_id, who) + Self::reserved_balance(asset_id, who)
	}

	/// Get an account's free balance of an asset kind.
	pub fn free_balance(asset_id: &T::AssetId, who: &T::AccountId) -> T::Balance {
		<FreeBalance<T>>::get(asset_id, who)
	}

	/// Get an account's reserved balance of an asset kind.
	pub fn reserved_balance(asset_id: &T::AssetId, who: &T::AccountId) -> T::Balance {
		<ReservedBalance<T>>::get(asset_id, who)
	}

	/// Creates an asset.
	///
	/// # Arguments
	/// * `asset_id`: An ID of a reserved asset.
	/// If not provided, a user-generated asset will be created with the next available ID.
	/// * `from_account`: The initiator account of this call
	/// * `asset_options`: Asset creation options.
	///
	pub fn create_asset(
		asset_id: Option<T::AssetId>,
		from_account: Option<T::AccountId>,
		options: AssetOptions<T::Balance, T::AccountId>,
	) -> Result {
		let asset_id = if let Some(asset_id) = asset_id {
			ensure!(!<TotalIssuance<T>>::exists(&asset_id), "Asset id already taken.");
			ensure!(asset_id < Self::next_asset_id(), "Asset id not available.");
			asset_id
		} else {
			let asset_id = Self::next_asset_id();
			let next_id = asset_id
				.checked_add(&One::one())
				.ok_or_else(|| "No new user asset id available.")?;
			<NextAssetId<T>>::put(next_id);
			asset_id
		};

		let account_id = from_account.unwrap_or_default();
		let permissions: PermissionVersions<T::AccountId> = options.permissions.clone().into();

		<TotalIssuance<T>>::insert(asset_id, &options.initial_issuance);
		<FreeBalance<T>>::insert(&asset_id, &account_id, options.initial_issuance);
		<Permissions<T>>::insert(&asset_id, permissions);

		Self::deposit_event(RawEvent::Created(asset_id, account_id, options));

		Ok(())
	}

	/// Transfer some liquid free balance from one account to another.
	/// This will not emit the `Transferred` event.
	pub fn make_transfer(asset_id: &T::AssetId, from: &T::AccountId, to: &T::AccountId, amount: T::Balance) -> Result {
		let new_balance = Self::free_balance(asset_id, from)
			.checked_sub(&amount)
			.ok_or_else(|| "balance too low to send amount")?;
		Self::ensure_can_withdraw(asset_id, from, amount, WithdrawReason::Transfer, new_balance)?;

		if from != to {
			<FreeBalance<T>>::mutate(asset_id, from, |balance| *balance -= amount);
			<FreeBalance<T>>::mutate(asset_id, to, |balance| *balance += amount);
		}

		Ok(())
	}

	/// Transfer some liquid free balance from one account to another.
	/// This will emit the `Transferred` event.
	pub fn make_transfer_with_event(
		asset_id: &T::AssetId,
		from: &T::AccountId,
		to: &T::AccountId,
		amount: T::Balance,
	) -> Result {
		Self::make_transfer(asset_id, from, to, amount)?;

		if from != to {
			Self::deposit_event(RawEvent::Transferred(*asset_id, from.clone(), to.clone(), amount));
		}

		Ok(())
	}

	/// Move `amount` from free balance to reserved balance.
	///
	/// If the free balance is lower than `amount`, then no funds will be moved and an `Err` will
	/// be returned. This is different behavior than `unreserve`.
	pub fn reserve(asset_id: &T::AssetId, who: &T::AccountId, amount: T::Balance) -> Result {
		// Do we need to consider that this is an atomic transaction?
		let original_reserve_balance = Self::reserved_balance(asset_id, who);
		let original_free_balance = Self::free_balance(asset_id, who);
		if original_free_balance < amount {
			return Err("not enough free funds");
		}
		let new_reserve_balance = original_reserve_balance + amount;
		Self::set_reserved_balance(asset_id, who, new_reserve_balance);
		let new_free_balance = original_free_balance - amount;
		Self::set_free_balance(asset_id, who, new_free_balance);
		Ok(())
	}

	/// Moves up to `amount` from reserved balance to free balance. This function cannot fail.
	///
	/// As many assets up to `amount` will be moved as possible. If the reserve balance of `who`
	/// is less than `amount`, then the remaining amount will be returned.
	/// NOTE: This is different behavior than `reserve`.
	pub fn unreserve(asset_id: &T::AssetId, who: &T::AccountId, amount: T::Balance) -> T::Balance {
		let b = Self::reserved_balance(asset_id, who);
		let actual = rstd::cmp::min(b, amount);
		let original_free_balance = Self::free_balance(asset_id, who);
		let new_free_balance = original_free_balance + actual;
		Self::set_free_balance(asset_id, who, new_free_balance);
		Self::set_reserved_balance(asset_id, who, b - actual);
		amount - actual
	}

	/// Deduct up to `amount` from the combined balance of `who`, preferring to deduct from the
	/// free balance. This function cannot fail.
	///
	/// As much funds up to `amount` will be deducted as possible. If this is less than `amount`
	/// then `Some(remaining)` will be returned. Full completion is given by `None`.
	/// NOTE: LOW-LEVEL: This will not attempt to maintain total issuance. It is expected that
	/// the caller will do this.
	fn slash(asset_id: &T::AssetId, who: &T::AccountId, amount: T::Balance) -> Option<T::Balance> {
		let free_balance = Self::free_balance(asset_id, who);
		let free_slash = rstd::cmp::min(free_balance, amount);
		let new_free_balance = free_balance - free_slash;
		Self::set_free_balance(asset_id, who, new_free_balance);
		if free_slash < amount {
			Self::slash_reserved(asset_id, who, amount - free_slash)
		} else {
			None
		}
	}

	/// Deducts up to `amount` from reserved balance of `who`. This function cannot fail.
	///
	/// As much funds up to `amount` will be deducted as possible. If the reserve balance of `who`
	/// is less than `amount`, then a non-zero second item will be returned.
	/// NOTE: LOW-LEVEL: This will not attempt to maintain total issuance. It is expected that
	/// the caller will do this.
	fn slash_reserved(asset_id: &T::AssetId, who: &T::AccountId, amount: T::Balance) -> Option<T::Balance> {
		let original_reserve_balance = Self::reserved_balance(asset_id, who);
		let slash = rstd::cmp::min(original_reserve_balance, amount);
		let new_reserve_balance = original_reserve_balance - slash;
		Self::set_reserved_balance(asset_id, who, new_reserve_balance);
		if amount == slash {
			None
		} else {
			Some(amount - slash)
		}
	}

	/// Move up to `amount` from reserved balance of account `who` to free balance of account
	/// `beneficiary`.
	///
	/// As much funds up to `amount` will be moved as possible. If this is less than `amount`, then
	/// the `remaining` would be returned, else `Zero::zero()`.
	/// NOTE: LOW-LEVEL: This will not attempt to maintain total issuance. It is expected that
	/// the caller will do this.
	fn repatriate_reserved(
		asset_id: &T::AssetId,
		who: &T::AccountId,
		beneficiary: &T::AccountId,
		amount: T::Balance,
	) -> T::Balance {
		let b = Self::reserved_balance(asset_id, who);
		let slash = rstd::cmp::min(b, amount);

		let original_free_balance = Self::free_balance(asset_id, beneficiary);
		let new_free_balance = original_free_balance + slash;
		Self::set_free_balance(asset_id, beneficiary, new_free_balance);

		let new_reserve_balance = b - slash;
		Self::set_reserved_balance(asset_id, who, new_reserve_balance);
		amount - slash
	}

	/// Check permission to perform burn, mint or update.
	///
	/// # Arguments
	/// * `asset_id`:  A `T::AssetId` type that contains the `asset_id`, which has the permission embedded.
	/// * `who`: A `T::AccountId` type that contains the `account_id` for which to check permissions.
	/// * `what`: The permission to check.
	///
	pub fn check_permission(asset_id: &T::AssetId, who: &T::AccountId, what: &PermissionType) -> bool {
		let permission_versions: PermissionVersions<T::AccountId> = Self::get_permission(asset_id);
		let permission = permission_versions.into();

		match (what, permission) {
			(
				PermissionType::Burn,
				PermissionLatest {
					burn: Owner::Address(account),
					..
				},
			) => account == *who,
			(
				PermissionType::Mint,
				PermissionLatest {
					mint: Owner::Address(account),
					..
				},
			) => account == *who,
			(
				PermissionType::Update,
				PermissionLatest {
					update: Owner::Address(account),
					..
				},
			) => account == *who,
			_ => false,
		}
	}

	/// Return `Ok` iff the account is able to make a withdrawal of the given amount
	/// for the given reason.
	///
	/// `Err(...)` with the reason why not otherwise.
	pub fn ensure_can_withdraw(
		asset_id: &T::AssetId,
		who: &T::AccountId,
		_amount: T::Balance,
		reason: WithdrawReason,
		new_balance: T::Balance,
	) -> Result {
		if asset_id != &Self::staking_asset_id() {
			return Ok(());
		}

		let locks = Self::locks(who);
		if locks.is_empty() {
			return Ok(());
		}
		let now = <system::Module<T>>::block_number();
		if Self::locks(who)
			.into_iter()
			.all(|l| now >= l.until || new_balance >= l.amount || !l.reasons.contains(reason))
		{
			Ok(())
		} else {
			Err("account liquidity restrictions prevent withdrawal")
		}
	}

	// PRIVATE MUTABLES

	/// NOTE: LOW-LEVEL: This will not attempt to maintain total issuance. It is expected that
	/// the caller will do this.
	fn set_reserved_balance(asset_id: &T::AssetId, who: &T::AccountId, balance: T::Balance) {
		<ReservedBalance<T>>::insert(asset_id, who, balance);
	}

	/// NOTE: LOW-LEVEL: This will not attempt to maintain total issuance. It is expected that
	/// the caller will do this.
	fn set_free_balance(asset_id: &T::AssetId, who: &T::AccountId, balance: T::Balance) {
		<FreeBalance<T>>::insert(asset_id, who, balance);
	}

	fn set_lock(
		id: LockIdentifier,
		who: &T::AccountId,
		amount: T::Balance,
		until: T::BlockNumber,
		reasons: WithdrawReasons,
	) {
		let now = <system::Module<T>>::block_number();
		let mut new_lock = Some(BalanceLock {
			id,
			amount,
			until,
			reasons,
		});
		let mut locks = <Module<T>>::locks(who)
			.into_iter()
			.filter_map(|l| {
				if l.id == id {
					new_lock.take()
				} else if l.until > now {
					Some(l)
				} else {
					None
				}
			})
			.collect::<Vec<_>>();
		if let Some(lock) = new_lock {
			locks.push(lock)
		}
		<Locks<T>>::insert(who, locks);
	}

	fn extend_lock(
		id: LockIdentifier,
		who: &T::AccountId,
		amount: T::Balance,
		until: T::BlockNumber,
		reasons: WithdrawReasons,
	) {
		let now = <system::Module<T>>::block_number();
		let mut new_lock = Some(BalanceLock {
			id,
			amount,
			until,
			reasons,
		});
		let mut locks = <Module<T>>::locks(who)
			.into_iter()
			.filter_map(|l| {
				if l.id == id {
					new_lock.take().map(|nl| BalanceLock {
						id: l.id,
						amount: l.amount.max(nl.amount),
						until: l.until.max(nl.until),
						reasons: l.reasons | nl.reasons,
					})
				} else if l.until > now {
					Some(l)
				} else {
					None
				}
			})
			.collect::<Vec<_>>();
		if let Some(lock) = new_lock {
			locks.push(lock)
		}
		<Locks<T>>::insert(who, locks);
	}

	fn remove_lock(id: LockIdentifier, who: &T::AccountId) {
		let now = <system::Module<T>>::block_number();
		let locks = <Module<T>>::locks(who)
			.into_iter()
			.filter_map(|l| if l.until > now && l.id != id { Some(l) } else { None })
			.collect::<Vec<_>>();
		<Locks<T>>::insert(who, locks);
	}
}

pub trait AssetIdProvider {
	type AssetId;
	fn asset_id() -> Self::AssetId;
}

// wrapping these imbalanes in a private module is necessary to ensure absolute privacy
// of the inner member.
mod imbalances {
	use super::{result, AssetIdProvider, Imbalance, Saturating, StorageMap, Subtrait, Zero};
	use rstd::mem;

	/// Opaque, move-only struct with private fields that serves as a token denoting that
	/// funds have been created without any equal and opposite accounting.
	#[must_use]
	pub struct PositiveImbalance<T: Subtrait, U: AssetIdProvider<AssetId = T::AssetId>>(
		T::Balance,
		rstd::marker::PhantomData<U>,
	);
	impl<T, U> PositiveImbalance<T, U>
	where
		T: Subtrait,
		U: AssetIdProvider<AssetId = T::AssetId>,
	{
		pub fn new(amount: T::Balance) -> Self {
			PositiveImbalance(amount, Default::default())
		}
	}

	/// Opaque, move-only struct with private fields that serves as a token denoting that
	/// funds have been destroyed without any equal and opposite accounting.
	#[must_use]
	pub struct NegativeImbalance<T: Subtrait, U: AssetIdProvider<AssetId = T::AssetId>>(
		T::Balance,
		rstd::marker::PhantomData<U>,
	);
	impl<T, U> NegativeImbalance<T, U>
	where
		T: Subtrait,
		U: AssetIdProvider<AssetId = T::AssetId>,
	{
		pub fn new(amount: T::Balance) -> Self {
			NegativeImbalance(amount, Default::default())
		}
	}

	impl<T, U> Imbalance<T::Balance> for PositiveImbalance<T, U>
	where
		T: Subtrait,
		U: AssetIdProvider<AssetId = T::AssetId>,
	{
		type Opposite = NegativeImbalance<T, U>;

		fn zero() -> Self {
			Self::new(Zero::zero())
		}
		fn drop_zero(self) -> result::Result<(), Self> {
			if self.0.is_zero() {
				Ok(())
			} else {
				Err(self)
			}
		}
		fn split(self, amount: T::Balance) -> (Self, Self) {
			let first = self.0.min(amount);
			let second = self.0 - first;

			mem::forget(self);
			(Self::new(first), Self::new(second))
		}
		fn merge(mut self, other: Self) -> Self {
			self.0 = self.0.saturating_add(other.0);
			mem::forget(other);

			self
		}
		fn subsume(&mut self, other: Self) {
			self.0 = self.0.saturating_add(other.0);
			mem::forget(other);
		}
		fn offset(self, other: Self::Opposite) -> result::Result<Self, Self::Opposite> {
			let (a, b) = (self.0, other.0);
			mem::forget((self, other));

			if a >= b {
				Ok(Self::new(a - b))
			} else {
				Err(NegativeImbalance::new(b - a))
			}
		}
		fn peek(&self) -> T::Balance {
			self.0.clone()
		}
	}

	impl<T, U> Imbalance<T::Balance> for NegativeImbalance<T, U>
	where
		T: Subtrait,
		U: AssetIdProvider<AssetId = T::AssetId>,
	{
		type Opposite = PositiveImbalance<T, U>;

		fn zero() -> Self {
			Self::new(Zero::zero())
		}
		fn drop_zero(self) -> result::Result<(), Self> {
			if self.0.is_zero() {
				Ok(())
			} else {
				Err(self)
			}
		}
		fn split(self, amount: T::Balance) -> (Self, Self) {
			let first = self.0.min(amount);
			let second = self.0 - first;

			mem::forget(self);
			(Self::new(first), Self::new(second))
		}
		fn merge(mut self, other: Self) -> Self {
			self.0 = self.0.saturating_add(other.0);
			mem::forget(other);

			self
		}
		fn subsume(&mut self, other: Self) {
			self.0 = self.0.saturating_add(other.0);
			mem::forget(other);
		}
		fn offset(self, other: Self::Opposite) -> result::Result<Self, Self::Opposite> {
			let (a, b) = (self.0, other.0);
			mem::forget((self, other));

			if a >= b {
				Ok(Self::new(a - b))
			} else {
				Err(PositiveImbalance::new(b - a))
			}
		}
		fn peek(&self) -> T::Balance {
			self.0.clone()
		}
	}

	impl<T, U> Drop for PositiveImbalance<T, U>
	where
		T: Subtrait,
		U: AssetIdProvider<AssetId = T::AssetId>,
	{
		/// Basic drop handler will just square up the total issuance.
		fn drop(&mut self) {
			<super::TotalIssuance<super::ElevatedTrait<T>>>::mutate(&U::asset_id(), |v| *v = v.saturating_add(self.0));
		}
	}

	impl<T, U> Drop for NegativeImbalance<T, U>
	where
		T: Subtrait,
		U: AssetIdProvider<AssetId = T::AssetId>,
	{
		/// Basic drop handler will just square up the total issuance.
		fn drop(&mut self) {
			<super::TotalIssuance<super::ElevatedTrait<T>>>::mutate(&U::asset_id(), |v| *v = v.saturating_sub(self.0));
		}
	}
}

// TODO: #2052
// Somewhat ugly hack in order to gain access to module's `increase_total_issuance_by`
// using only the Subtrait (which defines only the types that are not dependent
// on Positive/NegativeImbalance). Subtrait must be used otherwise we end up with a
// circular dependency with Trait having some types be dependent on PositiveImbalance<Trait>
// and PositiveImbalance itself depending back on Trait for its Drop impl (and thus
// its type declaration).
// This works as long as `increase_total_issuance_by` doesn't use the Imbalance
// types (basically for charging fees).
// This should eventually be refactored so that the three type items that do
// depend on the Imbalance type (TransactionPayment, TransferPayment, DustRemoval)
// are placed in their own SRML module.
struct ElevatedTrait<T: Subtrait>(T);
impl<T: Subtrait> Clone for ElevatedTrait<T> {
	fn clone(&self) -> Self {
		unimplemented!()
	}
}
impl<T: Subtrait> PartialEq for ElevatedTrait<T> {
	fn eq(&self, _: &Self) -> bool {
		unimplemented!()
	}
}
impl<T: Subtrait> Eq for ElevatedTrait<T> {}
impl<T: Subtrait> system::Trait for ElevatedTrait<T> {
	type Origin = T::Origin;
	type Index = T::Index;
	type BlockNumber = T::BlockNumber;
	type Hash = T::Hash;
	type Hashing = T::Hashing;
	type AccountId = T::AccountId;
	type Lookup = T::Lookup;
	type Header = T::Header;
	type Event = ();
	type BlockHashCount = T::BlockHashCount;
}
impl<T: Subtrait> Trait for ElevatedTrait<T> {
	type Balance = T::Balance;
	type AssetId = T::AssetId;
	type Event = ();
}

#[derive(Encode, Decode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct AssetCurrency<T, U>(rstd::marker::PhantomData<T>, rstd::marker::PhantomData<U>);

impl<T, U> Currency<T::AccountId> for AssetCurrency<T, U>
where
	T: Trait,
	U: AssetIdProvider<AssetId = T::AssetId>,
{
	type Balance = T::Balance;
	type PositiveImbalance = PositiveImbalance<T, U>;
	type NegativeImbalance = NegativeImbalance<T, U>;

	fn total_balance(who: &T::AccountId) -> Self::Balance {
		Self::free_balance(&who) + Self::reserved_balance(&who)
	}

	fn free_balance(who: &T::AccountId) -> Self::Balance {
		<Module<T>>::free_balance(&U::asset_id(), &who)
	}

	/// Returns the total staking asset issuance
	fn total_issuance() -> Self::Balance {
		<Module<T>>::total_issuance(U::asset_id())
	}

	fn minimum_balance() -> Self::Balance {
		Zero::zero()
	}

	fn transfer(transactor: &T::AccountId, dest: &T::AccountId, value: Self::Balance) -> Result {
		<Module<T>>::make_transfer(&U::asset_id(), transactor, dest, value)
	}

	fn ensure_can_withdraw(
		who: &T::AccountId,
		amount: Self::Balance,
		reason: WithdrawReason,
		new_balance: Self::Balance,
	) -> Result {
		<Module<T>>::ensure_can_withdraw(&U::asset_id(), who, amount, reason, new_balance)
	}

	fn withdraw(
		who: &T::AccountId,
		value: Self::Balance,
		reason: WithdrawReason,
		_: ExistenceRequirement, // no existential deposit policy for generic asset
	) -> result::Result<Self::NegativeImbalance, &'static str> {
		let new_balance = Self::free_balance(who)
			.checked_sub(&value)
			.ok_or_else(|| "account has too few funds")?;
		Self::ensure_can_withdraw(who, value, reason, new_balance)?;
		<Module<T>>::set_free_balance(&U::asset_id(), who, new_balance);
		Ok(NegativeImbalance::new(value))
	}

	fn deposit_into_existing(
		who: &T::AccountId,
		value: Self::Balance,
	) -> result::Result<Self::PositiveImbalance, &'static str> {
		// No existential deposit rule and creation fee in GA. `deposit_into_existing` is same with `deposit_creating`.
		Ok(Self::deposit_creating(who, value))
	}

	fn deposit_creating(who: &T::AccountId, value: Self::Balance) -> Self::PositiveImbalance {
		let (imbalance, _) = Self::make_free_balance_be(who, Self::free_balance(who) + value);
		if let SignedImbalance::Positive(p) = imbalance {
			p
		} else {
			// Impossible, but be defensive.
			Self::PositiveImbalance::zero()
		}
	}

	fn make_free_balance_be(
		who: &T::AccountId,
		balance: Self::Balance,
	) -> (
		SignedImbalance<Self::Balance, Self::PositiveImbalance>,
		UpdateBalanceOutcome,
	) {
		let original = <Module<T>>::free_balance(&U::asset_id(), who);
		let imbalance = if original <= balance {
			SignedImbalance::Positive(PositiveImbalance::new(balance - original))
		} else {
			SignedImbalance::Negative(NegativeImbalance::new(original - balance))
		};
		<Module<T>>::set_free_balance(&U::asset_id(), who, balance);
		(imbalance, UpdateBalanceOutcome::Updated)
	}

	fn can_slash(who: &T::AccountId, value: Self::Balance) -> bool {
		<Module<T>>::free_balance(&U::asset_id(), &who) >= value
	}

	fn slash(who: &T::AccountId, value: Self::Balance) -> (Self::NegativeImbalance, Self::Balance) {
		let remaining = <Module<T>>::slash(&U::asset_id(), who, value);
		if let Some(r) = remaining {
			(NegativeImbalance::new(value - r), r)
		} else {
			(NegativeImbalance::new(value), Zero::zero())
		}
	}

	fn burn(mut amount: Self::Balance) -> Self::PositiveImbalance {
		<TotalIssuance<T>>::mutate(&U::asset_id(), |issued|
			issued.checked_sub(&amount).unwrap_or_else(|| {
				amount = *issued;
				Zero::zero()
			})
		);
		PositiveImbalance::new(amount)
	}

	fn issue(mut amount: Self::Balance) -> Self::NegativeImbalance {
		<TotalIssuance<T>>::mutate(&U::asset_id(), |issued|
			*issued = issued.checked_add(&amount).unwrap_or_else(|| {
				amount = Self::Balance::max_value() - *issued;
				Self::Balance::max_value()
			})
		);
		NegativeImbalance::new(amount)
	}
}

impl<T, U> ReservableCurrency<T::AccountId> for AssetCurrency<T, U>
where
	T: Trait,
	U: AssetIdProvider<AssetId = T::AssetId>,
{
	fn can_reserve(who: &T::AccountId, value: Self::Balance) -> bool {
		Self::free_balance(who)
			.checked_sub(&value)
			.map_or(false, |new_balance|
				<Module<T>>::ensure_can_withdraw(&U::asset_id(), who, value, WithdrawReason::Reserve, new_balance).is_ok()
			)
	}

	fn reserved_balance(who: &T::AccountId) -> Self::Balance {
		<Module<T>>::reserved_balance(&U::asset_id(), &who)
	}

	fn reserve(who: &T::AccountId, value: Self::Balance) -> result::Result<(), &'static str> {
		<Module<T>>::reserve(&U::asset_id(), who, value)
	}

	fn unreserve(who: &T::AccountId, value: Self::Balance) -> Self::Balance {
		<Module<T>>::unreserve(&U::asset_id(), who, value)
	}

	fn slash_reserved(who: &T::AccountId, value: Self::Balance) -> (Self::NegativeImbalance, Self::Balance) {
		let b = Self::reserved_balance(&who.clone());
		let slash = cmp::min(b, value);

		<Module<T>>::set_reserved_balance(&U::asset_id(), who, b - slash);
		(NegativeImbalance::new(slash), value - slash)
	}

	fn repatriate_reserved(
		slashed: &T::AccountId,
		beneficiary: &T::AccountId,
		value: Self::Balance,
	) -> result::Result<Self::Balance, &'static str> {
		Ok(<Module<T>>::repatriate_reserved(&U::asset_id(), slashed, beneficiary, value))
	}
}

pub struct StakingAssetIdProvider<T>(rstd::marker::PhantomData<T>);

impl<T: Trait> AssetIdProvider for StakingAssetIdProvider<T> {
	type AssetId = T::AssetId;
	fn asset_id() -> Self::AssetId {
		<Module<T>>::staking_asset_id()
	}
}

pub struct SpendingAssetIdProvider<T>(rstd::marker::PhantomData<T>);

impl<T: Trait> AssetIdProvider for SpendingAssetIdProvider<T> {
	type AssetId = T::AssetId;
	fn asset_id() -> Self::AssetId {
		<Module<T>>::spending_asset_id()
	}
}

impl<T> LockableCurrency<T::AccountId> for AssetCurrency<T, StakingAssetIdProvider<T>>
where
	T: Trait,
	T::Balance: MaybeSerializeDebug,
{
	type Moment = T::BlockNumber;

	fn set_lock(
		id: LockIdentifier,
		who: &T::AccountId,
		amount: T::Balance,
		until: T::BlockNumber,
		reasons: WithdrawReasons,
	) {
		<Module<T>>::set_lock(id, who, amount, until, reasons)
	}

	fn extend_lock(
		id: LockIdentifier,
		who: &T::AccountId,
		amount: T::Balance,
		until: T::BlockNumber,
		reasons: WithdrawReasons,
	) {
		<Module<T>>::extend_lock(id, who, amount, until, reasons)
	}

	fn remove_lock(id: LockIdentifier, who: &T::AccountId) {
		<Module<T>>::remove_lock(id, who)
	}
}

pub type StakingAssetCurrency<T> = AssetCurrency<T, StakingAssetIdProvider<T>>;
pub type SpendingAssetCurrency<T> = AssetCurrency<T, SpendingAssetIdProvider<T>>;
