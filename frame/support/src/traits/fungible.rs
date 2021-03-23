// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! The traits for dealing with a single fungible token class and any associated types.

use super::*;

/// Trait for providing balance-inspection access to a fungible asset.
pub trait InspectFungible<AccountId> {
	/// Scalar type for representing balance of an account.
	type Balance: AtLeast32BitUnsigned + FullCodec + Copy + Default;
	/// The total amount of issuance in the system.
	fn total_issuance() -> Self::Balance;
	/// The minimum balance any single account may have.
	fn minimum_balance() -> Self::Balance;
	/// Get the balance of `who`.
	fn balance(who: &AccountId) -> Self::Balance;
	/// Returns `true` if the balance of `who` may be increased by `amount`.
	fn can_deposit(who: &AccountId, amount: Self::Balance) -> bool;
	/// Returns `Failed` if the balance of `who` may not be decreased by `amount`, otherwise
	/// the consequence.
	fn can_withdraw(who: &AccountId, amount: Self::Balance) -> WithdrawConsequence<Self::Balance>;
}

/// Trait for providing an ERC-20 style fungible asset.
pub trait Fungible<AccountId>: InspectFungible<AccountId> {
	/// Increase the balance of `who` by `amount`.
	fn deposit(who: &AccountId, amount: Self::Balance) -> DispatchResult;
	/// Attempt to reduce the balance of `who` by `amount`.
	fn withdraw(who: &AccountId, amount: Self::Balance) -> DispatchResult;
}

/// Trait for providing a fungible asset which can only be transferred.
pub trait TransferFungible<AccountId>: InspectFungible<AccountId> {
	/// Transfer funds from one account into another.
	fn transfer(
		source: &AccountId,
		dest: &AccountId,
		amount: Self::Balance,
	) -> DispatchResult;
}

/// Trait for providing a fungible asset which can be reserved.
pub trait ReserveFungible<AccountId>: InspectFungible<AccountId> {
	/// Amount of funds held in reserve by `who`.
	fn reserved_balance(who: &AccountId) -> Self::Balance;
	/// Amount of funds held in total by `who`.
	fn total_balance(who: &AccountId) -> Self::Balance {
		Self::reserved_balance(who).saturating_add(Self::balance(who))
	}
	/// Check to see if some `amount` of funds may be reserved on the account of `who`.
	fn can_reserve(who: &AccountId, amount: Self::Balance) -> bool;
	/// Reserve some funds in an account.
	fn reserve(who: &AccountId, amount: Self::Balance) -> DispatchResult;
	/// Unreserve some funds in an account.
	fn unreserve(who: &AccountId, amount: Self::Balance) -> DispatchResult;
	/// Transfer reserved funds into another account.
	fn repatriate_reserved(
		who: &AccountId,
		amount: Self::Balance,
		status: BalanceStatus,
	) -> DispatchResult;
}

pub struct AssetOf<
	F: InspectFungibles<AccountId>,
	A: Get<<F as InspectFungibles<AccountId>>::AssetId>,
	AccountId,
>(
	sp_std::marker::PhantomData<(F, A, AccountId)>
);
impl<
	F: InspectFungibles<AccountId>,
	A: Get<<F as InspectFungibles<AccountId>>::AssetId>,
	AccountId,
> InspectFungible<AccountId> for AssetOf<F, A, AccountId> {
	type Balance = <F as InspectFungibles<AccountId>>::Balance;
	fn total_issuance() -> Self::Balance {
		<F as InspectFungibles<AccountId>>::total_issuance(A::get())
	}
	fn minimum_balance() -> Self::Balance {
		<F as InspectFungibles<AccountId>>::minimum_balance(A::get())
	}
	fn balance(who: &AccountId) -> Self::Balance {
		<F as InspectFungibles<AccountId>>::balance(A::get(), who)
	}
	fn can_deposit(who: &AccountId, amount: Self::Balance) -> bool {
		<F as InspectFungibles<AccountId>>::can_deposit(A::get(), who, amount)
	}
	fn can_withdraw(who: &AccountId, amount: Self::Balance) -> WithdrawConsequence<Self::Balance> {
		<F as InspectFungibles<AccountId>>::can_withdraw(A::get(), who, amount)
	}
}

impl<
	F: Fungibles<AccountId>,
	A: Get<<F as InspectFungibles<AccountId>>::AssetId>,
	AccountId,
> Fungible<AccountId> for AssetOf<F, A, AccountId> {
	fn deposit(who: &AccountId, amount: Self::Balance) -> DispatchResult {
		<F as Fungibles<AccountId>>::deposit(A::get(), who, amount)
	}
	fn withdraw(who: &AccountId, amount: Self::Balance) -> DispatchResult {
		<F as Fungibles<AccountId>>::withdraw(A::get(), who, amount)
	}
}
impl<
	F: TransferFungibles<AccountId>,
	A: Get<<F as InspectFungibles<AccountId>>::AssetId>,
	AccountId,
> TransferFungible<AccountId> for AssetOf<F, A, AccountId> {
	fn transfer(source: &AccountId, dest: &AccountId, amount: Self::Balance) -> DispatchResult {
		<F as TransferFungibles<AccountId>>::transfer(A::get(), source, dest, amount)
	}
}
impl<
	F: ReserveFungibles<AccountId>,
	A: Get<<F as InspectFungibles<AccountId>>::AssetId>,
	AccountId,
> ReserveFungible<AccountId> for AssetOf<F, A, AccountId> {
	fn reserved_balance(who: &AccountId) -> Self::Balance {
		<F as ReserveFungibles<AccountId>>::reserved_balance(A::get(), who)
	}
	fn total_balance(who: &AccountId) -> Self::Balance {
		<F as ReserveFungibles<AccountId>>::total_balance(A::get(), who)
	}
	fn can_reserve(who: &AccountId, amount: Self::Balance) -> bool {
		<F as ReserveFungibles<AccountId>>::can_reserve(A::get(), who, amount)
	}
	fn reserve(who: &AccountId, amount: Self::Balance) -> DispatchResult {
		<F as ReserveFungibles<AccountId>>::reserve(A::get(), who, amount)
	}
	fn unreserve(who: &AccountId, amount: Self::Balance) -> DispatchResult {
		<F as ReserveFungibles<AccountId>>::unreserve(A::get(), who, amount)
	}
	fn repatriate_reserved(
		who: &AccountId,
		amount: Self::Balance,
		status: BalanceStatus,
	) -> DispatchResult {
		<F as ReserveFungibles<AccountId>>::repatriate_reserved(A::get(), who, amount, status)
	}
}
