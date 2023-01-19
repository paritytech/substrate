// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Adapter to use `fungibles::*` implementations as `fungible::*`.

use super::*;

/// Convert a `fungibles` trait implementation into a `fungible` trait implementation by identifying
/// a single item.
pub struct ItemOf<
	F: fungibles::Inspect<AccountId>,
	A: Get<<F as fungibles::Inspect<AccountId>>::AssetId>,
	AccountId,
>(sp_std::marker::PhantomData<(F, A, AccountId)>);

impl<
		F: fungibles::Inspect<AccountId>,
		A: Get<<F as fungibles::Inspect<AccountId>>::AssetId>,
		AccountId,
	> Inspect<AccountId> for ItemOf<F, A, AccountId>
{
	type Balance = <F as fungibles::Inspect<AccountId>>::Balance;
	fn total_issuance() -> Self::Balance {
		<F as fungibles::Inspect<AccountId>>::total_issuance(A::get())
	}
	fn active_issuance() -> Self::Balance {
		<F as fungibles::Inspect<AccountId>>::active_issuance(A::get())
	}
	fn minimum_balance() -> Self::Balance {
		<F as fungibles::Inspect<AccountId>>::minimum_balance(A::get())
	}
	fn balance(who: &AccountId) -> Self::Balance {
		<F as fungibles::Inspect<AccountId>>::balance(A::get(), who)
	}
	fn total_balance(who: &AccountId) -> Self::Balance {
		<F as fungibles::Inspect<AccountId>>::total_balance(A::get(), who)
	}
	fn reducible_balance(who: &AccountId, keep_alive: KeepAlive, force: bool) -> Self::Balance {
		<F as fungibles::Inspect<AccountId>>::reducible_balance(A::get(), who, keep_alive, force)
	}
	fn can_deposit(who: &AccountId, amount: Self::Balance, mint: bool) -> DepositConsequence {
		<F as fungibles::Inspect<AccountId>>::can_deposit(A::get(), who, amount, mint)
	}
	fn can_withdraw(who: &AccountId, amount: Self::Balance) -> WithdrawConsequence<Self::Balance> {
		<F as fungibles::Inspect<AccountId>>::can_withdraw(A::get(), who, amount)
	}
}

impl<
		F: fungibles::InspectHold<AccountId>,
		A: Get<<F as fungibles::Inspect<AccountId>>::AssetId>,
		AccountId,
	> InspectHold<AccountId> for ItemOf<F, A, AccountId>
{
	type Reason = F::Reason;

	fn reducible_total_balance_on_hold(who: &AccountId, force: bool) -> Self::Balance {
		<F as fungibles::InspectHold<AccountId>>::reducible_total_balance_on_hold(
			A::get(),
			who,
			force,
		)
	}
	fn hold_available(reason: &Self::Reason, who: &AccountId) -> bool {
		<F as fungibles::InspectHold<AccountId>>::hold_available(A::get(), reason, who)
	}
	fn total_balance_on_hold(who: &AccountId) -> Self::Balance {
		<F as fungibles::InspectHold<AccountId>>::total_balance_on_hold(A::get(), who)
	}
	fn balance_on_hold(reason: &Self::Reason, who: &AccountId) -> Self::Balance {
		<F as fungibles::InspectHold<AccountId>>::balance_on_hold(A::get(), reason, who)
	}
	fn can_hold(reason: &Self::Reason, who: &AccountId, amount: Self::Balance) -> bool {
		<F as fungibles::InspectHold<AccountId>>::can_hold(A::get(), reason, who, amount)
	}
}

impl<
		F: fungibles::Unbalanced<AccountId>,
		A: Get<<F as fungibles::Inspect<AccountId>>::AssetId>,
		AccountId,
	> Unbalanced<AccountId> for ItemOf<F, A, AccountId>
{
	fn set_balance(who: &AccountId, amount: Self::Balance) -> DispatchResult {
		<F as fungibles::Unbalanced<AccountId>>::set_balance(A::get(), who, amount)
	}
	fn set_total_issuance(amount: Self::Balance) -> () {
		<F as fungibles::Unbalanced<AccountId>>::set_total_issuance(A::get(), amount)
	}
	fn decrease_balance(
		who: &AccountId,
		amount: Self::Balance,
		best_effort: bool,
		keep_alive: KeepAlive,
		force: bool,
	) -> Result<Self::Balance, DispatchError> {
		<F as fungibles::Unbalanced<AccountId>>::decrease_balance(
			A::get(),
			who,
			amount,
			best_effort,
			keep_alive,
			force,
		)
	}
	fn increase_balance(
		who: &AccountId,
		amount: Self::Balance,
		best_effort: bool,
	) -> Result<Self::Balance, DispatchError> {
		<F as fungibles::Unbalanced<AccountId>>::increase_balance(
			A::get(),
			who,
			amount,
			best_effort,
		)
	}
}

impl<
		F: fungibles::UnbalancedHold<AccountId>,
		A: Get<<F as fungibles::Inspect<AccountId>>::AssetId>,
		AccountId,
	> UnbalancedHold<AccountId> for ItemOf<F, A, AccountId>
{
	fn set_balance_on_hold(
		reason: &Self::Reason,
		who: &AccountId,
		amount: Self::Balance,
	) -> DispatchResult {
		<F as fungibles::UnbalancedHold<AccountId>>::set_balance_on_hold(
			A::get(),
			reason,
			who,
			amount,
		)
	}
	fn decrease_balance_on_hold(
		reason: &Self::Reason,
		who: &AccountId,
		amount: Self::Balance,
		best_effort: bool,
	) -> Result<Self::Balance, DispatchError> {
		<F as fungibles::UnbalancedHold<AccountId>>::decrease_balance_on_hold(
			A::get(),
			reason,
			who,
			amount,
			best_effort,
		)
	}
	fn increase_balance_on_hold(
		reason: &Self::Reason,
		who: &AccountId,
		amount: Self::Balance,
		best_effort: bool,
	) -> Result<Self::Balance, DispatchError> {
		<F as fungibles::UnbalancedHold<AccountId>>::increase_balance_on_hold(
			A::get(),
			reason,
			who,
			amount,
			best_effort,
		)
	}
}
