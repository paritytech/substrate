// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Implementation of `fungible` traits for Balances pallet.
use frame_support::traits::{tokens::KeepAlive::{self, NoKill, Keep}, fungible::CreditOf};
use super::*;

impl<T: Config<I>, I: 'static> fungible::Inspect<T::AccountId> for Pallet<T, I> {
	type Balance = T::Balance;

	fn total_issuance() -> Self::Balance {
		TotalIssuance::<T, I>::get()
	}
	fn active_issuance() -> Self::Balance {
		TotalIssuance::<T, I>::get().saturating_sub(InactiveIssuance::<T, I>::get())
	}
	fn minimum_balance() -> Self::Balance {
		T::ExistentialDeposit::get()
	}
	fn total_balance(who: &T::AccountId) -> Self::Balance {
		Self::account(who).total()
	}
	fn balance(who: &T::AccountId) -> Self::Balance {
		Self::account(who).free
	}
	fn reducible_balance(who: &T::AccountId, keep_alive: KeepAlive, force: bool) -> Self::Balance {
		let a = Self::account(who);
		let mut untouchable = Zero::zero();
		if !force {
			// Frozen balance applies to total. Anything on hold therefore gets discounted from the
			// limit given by the freezes.
			untouchable = a.fee_frozen.max(a.misc_frozen).saturating_sub(a.reserved);
		}
		let is_provider = !a.free.is_zero();
		let must_remain = !frame_system::Pallet::<T>::can_dec_provider(who) || keep_alive == NoKill;
		let stay_alive = is_provider && must_remain;
		if keep_alive == Keep || stay_alive {
			// ED needed, because we want to `keep_alive` or we are required as a provider ref.
			untouchable = untouchable.max(T::ExistentialDeposit::get());
		}
		// Liquid balance is what is neither on hold nor frozen/required for provider.
		a.free.saturating_sub(untouchable)
	}
	fn can_deposit(who: &T::AccountId, amount: Self::Balance, mint: bool) -> DepositConsequence {
		Self::deposit_consequence(who, amount, &Self::account(who), mint)
	}
	fn can_withdraw(
		who: &T::AccountId,
		amount: Self::Balance,
	) -> WithdrawConsequence<Self::Balance> {
		Self::withdraw_consequence(who, amount, &Self::account(who))
	}
}

impl<T: Config<I>, I: 'static> fungible::Mutate<T::AccountId> for Pallet<T, I> {
	fn mint_into(who: &T::AccountId, amount: Self::Balance) -> DispatchResult {
		if amount.is_zero() {
			return Ok(())
		}
		Self::try_mutate_account(who, |account, _is_new| -> DispatchResult {
			Self::deposit_consequence(who, amount, account, true).into_result()?;
			account.free += amount;
			Ok(())
		})?;
		TotalIssuance::<T, I>::mutate(|t| *t += amount);
		Self::deposit_event(Event::Deposit { who: who.clone(), amount });
		Ok(())
	}

	fn burn_from(
		who: &T::AccountId,
		amount: Self::Balance,
		// TODO: respect these:
		best_effort: bool,
		force: bool,
	) -> Result<Self::Balance, DispatchError> {
		if amount.is_zero() {
			return Ok(Self::Balance::zero())
		}
		let actual = Self::try_mutate_account(
			who,
			|account, _is_new| -> Result<T::Balance, DispatchError> {
				let extra = Self::withdraw_consequence(who, amount, account).into_result()?;
				let actual = amount + extra;
				account.free -= actual;
				Ok(actual)
			},
		)?;
		TotalIssuance::<T, I>::mutate(|t| *t -= actual);
		Self::deposit_event(Event::Withdraw { who: who.clone(), amount });
		Ok(actual)
	}
}

impl<T: Config<I>, I: 'static> fungible::Transfer<T::AccountId> for Pallet<T, I> {
	fn transfer(
		source: &T::AccountId,
		dest: &T::AccountId,
		amount: T::Balance,
		keep_alive: KeepAlive,
	) -> Result<T::Balance, DispatchError> {
		// TODO: Use other impl.
		let er = if keep_alive == KeepAlive::CanKill { AllowDeath } else { KeepAlive };
		<Self as Currency<T::AccountId>>::transfer(source, dest, amount, er).map(|_| amount)
	}

	fn deactivate(amount: Self::Balance) {
		InactiveIssuance::<T, I>::mutate(|b| b.saturating_accrue(amount));
	}

	fn reactivate(amount: Self::Balance) {
		InactiveIssuance::<T, I>::mutate(|b| b.saturating_reduce(amount));
	}
}

impl<T: Config<I>, I: 'static> fungible::Unbalanced<T::AccountId> for Pallet<T, I> {
	fn set_balance(who: &T::AccountId, amount: Self::Balance) -> DispatchResult {
		let max_reduction = <Self as fungible::Inspect<_>>::reducible_balance(who, KeepAlive::CanKill, true);
		Self::mutate_account(who, |account| -> DispatchResult {
			// Make sure the reduction (if there is one) is no more than the maximum allowed.
			let reduction = account.free.saturating_sub(amount);
			ensure!(reduction <= max_reduction, Error::<T, I>::InsufficientBalance);

			account.free = amount;
			Self::deposit_event(Event::BalanceSet {
				who: who.clone(),
				free: account.free,
			});
			Ok(())
		})?
	}

	fn set_total_issuance(amount: Self::Balance) {
		TotalIssuance::<T, I>::mutate(|t| *t = amount);
	}
}

impl<T: Config<I>, I: 'static> fungible::InspectHold<T::AccountId> for Pallet<T, I> {
	type Reason = T::ReserveIdentifier;

	fn total_balance_on_hold(who: &T::AccountId) -> T::Balance {
		Self::account(who).reserved
	}
	fn reducible_total_balance_on_hold(who: &T::AccountId, force: bool) -> Self::Balance {
		// The total balance must never drop below the freeze requirements if we're not forcing:
		let a = Self::account(who);
		let unavailable = if force {
			Self::Balance::zero()
		} else {
			// The freeze lock applies to the total balance, so we can discount the free balance
			// from the amount which the total reserved balance must provide to satusfy it.
			a.fee_frozen.max(a.misc_frozen).saturating_sub(a.free)
		};
		a.reserved.saturating_sub(unavailable)
	}
	fn balance_on_hold(reason: &Self::Reason, who: &T::AccountId) -> T::Balance {
		Reserves::<T, I>::get(who)
			.iter()
			.find(|x| &x.id == reason)
			.map_or_else(Zero::zero, |x| x.amount)
	}
	fn hold_available(reason: &Self::Reason, who: &T::AccountId) -> bool {
		if frame_system::Pallet::<T>::providers(who) == 0 { return false }
		let holds = Reserves::<T, I>::get(who);
		if holds.is_full() && !holds.iter().any(|x| &x.id == reason) { return false }
		true
	}
}
impl<T: Config<I>, I: 'static> fungible::UnbalancedHold<T::AccountId> for Pallet<T, I> {
	fn set_balance_on_hold(
		reason: &Self::Reason,
		who: &T::AccountId,
		amount: Self::Balance,
	) -> DispatchResult {
		if amount.is_zero() {
			return Ok(())
		}
		let mut new_account = Self::account(who);
		let mut holds = Reserves::<T, I>::get(who);
		let mut increase = true;
		let mut delta = amount;

		if let Some(item) = holds.iter_mut().find(|x| &x.id == reason) {
			delta = item.amount.max(amount) - item.amount.min(amount);
			increase = amount > item.amount;
			item.amount = amount;
		} else {
			holds.try_push(ReserveData { id: reason.clone(), amount })
				.map_err(|_| Error::<T, I>::TooManyReserves)?;
		}

		new_account.reserved = if increase {
			new_account.reserved.checked_add(&delta).ok_or(ArithmeticError::Overflow)?
		} else {
			new_account.reserved.checked_sub(&delta).ok_or(ArithmeticError::Underflow)?
		};

		let r = Self::try_mutate_account(who, |a, _| -> DispatchResult {
			*a = new_account;
			Ok(())
		});
		Reserves::<T, I>::insert(who, holds);
		r
	}
}
/*
	(_reason: &Self::Reason, who: &T::AccountId, amount: Self::Balance) -> DispatchResult {
		if amount.is_zero() {
			return Ok(())
		}
		ensure!(Self::can_reserve(who, amount), Error::<T, I>::InsufficientBalance);
		Self::mutate_account(who, |a| {
			a.free -= amount;
			a.reserved += amount;
		})?;
		Ok(())
	}
	fn release(
		_reason: &Self::Reason,
		who: &T::AccountId,
		amount: Self::Balance,
		best_effort: bool,
	) -> Result<T::Balance, DispatchError> {
		if amount.is_zero() {
			return Ok(amount)
		}
		// Done on a best-effort basis.
		Self::try_mutate_account(who, |a, _| {
			let new_free = a.free.saturating_add(amount.min(a.reserved));
			let actual = new_free - a.free;
			ensure!(best_effort || actual == amount, Error::<T, I>::InsufficientBalance);
			// ^^^ Guaranteed to be <= amount and <= a.reserved
			a.free = new_free;
			a.reserved = a.reserved.saturating_sub(actual);
			Ok(actual)
		})
	}
	fn burn_held(
		reason: &Self::Reason,
		who: &T::AccountId,
		amount: Self::Balance,
		best_effort: bool,
		force: bool,
	) -> Result<Self::Balance, DispatchError> {
		// Essentially an unreserve + burn_from, but we want to do it in a single op.
		todo!()
	}
	fn transfer_held(
		_reason: &Self::Reason,
		source: &T::AccountId,
		dest: &T::AccountId,
		amount: Self::Balance,
		best_effort: bool,
		on_hold: bool,
		_force: bool,
	) -> Result<Self::Balance, DispatchError> {
		let status = if on_hold { Status::Reserved } else { Status::Free };
		Self::do_transfer_reserved(source, dest, amount, best_effort, status)
	}
	*/
