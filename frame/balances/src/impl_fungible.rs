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
use super::*;
use frame_support::traits::tokens::KeepAlive::{self, Keep, NoKill};

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
			untouchable = a.frozen.saturating_sub(a.reserved);
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
		if amount.is_zero() {
			return DepositConsequence::Success
		}

		if mint && TotalIssuance::<T, I>::get().checked_add(&amount).is_none() {
			return DepositConsequence::Overflow
		}

		let account = Self::account(who);
		let new_free = match account.free.checked_add(&amount) {
			None => return DepositConsequence::Overflow,
			Some(x) if x < T::ExistentialDeposit::get() => return DepositConsequence::BelowMinimum,
			Some(x) => x,
		};

		match account.reserved.checked_add(&new_free) {
			Some(_) => {},
			None => return DepositConsequence::Overflow,
		};

		// NOTE: We assume that we are a provider, so don't need to do any checks in the
		// case of account creation.

		DepositConsequence::Success
	}
	fn can_withdraw(
		who: &T::AccountId,
		amount: Self::Balance,
	) -> WithdrawConsequence<Self::Balance> {
		if amount.is_zero() {
			return WithdrawConsequence::Success
		}

		if TotalIssuance::<T, I>::get().checked_sub(&amount).is_none() {
			return WithdrawConsequence::Underflow
		}

		let account = Self::account(who);
		let new_free_balance = match account.free.checked_sub(&amount) {
			Some(x) => x,
			None => return WithdrawConsequence::BalanceLow,
		};

		let liquid = Self::reducible_balance(who, CanKill, false);
		if amount > liquid {
			return WithdrawConsequence::Frozen
		}

		// Provider restriction - total account balance cannot be reduced to zero if it cannot
		// sustain the loss of a provider reference.
		// NOTE: This assumes that the pallet is a provider (which is true). Is this ever changes,
		// then this will need to adapt accordingly.
		let ed = T::ExistentialDeposit::get();
		let success = if new_free_balance < ed {
			if frame_system::Pallet::<T>::can_dec_provider(who) {
				WithdrawConsequence::ReducedToZero(new_free_balance)
			} else {
				return WithdrawConsequence::WouldDie
			}
		} else {
			WithdrawConsequence::Success
		};

		let new_total_balance = new_free_balance.saturating_add(account.reserved);

		// Eventual free funds must be no less than the frozen balance.
		if new_total_balance < account.frozen {
			return WithdrawConsequence::Frozen
		}

		success
	}
}

impl<T: Config<I>, I: 'static> fungible::Unbalanced<T::AccountId> for Pallet<T, I> {
	fn set_balance(who: &T::AccountId, amount: Self::Balance) -> DispatchResult {
		let max_reduction =
			<Self as fungible::Inspect<_>>::reducible_balance(who, KeepAlive::CanKill, true);
		Self::mutate_account(who, |account| -> DispatchResult {
			// Make sure the reduction (if there is one) is no more than the maximum allowed.
			let reduction = account.free.saturating_sub(amount);
			ensure!(reduction <= max_reduction, Error::<T, I>::InsufficientBalance);

			account.free = amount;
			Self::deposit_event(Event::BalanceSet { who: who.clone(), free: account.free });
			Ok(())
		})?
	}

	fn set_total_issuance(amount: Self::Balance) {
		TotalIssuance::<T, I>::mutate(|t| *t = amount);
	}

	fn deactivate(amount: Self::Balance) {
		InactiveIssuance::<T, I>::mutate(|b| b.saturating_accrue(amount));
	}

	fn reactivate(amount: Self::Balance) {
		InactiveIssuance::<T, I>::mutate(|b| b.saturating_reduce(amount));
	}
}

impl<T: Config<I>, I: 'static> fungible::Mutate<T::AccountId> for Pallet<T, I> {
	fn done_mint_into(who: &T::AccountId, amount: Self::Balance) {
		Self::deposit_event(Event::<T, I>::Minted { who: who.clone(), amount });
	}
	fn done_burn_from(who: &T::AccountId, amount: Self::Balance) {
		Self::deposit_event(Event::<T, I>::Burned { who: who.clone(), amount });
	}
	fn done_shelve(who: &T::AccountId, amount: Self::Balance) {
		Self::deposit_event(Event::<T, I>::Suspended { who: who.clone(), amount });
	}
	fn done_restore(who: &T::AccountId, amount: Self::Balance) {
		Self::deposit_event(Event::<T, I>::Restored { who: who.clone(), amount });
	}
	fn done_transfer(source: &T::AccountId, dest: &T::AccountId, amount: Self::Balance) {
		Self::deposit_event(Event::<T, I>::Transfer {
			from: source.clone(),
			to: dest.clone(),
			amount,
		});
	}
}

impl<T: Config<I>, I: 'static> fungible::MutateHold<T::AccountId> for Pallet<T, I> {}

impl<T: Config<I>, I: 'static> fungible::InspectHold<T::AccountId> for Pallet<T, I> {
	type Reason = T::HoldIdentifier;

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
			// from the amount which the total reserved balance must provide to satisfy it.
			a.frozen.saturating_sub(a.free)
		};
		a.reserved.saturating_sub(unavailable)
	}
	fn balance_on_hold(reason: &Self::Reason, who: &T::AccountId) -> T::Balance {
		Holds::<T, I>::get(who)
			.iter()
			.find(|x| &x.id == reason)
			.map_or_else(Zero::zero, |x| x.amount)
	}
	fn hold_available(reason: &Self::Reason, who: &T::AccountId) -> bool {
		if frame_system::Pallet::<T>::providers(who) == 0 {
			return false
		}
		let holds = Holds::<T, I>::get(who);
		if holds.is_full() && !holds.iter().any(|x| &x.id == reason) {
			return false
		}
		true
	}
}

impl<T: Config<I>, I: 'static> fungible::UnbalancedHold<T::AccountId> for Pallet<T, I> {
	fn set_balance_on_hold(
		reason: &Self::Reason,
		who: &T::AccountId,
		amount: Self::Balance,
	) -> DispatchResult {
		let mut new_account = Self::account(who);
		let mut holds = Holds::<T, I>::get(who);
		let mut increase = true;
		let mut delta = amount;

		if let Some(item) = holds.iter_mut().find(|x| &x.id == reason) {
			delta = item.amount.max(amount) - item.amount.min(amount);
			increase = amount > item.amount;
			item.amount = amount;
		} else {
			holds
				.try_push(IdAmount { id: reason.clone(), amount })
				.map_err(|_| Error::<T, I>::TooManyHolds)?;
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
		Holds::<T, I>::insert(who, holds);
		r
	}
}

impl<T: Config<I>, I: 'static> fungible::InspectFreeze<T::AccountId> for Pallet<T, I> {
	type Id = T::FreezeIdentifier;

	fn balance_frozen(id: &Self::Id, who: &T::AccountId) -> Self::Balance {
		let locks = Freezes::<T, I>::get(who);
		locks.into_iter().find(|l| &l.id == id).map_or(Zero::zero(), |l| l.amount)
	}

	fn can_freeze(id: &Self::Id, who: &T::AccountId) -> bool {
		let l = Freezes::<T, I>::get(who);
		!l.is_full() || l.iter().any(|x| &x.id == id)
	}
}

impl<T: Config<I>, I: 'static> fungible::MutateFreeze<T::AccountId> for Pallet<T, I> {
	fn set_freeze(id: &Self::Id, who: &T::AccountId, amount: Self::Balance) -> DispatchResult {
		if amount.is_zero() {
			return Self::thaw(id, who)
		}
		let mut locks = Freezes::<T, I>::get(who);
		if let Some(i) = locks.iter_mut().find(|x| &x.id == id) {
			i.amount = amount;
		} else {
			locks
				.try_push(IdAmount { id: id.clone(), amount })
				.map_err(|_| Error::<T, I>::TooManyFreezes)?;
		}
		Self::update_freezes(who, locks.as_bounded_slice())
	}

	fn extend_freeze(id: &Self::Id, who: &T::AccountId, amount: Self::Balance) -> DispatchResult {
		if amount.is_zero() {
			return Ok(())
		}
		let mut locks = Freezes::<T, I>::get(who);
		if let Some(i) = locks.iter_mut().find(|x| &x.id == id) {
			i.amount = i.amount.max(amount);
		} else {
			locks
				.try_push(IdAmount { id: id.clone(), amount })
				.map_err(|_| Error::<T, I>::TooManyFreezes)?;
		}
		Self::update_freezes(who, locks.as_bounded_slice())
	}

	fn thaw(id: &Self::Id, who: &T::AccountId) -> DispatchResult {
		let mut locks = Freezes::<T, I>::get(who);
		locks.retain(|l| &l.id != id);
		Self::update_freezes(who, locks.as_bounded_slice())
	}
}

impl<T: Config<I>, I: 'static> fungible::Balanced<T::AccountId> for Pallet<T, I> {
	type OnDropCredit = fungible::DecreaseIssuance<T::AccountId, Self>;
	type OnDropDebt = fungible::IncreaseIssuance<T::AccountId, Self>;
}

impl<T: Config<I>, I: 'static> fungible::BalancedHold<T::AccountId> for Pallet<T, I> {}

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
