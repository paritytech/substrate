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

//! Functions for the Assets pallet.

use super::*;
use frame_support::{defensive, traits::Get, BoundedVec};

#[must_use]
pub(super) enum DeadConsequence {
	Remove,
	Keep,
}

use DeadConsequence::*;

// The main implementation block for the module.
impl<T: Config<I>, I: 'static> Pallet<T, I> {
	// Public immutables

	/// Return the extra "sid-car" data for `id`/`who`, or `None` if the account doesn't exist.
	pub fn adjust_extra(
		id: T::AssetId,
		who: impl sp_std::borrow::Borrow<T::AccountId>,
	) -> Option<ExtraMutator<T, I>> {
		ExtraMutator::maybe_new(id, who)
	}

	/// Get the asset `id` balance of `who`, or zero if the asset-account doesn't exist.
	pub fn balance(id: T::AssetId, who: impl sp_std::borrow::Borrow<T::AccountId>) -> T::Balance {
		Self::maybe_balance(id, who).unwrap_or_default()
	}

	/// Get the asset `id` balance of `who` if the asset-account exists.
	pub fn maybe_balance(
		id: T::AssetId,
		who: impl sp_std::borrow::Borrow<T::AccountId>,
	) -> Option<T::Balance> {
		Account::<T, I>::get(id, who.borrow()).map(|a| a.balance)
	}

	/// Get the total supply of an asset `id`.
	pub fn total_supply(id: T::AssetId) -> T::Balance {
		Self::maybe_total_supply(id).unwrap_or_default()
	}

	/// Get the total supply of an asset `id` if the asset exists.
	pub fn maybe_total_supply(id: T::AssetId) -> Option<T::Balance> {
		Asset::<T, I>::get(id).map(|x| x.supply)
	}

	pub(super) fn new_account(
		who: &T::AccountId,
		d: &mut AssetDetails<T::Balance, T::AccountId, DepositBalanceOf<T, I>>,
		maybe_deposit: Option<(&T::AccountId, DepositBalanceOf<T, I>)>,
	) -> Result<ExistenceReasonOf<T, I>, DispatchError> {
		let accounts = d.accounts.checked_add(1).ok_or(ArithmeticError::Overflow)?;
		let reason = if let Some((depositor, deposit)) = maybe_deposit {
			if depositor == who {
				ExistenceReason::DepositHeld(deposit)
			} else {
				ExistenceReason::DepositFrom(depositor.clone(), deposit)
			}
		} else if d.is_sufficient {
			frame_system::Pallet::<T>::inc_sufficients(who);
			d.sufficients += 1;
			ExistenceReason::Sufficient
		} else {
			frame_system::Pallet::<T>::inc_consumers(who)
				.map_err(|_| Error::<T, I>::UnavailableConsumer)?;
			// We ensure that we can still increment consumers once more because we could otherwise
			// allow accidental usage of all consumer references which could cause grief.
			if !frame_system::Pallet::<T>::can_inc_consumer(who) {
				frame_system::Pallet::<T>::dec_consumers(who);
				return Err(Error::<T, I>::UnavailableConsumer.into())
			}
			ExistenceReason::Consumer
		};
		d.accounts = accounts;
		Ok(reason)
	}

	pub(super) fn dead_account(
		who: &T::AccountId,
		d: &mut AssetDetails<T::Balance, T::AccountId, DepositBalanceOf<T, I>>,
		reason: &ExistenceReasonOf<T, I>,
		force: bool,
	) -> DeadConsequence {
		use ExistenceReason::*;
		match *reason {
			Consumer => frame_system::Pallet::<T>::dec_consumers(who),
			Sufficient => {
				d.sufficients = d.sufficients.saturating_sub(1);
				frame_system::Pallet::<T>::dec_sufficients(who);
			},
			DepositRefunded => {},
			DepositHeld(_) | DepositFrom(..) if !force => return Keep,
			DepositHeld(_) | DepositFrom(..) => {},
		}
		d.accounts = d.accounts.saturating_sub(1);
		Remove
	}

	/// Returns `true` when the balance of `account` can be increased by `amount`.
	///
	/// - `id`: The id of the asset that should be increased.
	/// - `who`: The account of which the balance should be increased.
	/// - `amount`: The amount by which the balance should be increased.
	/// - `increase_supply`: Will the supply of the asset be increased by `amount` at the same time
	///   as crediting the `account`.
	pub(super) fn can_increase(
		id: T::AssetId,
		who: &T::AccountId,
		amount: T::Balance,
		increase_supply: bool,
	) -> DepositConsequence {
		let details = match Asset::<T, I>::get(&id) {
			Some(details) => details,
			None => return DepositConsequence::UnknownAsset,
		};
		if increase_supply && details.supply.checked_add(&amount).is_none() {
			return DepositConsequence::Overflow
		}
		if let Some(account) = Account::<T, I>::get(id, who) {
			if account.status.is_blocked() {
				return DepositConsequence::Blocked
			}
			if account.balance.checked_add(&amount).is_none() {
				return DepositConsequence::Overflow
			}
		} else {
			if amount < details.min_balance {
				return DepositConsequence::BelowMinimum
			}
			if !details.is_sufficient && !frame_system::Pallet::<T>::can_accrue_consumers(who, 2) {
				return DepositConsequence::CannotCreate
			}
			if details.is_sufficient && details.sufficients.checked_add(1).is_none() {
				return DepositConsequence::Overflow
			}
		}

		DepositConsequence::Success
	}

	/// Return the consequence of a withdraw.
	pub(super) fn can_decrease(
		id: T::AssetId,
		who: &T::AccountId,
		amount: T::Balance,
		keep_alive: bool,
	) -> WithdrawConsequence<T::Balance> {
		use WithdrawConsequence::*;
		let details = match Asset::<T, I>::get(&id) {
			Some(details) => details,
			None => return UnknownAsset,
		};
		if details.supply.checked_sub(&amount).is_none() {
			return Underflow
		}
		if details.status == AssetStatus::Frozen {
			return Frozen
		}
		if amount.is_zero() {
			return Success
		}
		let account = match Account::<T, I>::get(&id, who) {
			Some(a) => a,
			None => return BalanceLow,
		};
		if account.status.is_frozen() {
			return Frozen
		}
		if let Some(rest) = account.balance.checked_sub(&amount) {
			if let Some(frozen) = T::Freezer::frozen_balance(id.clone(), who) {
				match frozen.checked_add(&details.min_balance) {
					Some(required) if rest < required => return Frozen,
					None => return Overflow,
					_ => {},
				}
			}

			if rest < details.min_balance {
				if keep_alive {
					WouldDie
				} else {
					ReducedToZero(rest)
				}
			} else {
				Success
			}
		} else {
			BalanceLow
		}
	}

	// Maximum `amount` that can be passed into `can_withdraw` to result in a `WithdrawConsequence`
	// of `Success`.
	pub(super) fn reducible_balance(
		id: T::AssetId,
		who: &T::AccountId,
		keep_alive: bool,
	) -> Result<T::Balance, DispatchError> {
		let details = Asset::<T, I>::get(&id).ok_or(Error::<T, I>::Unknown)?;
		ensure!(details.status == AssetStatus::Live, Error::<T, I>::AssetNotLive);

		let account = Account::<T, I>::get(&id, who).ok_or(Error::<T, I>::NoAccount)?;
		ensure!(!account.status.is_frozen(), Error::<T, I>::Frozen);

		let amount = if let Some(frozen) = T::Freezer::frozen_balance(id, who) {
			// Frozen balance: account CANNOT be deleted
			let required =
				frozen.checked_add(&details.min_balance).ok_or(ArithmeticError::Overflow)?;
			account.balance.saturating_sub(required)
		} else {
			if keep_alive {
				// We want to keep the account around.
				account.balance.saturating_sub(details.min_balance)
			} else {
				// Don't care if the account dies
				account.balance
			}
		};
		Ok(amount.min(details.supply))
	}

	/// Make preparatory checks for debiting some funds from an account. Flags indicate requirements
	/// of the debit.
	///
	/// - `amount`: The amount desired to be debited. The actual amount returned for debit may be
	///   less (in the case of `best_effort` being `true`) or greater by up to the minimum balance
	///   less one.
	/// - `keep_alive`: Require that `target` must stay alive.
	/// - `respect_freezer`: Respect any freezes on the account or token (or not).
	/// - `best_effort`: The debit amount may be less than `amount`.
	///
	/// On success, the amount which should be debited (this will always be at least `amount` unless
	/// `best_effort` is `true`) together with an optional value indicating the argument which must
	/// be passed into the `melted` function of the `T::Freezer` if `Some`.
	///
	/// If no valid debit can be made then return an `Err`.
	pub(super) fn prep_debit(
		id: T::AssetId,
		target: &T::AccountId,
		amount: T::Balance,
		f: DebitFlags,
	) -> Result<T::Balance, DispatchError> {
		let actual = Self::reducible_balance(id.clone(), target, f.keep_alive)?.min(amount);
		ensure!(f.best_effort || actual >= amount, Error::<T, I>::BalanceLow);

		let conseq = Self::can_decrease(id, target, actual, f.keep_alive);
		let actual = match conseq.into_result(f.keep_alive) {
			Ok(dust) => actual.saturating_add(dust), //< guaranteed by reducible_balance
			Err(e) => {
				debug_assert!(false, "passed from reducible_balance; qed");
				return Err(e)
			},
		};

		Ok(actual)
	}

	/// Make preparatory checks for crediting some funds from an account. Flags indicate
	/// requirements of the credit.
	///
	/// - `amount`: The amount desired to be credited.
	/// - `debit`: The amount by which some other account has been debited. If this is greater than
	///   `amount`, then the `burn_dust` parameter takes effect.
	/// - `burn_dust`: Indicates that in the case of debit being greater than amount, the additional
	///   (dust) value should be burned, rather than credited.
	///
	/// On success, the amount which should be credited (this will always be at least `amount`)
	/// together with an optional value indicating the value which should be burned. The latter
	/// will always be `None` as long as `burn_dust` is `false` or `debit` is no greater than
	/// `amount`.
	///
	/// If no valid credit can be made then return an `Err`.
	pub(super) fn prep_credit(
		id: T::AssetId,
		dest: &T::AccountId,
		amount: T::Balance,
		debit: T::Balance,
		burn_dust: bool,
	) -> Result<(T::Balance, Option<T::Balance>), DispatchError> {
		let (credit, maybe_burn) = match (burn_dust, debit.checked_sub(&amount)) {
			(true, Some(dust)) => (amount, Some(dust)),
			_ => (debit, None),
		};
		Self::can_increase(id, dest, credit, false).into_result()?;
		Ok((credit, maybe_burn))
	}

	/// Creates an account for `who` to hold asset `id` with a zero balance and takes a deposit.
	///
	/// When `check_depositor` is set to true, the depositor must be either the asset's Admin or
	/// Freezer, otherwise the depositor can be any account.
	pub(super) fn do_touch(
		id: T::AssetId,
		who: T::AccountId,
		depositor: T::AccountId,
		check_depositor: bool,
	) -> DispatchResult {
		ensure!(!Account::<T, I>::contains_key(&id, &who), Error::<T, I>::AlreadyExists);
		let deposit = T::AssetAccountDeposit::get();
		let mut details = Asset::<T, I>::get(&id).ok_or(Error::<T, I>::Unknown)?;
		ensure!(details.status == AssetStatus::Live, Error::<T, I>::AssetNotLive);
		ensure!(
			!check_depositor || &depositor == &details.admin || &depositor == &details.freezer,
			Error::<T, I>::NoPermission
		);
		let reason = Self::new_account(&who, &mut details, Some((&depositor, deposit)))?;
		T::Currency::reserve(&depositor, deposit)?;
		Asset::<T, I>::insert(&id, details);
		Account::<T, I>::insert(
			&id,
			&who,
			AssetAccountOf::<T, I> {
				balance: Zero::zero(),
				status: AccountStatus::Liquid,
				reason,
				extra: T::Extra::default(),
			},
		);
		Self::deposit_event(Event::Touched { asset_id: id, who, depositor });
		Ok(())
	}

	/// Returns a deposit or a consumer reference, destroying an asset-account.
	/// Non-zero balance accounts refunded and destroyed only if `allow_burn` is true.
	pub(super) fn do_refund(id: T::AssetId, who: T::AccountId, allow_burn: bool) -> DispatchResult {
		use AssetStatus::*;
		use ExistenceReason::*;
		let mut account = Account::<T, I>::get(&id, &who).ok_or(Error::<T, I>::NoDeposit)?;
		ensure!(matches!(account.reason, Consumer | DepositHeld(..)), Error::<T, I>::NoDeposit);
		let mut details = Asset::<T, I>::get(&id).ok_or(Error::<T, I>::Unknown)?;
		ensure!(matches!(details.status, Live | Frozen), Error::<T, I>::IncorrectStatus);
		ensure!(account.balance.is_zero() || allow_burn, Error::<T, I>::WouldBurn);

		if let Some(deposit) = account.reason.take_deposit() {
			T::Currency::unreserve(&who, deposit);
		}

		if let Remove = Self::dead_account(&who, &mut details, &account.reason, false) {
			Account::<T, I>::remove(&id, &who);
		} else {
			debug_assert!(false, "refund did not result in dead account?!");
			// deposit may have been refunded, need to update `Account`
			Account::<T, I>::insert(id, &who, account);
			return Ok(())
		}
		Asset::<T, I>::insert(&id, details);
		// Executing a hook here is safe, since it is not in a `mutate`.
		T::Freezer::died(id, &who);
		Ok(())
	}

	/// Returns a `DepositFrom` of an account only if balance is zero.
	pub(super) fn do_refund_other(
		id: T::AssetId,
		who: &T::AccountId,
		caller: &T::AccountId,
	) -> DispatchResult {
		let mut account = Account::<T, I>::get(&id, &who).ok_or(Error::<T, I>::NoDeposit)?;
		let (depositor, deposit) =
			account.reason.take_deposit_from().ok_or(Error::<T, I>::NoDeposit)?;
		let mut details = Asset::<T, I>::get(&id).ok_or(Error::<T, I>::Unknown)?;
		ensure!(details.status == AssetStatus::Live, Error::<T, I>::AssetNotLive);
		ensure!(!account.status.is_frozen(), Error::<T, I>::Frozen);
		ensure!(caller == &depositor || caller == &details.admin, Error::<T, I>::NoPermission);
		ensure!(account.balance.is_zero(), Error::<T, I>::WouldBurn);

		T::Currency::unreserve(&depositor, deposit);

		if let Remove = Self::dead_account(&who, &mut details, &account.reason, false) {
			Account::<T, I>::remove(&id, &who);
		} else {
			debug_assert!(false, "refund did not result in dead account?!");
			// deposit may have been refunded, need to update `Account`
			Account::<T, I>::insert(&id, &who, account);
			return Ok(())
		}
		Asset::<T, I>::insert(&id, details);
		// Executing a hook here is safe, since it is not in a `mutate`.
		T::Freezer::died(id, &who);
		return Ok(())
	}

	/// Increases the asset `id` balance of `beneficiary` by `amount`.
	///
	/// This alters the registered supply of the asset and emits an event.
	///
	/// Will return an error or will increase the amount by exactly `amount`.
	pub(super) fn do_mint(
		id: T::AssetId,
		beneficiary: &T::AccountId,
		amount: T::Balance,
		maybe_check_issuer: Option<T::AccountId>,
	) -> DispatchResult {
		Self::increase_balance(id.clone(), beneficiary, amount, |details| -> DispatchResult {
			if let Some(check_issuer) = maybe_check_issuer {
				ensure!(check_issuer == details.issuer, Error::<T, I>::NoPermission);
			}
			debug_assert!(details.supply.checked_add(&amount).is_some(), "checked in prep; qed");

			details.supply = details.supply.saturating_add(amount);

			Ok(())
		})?;

		Self::deposit_event(Event::Issued { asset_id: id, owner: beneficiary.clone(), amount });

		Ok(())
	}

	/// Increases the asset `id` balance of `beneficiary` by `amount`.
	///
	/// LOW-LEVEL: Does not alter the supply of asset or emit an event. Use `do_mint` if you need
	/// that. This is not intended to be used alone.
	///
	/// Will return an error or will increase the amount by exactly `amount`.
	pub(super) fn increase_balance(
		id: T::AssetId,
		beneficiary: &T::AccountId,
		amount: T::Balance,
		check: impl FnOnce(
			&mut AssetDetails<T::Balance, T::AccountId, DepositBalanceOf<T, I>>,
		) -> DispatchResult,
	) -> DispatchResult {
		if amount.is_zero() {
			return Ok(())
		}

		Self::can_increase(id.clone(), beneficiary, amount, true).into_result()?;
		Asset::<T, I>::try_mutate(&id, |maybe_details| -> DispatchResult {
			let details = maybe_details.as_mut().ok_or(Error::<T, I>::Unknown)?;
			ensure!(details.status == AssetStatus::Live, Error::<T, I>::AssetNotLive);
			check(details)?;

			Account::<T, I>::try_mutate(&id, beneficiary, |maybe_account| -> DispatchResult {
				match maybe_account {
					Some(ref mut account) => {
						account.balance.saturating_accrue(amount);
					},
					maybe_account @ None => {
						// Note this should never fail as it's already checked by
						// `can_increase`.
						ensure!(amount >= details.min_balance, TokenError::BelowMinimum);
						*maybe_account = Some(AssetAccountOf::<T, I> {
							balance: amount,
							reason: Self::new_account(beneficiary, details, None)?,
							status: AccountStatus::Liquid,
							extra: T::Extra::default(),
						});
					},
				}
				Ok(())
			})?;
			Ok(())
		})?;
		Ok(())
	}

	/// Reduces asset `id` balance of `target` by `amount`. Flags `f` can be given to alter whether
	/// it attempts a `best_effort` or makes sure to `keep_alive` the account.
	///
	/// This alters the registered supply of the asset and emits an event.
	///
	/// Will return an error and do nothing or will decrease the amount and return the amount
	/// reduced by.
	pub(super) fn do_burn(
		id: T::AssetId,
		target: &T::AccountId,
		amount: T::Balance,
		maybe_check_admin: Option<T::AccountId>,
		f: DebitFlags,
	) -> Result<T::Balance, DispatchError> {
		let d = Asset::<T, I>::get(&id).ok_or(Error::<T, I>::Unknown)?;
		ensure!(
			d.status == AssetStatus::Live || d.status == AssetStatus::Frozen,
			Error::<T, I>::AssetNotLive
		);

		let actual = Self::decrease_balance(id.clone(), target, amount, f, |actual, details| {
			// Check admin rights.
			if let Some(check_admin) = maybe_check_admin {
				ensure!(check_admin == details.admin, Error::<T, I>::NoPermission);
			}

			debug_assert!(details.supply >= actual, "checked in prep; qed");
			details.supply = details.supply.saturating_sub(actual);

			Ok(())
		})?;
		Self::deposit_event(Event::Burned { asset_id: id, owner: target.clone(), balance: actual });
		Ok(actual)
	}

	/// Reduces asset `id` balance of `target` by `amount`. Flags `f` can be given to alter whether
	/// it attempts a `best_effort` or makes sure to `keep_alive` the account.
	///
	/// LOW-LEVEL: Does not alter the supply of asset or emit an event. Use `do_burn` if you need
	/// that. This is not intended to be used alone.
	///
	/// Will return an error and do nothing or will decrease the amount and return the amount
	/// reduced by.
	pub(super) fn decrease_balance(
		id: T::AssetId,
		target: &T::AccountId,
		amount: T::Balance,
		f: DebitFlags,
		check: impl FnOnce(
			T::Balance,
			&mut AssetDetails<T::Balance, T::AccountId, DepositBalanceOf<T, I>>,
		) -> DispatchResult,
	) -> Result<T::Balance, DispatchError> {
		if amount.is_zero() {
			return Ok(amount)
		}

		let details = Asset::<T, I>::get(&id).ok_or(Error::<T, I>::Unknown)?;
		ensure!(details.status == AssetStatus::Live, Error::<T, I>::AssetNotLive);

		let actual = Self::prep_debit(id.clone(), target, amount, f)?;
		let mut target_died: Option<DeadConsequence> = None;

		Asset::<T, I>::try_mutate(&id, |maybe_details| -> DispatchResult {
			let details = maybe_details.as_mut().ok_or(Error::<T, I>::Unknown)?;
			check(actual, details)?;

			Account::<T, I>::try_mutate(&id, target, |maybe_account| -> DispatchResult {
				let mut account = maybe_account.take().ok_or(Error::<T, I>::NoAccount)?;
				debug_assert!(account.balance >= actual, "checked in prep; qed");

				// Make the debit.
				account.balance = account.balance.saturating_sub(actual);
				if account.balance < details.min_balance {
					debug_assert!(account.balance.is_zero(), "checked in prep; qed");
					target_died = Some(Self::dead_account(target, details, &account.reason, false));
					if let Some(Remove) = target_died {
						return Ok(())
					}
				};
				*maybe_account = Some(account);
				Ok(())
			})?;

			Ok(())
		})?;

		// Execute hook outside of `mutate`.
		if let Some(Remove) = target_died {
			T::Freezer::died(id, target);
		}
		Ok(actual)
	}

	/// Reduces the asset `id` balance of `source` by some `amount` and increases the balance of
	/// `dest` by (similar) amount.
	///
	/// Returns the actual amount placed into `dest`. Exact semantics are determined by the flags
	/// `f`.
	///
	/// Will fail if the amount transferred is so small that it cannot create the destination due
	/// to minimum balance requirements.
	pub(super) fn do_transfer(
		id: T::AssetId,
		source: &T::AccountId,
		dest: &T::AccountId,
		amount: T::Balance,
		maybe_need_admin: Option<T::AccountId>,
		f: TransferFlags,
	) -> Result<T::Balance, DispatchError> {
		let (balance, died) =
			Self::transfer_and_die(id.clone(), source, dest, amount, maybe_need_admin, f)?;
		if let Some(Remove) = died {
			T::Freezer::died(id, source);
		}
		Ok(balance)
	}

	/// Same as `do_transfer` but it does not execute the `FrozenBalance::died` hook and
	/// instead returns whether and how the `source` account died in this operation.
	fn transfer_and_die(
		id: T::AssetId,
		source: &T::AccountId,
		dest: &T::AccountId,
		amount: T::Balance,
		maybe_need_admin: Option<T::AccountId>,
		f: TransferFlags,
	) -> Result<(T::Balance, Option<DeadConsequence>), DispatchError> {
		// Early exit if no-op.
		if amount.is_zero() {
			return Ok((amount, None))
		}
		let details = Asset::<T, I>::get(&id).ok_or(Error::<T, I>::Unknown)?;
		ensure!(details.status == AssetStatus::Live, Error::<T, I>::AssetNotLive);

		// Figure out the debit and credit, together with side-effects.
		let debit = Self::prep_debit(id.clone(), source, amount, f.into())?;
		let (credit, maybe_burn) = Self::prep_credit(id.clone(), dest, amount, debit, f.burn_dust)?;

		let mut source_account =
			Account::<T, I>::get(&id, &source).ok_or(Error::<T, I>::NoAccount)?;
		let mut source_died: Option<DeadConsequence> = None;

		Asset::<T, I>::try_mutate(&id, |maybe_details| -> DispatchResult {
			let details = maybe_details.as_mut().ok_or(Error::<T, I>::Unknown)?;

			// Check admin rights.
			if let Some(need_admin) = maybe_need_admin {
				ensure!(need_admin == details.admin, Error::<T, I>::NoPermission);
			}

			// Skip if source == dest
			if source == dest {
				return Ok(())
			}

			// Burn any dust if needed.
			if let Some(burn) = maybe_burn {
				// Debit dust from supply; this will not saturate since it's already checked in
				// prep.
				debug_assert!(details.supply >= burn, "checked in prep; qed");
				details.supply = details.supply.saturating_sub(burn);
			}

			// Debit balance from source; this will not saturate since it's already checked in prep.
			debug_assert!(source_account.balance >= debit, "checked in prep; qed");
			source_account.balance = source_account.balance.saturating_sub(debit);

			Account::<T, I>::try_mutate(&id, &dest, |maybe_account| -> DispatchResult {
				match maybe_account {
					Some(ref mut account) => {
						// Calculate new balance; this will not saturate since it's already checked
						// in prep.
						debug_assert!(
							account.balance.checked_add(&credit).is_some(),
							"checked in prep; qed"
						);
						account.balance.saturating_accrue(credit);
					},
					maybe_account @ None => {
						*maybe_account = Some(AssetAccountOf::<T, I> {
							balance: credit,
							status: AccountStatus::Liquid,
							reason: Self::new_account(dest, details, None)?,
							extra: T::Extra::default(),
						});
					},
				}
				Ok(())
			})?;

			// Remove source account if it's now dead.
			if source_account.balance < details.min_balance {
				debug_assert!(source_account.balance.is_zero(), "checked in prep; qed");
				source_died =
					Some(Self::dead_account(source, details, &source_account.reason, false));
				if let Some(Remove) = source_died {
					Account::<T, I>::remove(&id, &source);
					return Ok(())
				}
			}
			Account::<T, I>::insert(&id, &source, &source_account);
			Ok(())
		})?;

		Self::deposit_event(Event::Transferred {
			asset_id: id,
			from: source.clone(),
			to: dest.clone(),
			amount: credit,
		});
		Ok((credit, source_died))
	}

	/// Create a new asset without taking a deposit.
	///
	/// * `id`: The `AssetId` you want the new asset to have. Must not already be in use.
	/// * `owner`: The owner, issuer, admin, and freezer of this asset upon creation.
	/// * `is_sufficient`: Whether this asset needs users to have an existential deposit to hold
	///   this asset.
	/// * `min_balance`: The minimum balance a user is allowed to have of this asset before they are
	///   considered dust and cleaned up.
	pub(super) fn do_force_create(
		id: T::AssetId,
		owner: T::AccountId,
		is_sufficient: bool,
		min_balance: T::Balance,
	) -> DispatchResult {
		ensure!(!Asset::<T, I>::contains_key(&id), Error::<T, I>::InUse);
		ensure!(!min_balance.is_zero(), Error::<T, I>::MinBalanceZero);

		Asset::<T, I>::insert(
			&id,
			AssetDetails {
				owner: owner.clone(),
				issuer: owner.clone(),
				admin: owner.clone(),
				freezer: owner.clone(),
				supply: Zero::zero(),
				deposit: Zero::zero(),
				min_balance,
				is_sufficient,
				accounts: 0,
				sufficients: 0,
				approvals: 0,
				status: AssetStatus::Live,
			},
		);
		ensure!(T::CallbackHandle::created(&id, &owner).is_ok(), Error::<T, I>::CallbackFailed);
		Self::deposit_event(Event::ForceCreated { asset_id: id, owner: owner.clone() });
		Ok(())
	}

	/// Start the process of destroying an asset, by setting the asset status to `Destroying`, and
	/// emitting the `DestructionStarted` event.
	pub(super) fn do_start_destroy(
		id: T::AssetId,
		maybe_check_owner: Option<T::AccountId>,
	) -> DispatchResult {
		Asset::<T, I>::try_mutate_exists(id.clone(), |maybe_details| -> Result<(), DispatchError> {
			let details = maybe_details.as_mut().ok_or(Error::<T, I>::Unknown)?;
			if let Some(check_owner) = maybe_check_owner {
				ensure!(details.owner == check_owner, Error::<T, I>::NoPermission);
			}
			details.status = AssetStatus::Destroying;

			Self::deposit_event(Event::DestructionStarted { asset_id: id });
			Ok(())
		})
	}

	/// Destroy accounts associated with a given asset up to the max (T::RemoveItemsLimit).
	///
	/// Each call emits the `Event::DestroyedAccounts` event.
	/// Returns the number of destroyed accounts.
	pub(super) fn do_destroy_accounts(
		id: T::AssetId,
		max_items: u32,
	) -> Result<u32, DispatchError> {
		let mut dead_accounts: Vec<T::AccountId> = vec![];
		let mut remaining_accounts = 0;
		let _ =
			Asset::<T, I>::try_mutate_exists(&id, |maybe_details| -> Result<(), DispatchError> {
				let mut details = maybe_details.as_mut().ok_or(Error::<T, I>::Unknown)?;
				// Should only destroy accounts while the asset is in a destroying state
				ensure!(details.status == AssetStatus::Destroying, Error::<T, I>::IncorrectStatus);
				for (i, (who, mut v)) in Account::<T, I>::iter_prefix(&id).enumerate() {
					// unreserve the existence deposit if any
					if let Some((depositor, deposit)) = v.reason.take_deposit_from() {
						T::Currency::unreserve(&depositor, deposit);
					} else if let Some(deposit) = v.reason.take_deposit() {
						T::Currency::unreserve(&who, deposit);
					}
					if let Remove = Self::dead_account(&who, &mut details, &v.reason, false) {
						Account::<T, I>::remove(&id, &who);
						dead_accounts.push(who);
					} else {
						// deposit may have been released, need to update `Account`
						Account::<T, I>::insert(&id, &who, v);
						defensive!("destroy did not result in dead account?!");
					}
					if i + 1 >= (max_items as usize) {
						break
					}
				}
				remaining_accounts = details.accounts;
				Ok(())
			})?;

		for who in &dead_accounts {
			T::Freezer::died(id.clone(), &who);
		}

		Self::deposit_event(Event::AccountsDestroyed {
			asset_id: id,
			accounts_destroyed: dead_accounts.len() as u32,
			accounts_remaining: remaining_accounts as u32,
		});
		Ok(dead_accounts.len() as u32)
	}

	/// Destroy approvals associated with a given asset up to the max (T::RemoveItemsLimit).
	///
	/// Each call emits the `Event::DestroyedApprovals` event
	/// Returns the number of destroyed approvals.
	pub(super) fn do_destroy_approvals(
		id: T::AssetId,
		max_items: u32,
	) -> Result<u32, DispatchError> {
		let mut removed_approvals = 0;
		let _ = Asset::<T, I>::try_mutate_exists(
			id.clone(),
			|maybe_details| -> Result<(), DispatchError> {
				let details = maybe_details.as_mut().ok_or(Error::<T, I>::Unknown)?;

				// Should only destroy accounts while the asset is in a destroying state.
				ensure!(details.status == AssetStatus::Destroying, Error::<T, I>::IncorrectStatus);

				for ((owner, _), approval) in Approvals::<T, I>::drain_prefix((id.clone(),)) {
					T::Currency::unreserve(&owner, approval.deposit);
					removed_approvals = removed_approvals.saturating_add(1);
					details.approvals = details.approvals.saturating_sub(1);
					if removed_approvals >= max_items {
						break
					}
				}
				Self::deposit_event(Event::ApprovalsDestroyed {
					asset_id: id,
					approvals_destroyed: removed_approvals as u32,
					approvals_remaining: details.approvals as u32,
				});
				Ok(())
			},
		)?;
		Ok(removed_approvals)
	}

	/// Complete destroying an asset and unreserve the deposit.
	///
	/// On success, the `Event::Destroyed` event is emitted.
	pub(super) fn do_finish_destroy(id: T::AssetId) -> DispatchResult {
		Asset::<T, I>::try_mutate_exists(id.clone(), |maybe_details| -> Result<(), DispatchError> {
			let details = maybe_details.take().ok_or(Error::<T, I>::Unknown)?;
			ensure!(details.status == AssetStatus::Destroying, Error::<T, I>::IncorrectStatus);
			ensure!(details.accounts == 0, Error::<T, I>::InUse);
			ensure!(details.approvals == 0, Error::<T, I>::InUse);
			ensure!(T::CallbackHandle::destroyed(&id).is_ok(), Error::<T, I>::CallbackFailed);

			let metadata = Metadata::<T, I>::take(&id);
			T::Currency::unreserve(
				&details.owner,
				details.deposit.saturating_add(metadata.deposit),
			);
			Self::deposit_event(Event::Destroyed { asset_id: id });

			Ok(())
		})
	}

	/// Creates an approval from `owner` to spend `amount` of asset `id` tokens by 'delegate'
	/// while reserving `T::ApprovalDeposit` from owner
	///
	/// If an approval already exists, the new amount is added to such existing approval
	pub(super) fn do_approve_transfer(
		id: T::AssetId,
		owner: &T::AccountId,
		delegate: &T::AccountId,
		amount: T::Balance,
	) -> DispatchResult {
		let mut d = Asset::<T, I>::get(&id).ok_or(Error::<T, I>::Unknown)?;
		ensure!(d.status == AssetStatus::Live, Error::<T, I>::AssetNotLive);
		Approvals::<T, I>::try_mutate(
			(id.clone(), &owner, &delegate),
			|maybe_approved| -> DispatchResult {
				let mut approved = match maybe_approved.take() {
					// an approval already exists and is being updated
					Some(a) => a,
					// a new approval is created
					None => {
						d.approvals.saturating_inc();
						Default::default()
					},
				};
				let deposit_required = T::ApprovalDeposit::get();
				if approved.deposit < deposit_required {
					T::Currency::reserve(owner, deposit_required - approved.deposit)?;
					approved.deposit = deposit_required;
				}
				approved.amount = approved.amount.saturating_add(amount);
				*maybe_approved = Some(approved);
				Ok(())
			},
		)?;
		Asset::<T, I>::insert(&id, d);
		Self::deposit_event(Event::ApprovedTransfer {
			asset_id: id,
			source: owner.clone(),
			delegate: delegate.clone(),
			amount,
		});

		Ok(())
	}

	/// Reduces the asset `id` balance of `owner` by some `amount` and increases the balance of
	/// `dest` by (similar) amount, checking that 'delegate' has an existing approval from `owner`
	/// to spend`amount`.
	///
	/// Will fail if `amount` is greater than the approval from `owner` to 'delegate'
	/// Will unreserve the deposit from `owner` if the entire approved `amount` is spent by
	/// 'delegate'
	pub(super) fn do_transfer_approved(
		id: T::AssetId,
		owner: &T::AccountId,
		delegate: &T::AccountId,
		destination: &T::AccountId,
		amount: T::Balance,
	) -> DispatchResult {
		let mut owner_died: Option<DeadConsequence> = None;

		let d = Asset::<T, I>::get(&id).ok_or(Error::<T, I>::Unknown)?;
		ensure!(d.status == AssetStatus::Live, Error::<T, I>::AssetNotLive);

		Approvals::<T, I>::try_mutate_exists(
			(id.clone(), &owner, delegate),
			|maybe_approved| -> DispatchResult {
				let mut approved = maybe_approved.take().ok_or(Error::<T, I>::Unapproved)?;
				let remaining =
					approved.amount.checked_sub(&amount).ok_or(Error::<T, I>::Unapproved)?;

				let f = TransferFlags { keep_alive: false, best_effort: false, burn_dust: false };
				owner_died =
					Self::transfer_and_die(id.clone(), owner, destination, amount, None, f)?.1;

				if remaining.is_zero() {
					T::Currency::unreserve(owner, approved.deposit);
					Asset::<T, I>::mutate(id.clone(), |maybe_details| {
						if let Some(details) = maybe_details {
							details.approvals.saturating_dec();
						}
					});
				} else {
					approved.amount = remaining;
					*maybe_approved = Some(approved);
				}
				Ok(())
			},
		)?;

		// Execute hook outside of `mutate`.
		if let Some(Remove) = owner_died {
			T::Freezer::died(id, owner);
		}
		Ok(())
	}

	/// Do set metadata
	pub(super) fn do_set_metadata(
		id: T::AssetId,
		from: &T::AccountId,
		name: Vec<u8>,
		symbol: Vec<u8>,
		decimals: u8,
	) -> DispatchResult {
		let bounded_name: BoundedVec<u8, T::StringLimit> =
			name.clone().try_into().map_err(|_| Error::<T, I>::BadMetadata)?;
		let bounded_symbol: BoundedVec<u8, T::StringLimit> =
			symbol.clone().try_into().map_err(|_| Error::<T, I>::BadMetadata)?;

		let d = Asset::<T, I>::get(&id).ok_or(Error::<T, I>::Unknown)?;
		ensure!(d.status == AssetStatus::Live, Error::<T, I>::AssetNotLive);
		ensure!(from == &d.owner, Error::<T, I>::NoPermission);

		Metadata::<T, I>::try_mutate_exists(id.clone(), |metadata| {
			ensure!(metadata.as_ref().map_or(true, |m| !m.is_frozen), Error::<T, I>::NoPermission);

			let old_deposit = metadata.take().map_or(Zero::zero(), |m| m.deposit);
			let new_deposit = Self::calc_metadata_deposit(&name, &symbol);

			if new_deposit > old_deposit {
				T::Currency::reserve(from, new_deposit - old_deposit)?;
			} else {
				T::Currency::unreserve(from, old_deposit - new_deposit);
			}

			*metadata = Some(AssetMetadata {
				deposit: new_deposit,
				name: bounded_name,
				symbol: bounded_symbol,
				decimals,
				is_frozen: false,
			});

			Self::deposit_event(Event::MetadataSet {
				asset_id: id,
				name,
				symbol,
				decimals,
				is_frozen: false,
			});
			Ok(())
		})
	}

	/// Calculate the metadata deposit for the provided data.
	pub(super) fn calc_metadata_deposit(name: &[u8], symbol: &[u8]) -> DepositBalanceOf<T, I> {
		T::MetadataDepositPerByte::get()
			.saturating_mul(((name.len() + symbol.len()) as u32).into())
			.saturating_add(T::MetadataDepositBase::get())
	}

	/// Returns all the non-zero balances for all assets of the given `account`.
	pub fn account_balances(account: T::AccountId) -> Vec<(T::AssetId, T::Balance)> {
		Asset::<T, I>::iter_keys()
			.filter_map(|id| {
				Self::maybe_balance(id.clone(), account.clone()).map(|balance| (id, balance))
			})
			.collect::<Vec<_>>()
	}
}
