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

//! Functions for the Assets pallet.

use super::*;
use frame_support::{traits::Get, BoundedVec};

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
		Asset::<T, I>::get(id).map(|x| x.supply).unwrap_or_else(Zero::zero)
	}

	pub(super) fn new_account(
		who: &T::AccountId,
		d: &mut AssetDetails<T::Balance, T::AccountId, DepositBalanceOf<T, I>>,
		maybe_deposit: Option<DepositBalanceOf<T, I>>,
	) -> Result<ExistenceReason<DepositBalanceOf<T, I>>, DispatchError> {
		let accounts = d.accounts.checked_add(1).ok_or(ArithmeticError::Overflow)?;
		let reason = if let Some(deposit) = maybe_deposit {
			ExistenceReason::DepositHeld(deposit)
		} else if d.is_sufficient {
			frame_system::Pallet::<T>::inc_sufficients(who);
			d.sufficients += 1;
			ExistenceReason::Sufficient
		} else {
			frame_system::Pallet::<T>::inc_consumers(who).map_err(|_| Error::<T, I>::NoProvider)?;
			ExistenceReason::Consumer
		};
		d.accounts = accounts;
		Ok(reason)
	}

	pub(super) fn dead_account(
		what: T::AssetId,
		who: &T::AccountId,
		d: &mut AssetDetails<T::Balance, T::AccountId, DepositBalanceOf<T, I>>,
		reason: &ExistenceReason<DepositBalanceOf<T, I>>,
		force: bool,
	) -> DeadConsequence {
		let mut result = Remove;
		match *reason {
			ExistenceReason::Consumer => frame_system::Pallet::<T>::dec_consumers(who),
			ExistenceReason::Sufficient => {
				d.sufficients = d.sufficients.saturating_sub(1);
				frame_system::Pallet::<T>::dec_sufficients(who);
			},
			ExistenceReason::DepositRefunded => {},
			ExistenceReason::DepositHeld(_) if !force => return Keep,
			ExistenceReason::DepositHeld(_) => result = Keep,
		}
		d.accounts = d.accounts.saturating_sub(1);
		T::Freezer::died(what, who);
		result
	}

	pub(super) fn can_increase(
		id: T::AssetId,
		who: &T::AccountId,
		amount: T::Balance,
	) -> DepositConsequence {
		let details = match Asset::<T, I>::get(id) {
			Some(details) => details,
			None => return DepositConsequence::UnknownAsset,
		};
		if details.supply.checked_add(&amount).is_none() {
			return DepositConsequence::Overflow
		}
		if let Some(balance) = Self::maybe_balance(id, who) {
			if balance.checked_add(&amount).is_none() {
				return DepositConsequence::Overflow
			}
		} else {
			if amount < details.min_balance {
				return DepositConsequence::BelowMinimum
			}
			if !details.is_sufficient && !frame_system::Pallet::<T>::can_inc_consumer(who) {
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
		let details = match Asset::<T, I>::get(id) {
			Some(details) => details,
			None => return UnknownAsset,
		};
		if details.supply.checked_sub(&amount).is_none() {
			return Underflow
		}
		if details.is_frozen {
			return Frozen
		}
		if amount.is_zero() {
			return Success
		}
		let account = match Account::<T, I>::get(id, who) {
			Some(a) => a,
			None => return NoFunds,
		};
		if account.is_frozen {
			return Frozen
		}
		if let Some(rest) = account.balance.checked_sub(&amount) {
			if let Some(frozen) = T::Freezer::frozen_balance(id, who) {
				match frozen.checked_add(&details.min_balance) {
					Some(required) if rest < required => return Frozen,
					None => return Overflow,
					_ => {},
				}
			}

			let is_provider = false;
			let is_required = is_provider && !frame_system::Pallet::<T>::can_dec_provider(who);
			let must_keep_alive = keep_alive || is_required;

			if rest < details.min_balance {
				if must_keep_alive {
					WouldDie
				} else {
					ReducedToZero(rest)
				}
			} else {
				Success
			}
		} else {
			NoFunds
		}
	}

	// Maximum `amount` that can be passed into `can_withdraw` to result in a `WithdrawConsequence`
	// of `Success`.
	pub(super) fn reducible_balance(
		id: T::AssetId,
		who: &T::AccountId,
		keep_alive: bool,
	) -> Result<T::Balance, DispatchError> {
		let details = Asset::<T, I>::get(id).ok_or_else(|| Error::<T, I>::Unknown)?;
		ensure!(!details.is_frozen, Error::<T, I>::Frozen);

		let account = Account::<T, I>::get(id, who).ok_or(Error::<T, I>::NoAccount)?;
		ensure!(!account.is_frozen, Error::<T, I>::Frozen);

		let amount = if let Some(frozen) = T::Freezer::frozen_balance(id, who) {
			// Frozen balance: account CANNOT be deleted
			let required =
				frozen.checked_add(&details.min_balance).ok_or(ArithmeticError::Overflow)?;
			account.balance.saturating_sub(required)
		} else {
			let is_provider = false;
			let is_required = is_provider && !frame_system::Pallet::<T>::can_dec_provider(who);
			if keep_alive || is_required {
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
		let actual = Self::reducible_balance(id, target, f.keep_alive)?.min(amount);
		ensure!(f.best_effort || actual >= amount, Error::<T, I>::BalanceLow);

		let conseq = Self::can_decrease(id, target, actual, f.keep_alive);
		let actual = match conseq.into_result() {
			Ok(dust) => actual.saturating_add(dust), //< guaranteed by reducible_balance
			Err(e) => {
				debug_assert!(false, "passed from reducible_balance; qed");
				return Err(e.into())
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
		Self::can_increase(id, &dest, credit).into_result()?;
		Ok((credit, maybe_burn))
	}

	/// Creates a account for `who` to hold asset `id` with a zero balance and takes a deposit.
	pub(super) fn do_touch(id: T::AssetId, who: T::AccountId) -> DispatchResult {
		ensure!(!Account::<T, I>::contains_key(id, &who), Error::<T, I>::AlreadyExists);
		let deposit = T::AssetAccountDeposit::get();
		let mut details = Asset::<T, I>::get(&id).ok_or(Error::<T, I>::Unknown)?;
		let reason = Self::new_account(&who, &mut details, Some(deposit))?;
		T::Currency::reserve(&who, deposit)?;
		Asset::<T, I>::insert(&id, details);
		Account::<T, I>::insert(
			id,
			&who,
			AssetAccountOf::<T, I> {
				balance: Zero::zero(),
				is_frozen: false,
				reason,
				extra: T::Extra::default(),
			},
		);
		Ok(())
	}

	/// Returns a deposit, destroying an asset-account.
	pub(super) fn do_refund(id: T::AssetId, who: T::AccountId, allow_burn: bool) -> DispatchResult {
		let mut account = Account::<T, I>::get(id, &who).ok_or(Error::<T, I>::NoDeposit)?;
		let deposit = account.reason.take_deposit().ok_or(Error::<T, I>::NoDeposit)?;
		let mut details = Asset::<T, I>::get(&id).ok_or(Error::<T, I>::Unknown)?;

		ensure!(account.balance.is_zero() || allow_burn, Error::<T, I>::WouldBurn);
		ensure!(!details.is_frozen, Error::<T, I>::Frozen);
		ensure!(!account.is_frozen, Error::<T, I>::Frozen);

		T::Currency::unreserve(&who, deposit);

		if let Remove = Self::dead_account(id, &who, &mut details, &account.reason, false) {
			Account::<T, I>::remove(id, &who);
		} else {
			debug_assert!(false, "refund did not result in dead account?!");
		}
		Asset::<T, I>::insert(&id, details);
		Ok(())
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
		Self::increase_balance(id, beneficiary, amount, |details| -> DispatchResult {
			if let Some(check_issuer) = maybe_check_issuer {
				ensure!(&check_issuer == &details.issuer, Error::<T, I>::NoPermission);
			}
			debug_assert!(
				T::Balance::max_value() - details.supply >= amount,
				"checked in prep; qed"
			);
			details.supply = details.supply.saturating_add(amount);
			Ok(())
		})?;
		Self::deposit_event(Event::Issued {
			asset_id: id,
			owner: beneficiary.clone(),
			total_supply: amount,
		});
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

		Self::can_increase(id, beneficiary, amount).into_result()?;
		Asset::<T, I>::try_mutate(id, |maybe_details| -> DispatchResult {
			let details = maybe_details.as_mut().ok_or(Error::<T, I>::Unknown)?;

			check(details)?;

			Account::<T, I>::try_mutate(id, beneficiary, |maybe_account| -> DispatchResult {
				match maybe_account {
					Some(ref mut account) => {
						account.balance.saturating_accrue(amount);
					},
					maybe_account @ None => {
						// Note this should never fail as it's already checked by `can_increase`.
						ensure!(amount >= details.min_balance, TokenError::BelowMinimum);
						*maybe_account = Some(AssetAccountOf::<T, I> {
							balance: amount,
							reason: Self::new_account(beneficiary, details, None)?,
							is_frozen: false,
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
		let actual = Self::decrease_balance(id, target, amount, f, |actual, details| {
			// Check admin rights.
			if let Some(check_admin) = maybe_check_admin {
				ensure!(&check_admin == &details.admin, Error::<T, I>::NoPermission);
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

		let actual = Self::prep_debit(id, target, amount, f)?;

		Asset::<T, I>::try_mutate(id, |maybe_details| -> DispatchResult {
			let mut details = maybe_details.as_mut().ok_or(Error::<T, I>::Unknown)?;

			check(actual, details)?;

			Account::<T, I>::try_mutate(id, target, |maybe_account| -> DispatchResult {
				let mut account = maybe_account.take().ok_or(Error::<T, I>::NoAccount)?;
				debug_assert!(account.balance >= actual, "checked in prep; qed");

				// Make the debit.
				account.balance = account.balance.saturating_sub(actual);
				if account.balance < details.min_balance {
					debug_assert!(account.balance.is_zero(), "checked in prep; qed");
					if let Remove =
						Self::dead_account(id, target, &mut details, &account.reason, false)
					{
						return Ok(())
					}
				};
				*maybe_account = Some(account);
				Ok(())
			})?;

			Ok(())
		})?;

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
		// Early exist if no-op.
		if amount.is_zero() {
			Self::deposit_event(Event::Transferred {
				asset_id: id,
				from: source.clone(),
				to: dest.clone(),
				amount,
			});
			return Ok(amount)
		}

		// Figure out the debit and credit, together with side-effects.
		let debit = Self::prep_debit(id, &source, amount, f.into())?;
		let (credit, maybe_burn) = Self::prep_credit(id, &dest, amount, debit, f.burn_dust)?;

		let mut source_account =
			Account::<T, I>::get(id, &source).ok_or(Error::<T, I>::NoAccount)?;

		Asset::<T, I>::try_mutate(id, |maybe_details| -> DispatchResult {
			let details = maybe_details.as_mut().ok_or(Error::<T, I>::Unknown)?;

			// Check admin rights.
			if let Some(need_admin) = maybe_need_admin {
				ensure!(&need_admin == &details.admin, Error::<T, I>::NoPermission);
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

			Account::<T, I>::try_mutate(id, &dest, |maybe_account| -> DispatchResult {
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
							is_frozen: false,
							reason: Self::new_account(&dest, details, None)?,
							extra: T::Extra::default(),
						});
					},
				}
				Ok(())
			})?;

			// Remove source account if it's now dead.
			if source_account.balance < details.min_balance {
				debug_assert!(source_account.balance.is_zero(), "checked in prep; qed");
				if let Remove =
					Self::dead_account(id, &source, details, &source_account.reason, false)
				{
					Account::<T, I>::remove(id, &source);
					return Ok(())
				}
			}
			Account::<T, I>::insert(id, &source, &source_account);
			Ok(())
		})?;

		Self::deposit_event(Event::Transferred {
			asset_id: id,
			from: source.clone(),
			to: dest.clone(),
			amount: credit,
		});
		Ok(credit)
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
		ensure!(!Asset::<T, I>::contains_key(id), Error::<T, I>::InUse);
		ensure!(!min_balance.is_zero(), Error::<T, I>::MinBalanceZero);

		Asset::<T, I>::insert(
			id,
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
				is_frozen: false,
			},
		);
		Self::deposit_event(Event::ForceCreated { asset_id: id, owner });
		Ok(())
	}

	/// Destroy an existing asset.
	///
	/// * `id`: The asset you want to destroy.
	/// * `witness`: Witness data needed about the current state of the asset, used to confirm
	///   complexity of the operation.
	/// * `maybe_check_owner`: An optional check before destroying the asset, if the provided
	///   account is the owner of that asset. Can be used for authorization checks.
	pub(super) fn do_destroy(
		id: T::AssetId,
		witness: DestroyWitness,
		maybe_check_owner: Option<T::AccountId>,
	) -> Result<DestroyWitness, DispatchError> {
		Asset::<T, I>::try_mutate_exists(id, |maybe_details| {
			let mut details = maybe_details.take().ok_or(Error::<T, I>::Unknown)?;
			if let Some(check_owner) = maybe_check_owner {
				ensure!(details.owner == check_owner, Error::<T, I>::NoPermission);
			}
			ensure!(details.accounts <= witness.accounts, Error::<T, I>::BadWitness);
			ensure!(details.sufficients <= witness.sufficients, Error::<T, I>::BadWitness);
			ensure!(details.approvals <= witness.approvals, Error::<T, I>::BadWitness);

			for (who, v) in Account::<T, I>::drain_prefix(id) {
				// We have to force this as it's destroying the entire asset class.
				// This could mean that some accounts now have irreversibly reserved
				// funds.
				let _ = Self::dead_account(id, &who, &mut details, &v.reason, true);
			}
			debug_assert_eq!(details.accounts, 0);
			debug_assert_eq!(details.sufficients, 0);

			let metadata = Metadata::<T, I>::take(&id);
			T::Currency::unreserve(
				&details.owner,
				details.deposit.saturating_add(metadata.deposit),
			);

			for ((owner, _), approval) in Approvals::<T, I>::drain_prefix((&id,)) {
				T::Currency::unreserve(&owner, approval.deposit);
			}
			Self::deposit_event(Event::Destroyed { asset_id: id });

			Ok(DestroyWitness {
				accounts: details.accounts,
				sufficients: details.sufficients,
				approvals: details.approvals,
			})
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
		let mut d = Asset::<T, I>::get(id).ok_or(Error::<T, I>::Unknown)?;
		ensure!(!d.is_frozen, Error::<T, I>::Frozen);
		Approvals::<T, I>::try_mutate(
			(id, &owner, &delegate),
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
					T::Currency::reserve(&owner, deposit_required - approved.deposit)?;
					approved.deposit = deposit_required;
				}
				approved.amount = approved.amount.saturating_add(amount);
				*maybe_approved = Some(approved);
				Ok(())
			},
		)?;
		Asset::<T, I>::insert(id, d);
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
		Approvals::<T, I>::try_mutate_exists(
			(id, &owner, delegate),
			|maybe_approved| -> DispatchResult {
				let mut approved = maybe_approved.take().ok_or(Error::<T, I>::Unapproved)?;
				let remaining =
					approved.amount.checked_sub(&amount).ok_or(Error::<T, I>::Unapproved)?;

				let f = TransferFlags { keep_alive: false, best_effort: false, burn_dust: false };
				Self::do_transfer(id, &owner, &destination, amount, None, f)?;

				if remaining.is_zero() {
					T::Currency::unreserve(&owner, approved.deposit);
					Asset::<T, I>::mutate(id, |maybe_details| {
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

		let d = Asset::<T, I>::get(id).ok_or(Error::<T, I>::Unknown)?;
		ensure!(from == &d.owner, Error::<T, I>::NoPermission);

		Metadata::<T, I>::try_mutate_exists(id, |metadata| {
			ensure!(metadata.as_ref().map_or(true, |m| !m.is_frozen), Error::<T, I>::NoPermission);

			let old_deposit = metadata.take().map_or(Zero::zero(), |m| m.deposit);
			let new_deposit = T::MetadataDepositPerByte::get()
				.saturating_mul(((name.len() + symbol.len()) as u32).into())
				.saturating_add(T::MetadataDepositBase::get());

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
}
