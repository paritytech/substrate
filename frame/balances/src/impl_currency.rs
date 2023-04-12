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

//! Implementations for the `Currency` family of traits.

use super::*;
use frame_support::{
	ensure,
	pallet_prelude::DispatchResult,
	traits::{
		tokens::{fungible, BalanceStatus as Status, Fortitude::Polite, Precision::BestEffort},
		Currency, DefensiveSaturating, ExistenceRequirement,
		ExistenceRequirement::AllowDeath,
		Get, Imbalance, LockIdentifier, LockableCurrency, NamedReservableCurrency,
		ReservableCurrency, SignedImbalance, TryDrop, WithdrawReasons,
	},
};
pub use imbalances::{NegativeImbalance, PositiveImbalance};

// wrapping these imbalances in a private module is necessary to ensure absolute privacy
// of the inner member.
mod imbalances {
	use super::{result, Config, Imbalance, RuntimeDebug, Saturating, TryDrop, Zero};
	use frame_support::traits::SameOrOther;
	use sp_std::mem;

	/// Opaque, move-only struct with private fields that serves as a token denoting that
	/// funds have been created without any equal and opposite accounting.
	#[must_use]
	#[derive(RuntimeDebug, PartialEq, Eq)]
	pub struct PositiveImbalance<T: Config<I>, I: 'static = ()>(T::Balance);

	impl<T: Config<I>, I: 'static> PositiveImbalance<T, I> {
		/// Create a new positive imbalance from a balance.
		pub fn new(amount: T::Balance) -> Self {
			PositiveImbalance(amount)
		}
	}

	/// Opaque, move-only struct with private fields that serves as a token denoting that
	/// funds have been destroyed without any equal and opposite accounting.
	#[must_use]
	#[derive(RuntimeDebug, PartialEq, Eq)]
	pub struct NegativeImbalance<T: Config<I>, I: 'static = ()>(T::Balance);

	impl<T: Config<I>, I: 'static> NegativeImbalance<T, I> {
		/// Create a new negative imbalance from a balance.
		pub fn new(amount: T::Balance) -> Self {
			NegativeImbalance(amount)
		}
	}

	impl<T: Config<I>, I: 'static> TryDrop for PositiveImbalance<T, I> {
		fn try_drop(self) -> result::Result<(), Self> {
			self.drop_zero()
		}
	}

	impl<T: Config<I>, I: 'static> Default for PositiveImbalance<T, I> {
		fn default() -> Self {
			Self::zero()
		}
	}

	impl<T: Config<I>, I: 'static> Imbalance<T::Balance> for PositiveImbalance<T, I> {
		type Opposite = NegativeImbalance<T, I>;

		fn zero() -> Self {
			Self(Zero::zero())
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
			(Self(first), Self(second))
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
		fn offset(self, other: Self::Opposite) -> SameOrOther<Self, Self::Opposite> {
			let (a, b) = (self.0, other.0);
			mem::forget((self, other));

			if a > b {
				SameOrOther::Same(Self(a - b))
			} else if b > a {
				SameOrOther::Other(NegativeImbalance::new(b - a))
			} else {
				SameOrOther::None
			}
		}
		fn peek(&self) -> T::Balance {
			self.0
		}
	}

	impl<T: Config<I>, I: 'static> TryDrop for NegativeImbalance<T, I> {
		fn try_drop(self) -> result::Result<(), Self> {
			self.drop_zero()
		}
	}

	impl<T: Config<I>, I: 'static> Default for NegativeImbalance<T, I> {
		fn default() -> Self {
			Self::zero()
		}
	}

	impl<T: Config<I>, I: 'static> Imbalance<T::Balance> for NegativeImbalance<T, I> {
		type Opposite = PositiveImbalance<T, I>;

		fn zero() -> Self {
			Self(Zero::zero())
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
			(Self(first), Self(second))
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
		fn offset(self, other: Self::Opposite) -> SameOrOther<Self, Self::Opposite> {
			let (a, b) = (self.0, other.0);
			mem::forget((self, other));

			if a > b {
				SameOrOther::Same(Self(a - b))
			} else if b > a {
				SameOrOther::Other(PositiveImbalance::new(b - a))
			} else {
				SameOrOther::None
			}
		}
		fn peek(&self) -> T::Balance {
			self.0
		}
	}

	impl<T: Config<I>, I: 'static> Drop for PositiveImbalance<T, I> {
		/// Basic drop handler will just square up the total issuance.
		fn drop(&mut self) {
			<super::TotalIssuance<T, I>>::mutate(|v| *v = v.saturating_add(self.0));
		}
	}

	impl<T: Config<I>, I: 'static> Drop for NegativeImbalance<T, I> {
		/// Basic drop handler will just square up the total issuance.
		fn drop(&mut self) {
			<super::TotalIssuance<T, I>>::mutate(|v| *v = v.saturating_sub(self.0));
		}
	}
}

impl<T: Config<I>, I: 'static> Currency<T::AccountId> for Pallet<T, I>
where
	T::Balance: MaybeSerializeDeserialize + Debug,
{
	type Balance = T::Balance;
	type PositiveImbalance = PositiveImbalance<T, I>;
	type NegativeImbalance = NegativeImbalance<T, I>;

	fn total_balance(who: &T::AccountId) -> Self::Balance {
		Self::account(who).total()
	}

	// Check if `value` amount of free balance can be slashed from `who`.
	fn can_slash(who: &T::AccountId, value: Self::Balance) -> bool {
		if value.is_zero() {
			return true
		}
		Self::free_balance(who) >= value
	}

	fn total_issuance() -> Self::Balance {
		TotalIssuance::<T, I>::get()
	}

	fn active_issuance() -> Self::Balance {
		<Self as fungible::Inspect<_>>::active_issuance()
	}

	fn deactivate(amount: Self::Balance) {
		<Self as fungible::Unbalanced<_>>::deactivate(amount);
	}

	fn reactivate(amount: Self::Balance) {
		<Self as fungible::Unbalanced<_>>::reactivate(amount);
	}

	fn minimum_balance() -> Self::Balance {
		T::ExistentialDeposit::get()
	}

	// Burn funds from the total issuance, returning a positive imbalance for the amount burned.
	// Is a no-op if amount to be burned is zero.
	fn burn(mut amount: Self::Balance) -> Self::PositiveImbalance {
		if amount.is_zero() {
			return PositiveImbalance::zero()
		}
		<TotalIssuance<T, I>>::mutate(|issued| {
			*issued = issued.checked_sub(&amount).unwrap_or_else(|| {
				amount = *issued;
				Zero::zero()
			});
		});
		PositiveImbalance::new(amount)
	}

	// Create new funds into the total issuance, returning a negative imbalance
	// for the amount issued.
	// Is a no-op if amount to be issued it zero.
	fn issue(mut amount: Self::Balance) -> Self::NegativeImbalance {
		if amount.is_zero() {
			return NegativeImbalance::zero()
		}
		<TotalIssuance<T, I>>::mutate(|issued| {
			*issued = issued.checked_add(&amount).unwrap_or_else(|| {
				amount = Self::Balance::max_value() - *issued;
				Self::Balance::max_value()
			})
		});
		NegativeImbalance::new(amount)
	}

	fn free_balance(who: &T::AccountId) -> Self::Balance {
		Self::account(who).free
	}

	// Ensure that an account can withdraw from their free balance given any existing withdrawal
	// restrictions like locks and vesting balance.
	// Is a no-op if amount to be withdrawn is zero.
	fn ensure_can_withdraw(
		who: &T::AccountId,
		amount: T::Balance,
		_reasons: WithdrawReasons,
		new_balance: T::Balance,
	) -> DispatchResult {
		if amount.is_zero() {
			return Ok(())
		}
		ensure!(new_balance >= Self::account(who).frozen, Error::<T, I>::LiquidityRestrictions);
		Ok(())
	}

	// Transfer some free balance from `transactor` to `dest`, respecting existence requirements.
	// Is a no-op if value to be transferred is zero or the `transactor` is the same as `dest`.
	fn transfer(
		transactor: &T::AccountId,
		dest: &T::AccountId,
		value: Self::Balance,
		existence_requirement: ExistenceRequirement,
	) -> DispatchResult {
		if value.is_zero() || transactor == dest {
			return Ok(())
		}
		let keep_alive = match existence_requirement {
			ExistenceRequirement::KeepAlive => Preserve,
			ExistenceRequirement::AllowDeath => Expendable,
		};
		<Self as fungible::Mutate<_>>::transfer(transactor, dest, value, keep_alive)?;
		Ok(())
	}

	/// Slash a target account `who`, returning the negative imbalance created and any left over
	/// amount that could not be slashed.
	///
	/// Is a no-op if `value` to be slashed is zero or the account does not exist.
	///
	/// NOTE: `slash()` prefers free balance, but assumes that reserve balance can be drawn
	/// from in extreme circumstances. `can_slash()` should be used prior to `slash()` to avoid
	/// having to draw from reserved funds, however we err on the side of punishment if things are
	/// inconsistent or `can_slash` wasn't used appropriately.
	fn slash(who: &T::AccountId, value: Self::Balance) -> (Self::NegativeImbalance, Self::Balance) {
		if value.is_zero() {
			return (NegativeImbalance::zero(), Zero::zero())
		}
		if Self::total_balance(who).is_zero() {
			return (NegativeImbalance::zero(), value)
		}

		let result = match Self::try_mutate_account_handling_dust(
			who,
			|account, _is_new| -> Result<(Self::NegativeImbalance, Self::Balance), DispatchError> {
				// Best value is the most amount we can slash following liveness rules.
				let ed = T::ExistentialDeposit::get();
				let actual = match system::Pallet::<T>::can_dec_provider(who) {
					true => value.min(account.free),
					false => value.min(account.free.saturating_sub(ed)),
				};
				account.free.saturating_reduce(actual);
				let remaining = value.saturating_sub(actual);
				Ok((NegativeImbalance::new(actual), remaining))
			},
		) {
			Ok((imbalance, remaining)) => {
				Self::deposit_event(Event::Slashed {
					who: who.clone(),
					amount: value.saturating_sub(remaining),
				});
				(imbalance, remaining)
			},
			Err(_) => (Self::NegativeImbalance::zero(), value),
		};
		result
	}

	/// Deposit some `value` into the free balance of an existing target account `who`.
	///
	/// Is a no-op if the `value` to be deposited is zero.
	fn deposit_into_existing(
		who: &T::AccountId,
		value: Self::Balance,
	) -> Result<Self::PositiveImbalance, DispatchError> {
		if value.is_zero() {
			return Ok(PositiveImbalance::zero())
		}

		Self::try_mutate_account_handling_dust(
			who,
			|account, is_new| -> Result<Self::PositiveImbalance, DispatchError> {
				ensure!(!is_new, Error::<T, I>::DeadAccount);
				account.free = account.free.checked_add(&value).ok_or(ArithmeticError::Overflow)?;
				Self::deposit_event(Event::Deposit { who: who.clone(), amount: value });
				Ok(PositiveImbalance::new(value))
			},
		)
	}

	/// Deposit some `value` into the free balance of `who`, possibly creating a new account.
	///
	/// This function is a no-op if:
	/// - the `value` to be deposited is zero; or
	/// - the `value` to be deposited is less than the required ED and the account does not yet
	///   exist; or
	/// - the deposit would necessitate the account to exist and there are no provider references;
	///   or
	/// - `value` is so large it would cause the balance of `who` to overflow.
	fn deposit_creating(who: &T::AccountId, value: Self::Balance) -> Self::PositiveImbalance {
		if value.is_zero() {
			return Self::PositiveImbalance::zero()
		}

		Self::try_mutate_account_handling_dust(
			who,
			|account, is_new| -> Result<Self::PositiveImbalance, DispatchError> {
				let ed = T::ExistentialDeposit::get();
				ensure!(value >= ed || !is_new, Error::<T, I>::ExistentialDeposit);

				// defensive only: overflow should never happen, however in case it does, then this
				// operation is a no-op.
				account.free = match account.free.checked_add(&value) {
					Some(x) => x,
					None => return Ok(Self::PositiveImbalance::zero()),
				};

				Self::deposit_event(Event::Deposit { who: who.clone(), amount: value });
				Ok(PositiveImbalance::new(value))
			},
		)
		.unwrap_or_else(|_| Self::PositiveImbalance::zero())
	}

	/// Withdraw some free balance from an account, respecting existence requirements.
	///
	/// Is a no-op if value to be withdrawn is zero.
	fn withdraw(
		who: &T::AccountId,
		value: Self::Balance,
		reasons: WithdrawReasons,
		liveness: ExistenceRequirement,
	) -> result::Result<Self::NegativeImbalance, DispatchError> {
		if value.is_zero() {
			return Ok(NegativeImbalance::zero())
		}

		Self::try_mutate_account_handling_dust(
			who,
			|account, _| -> Result<Self::NegativeImbalance, DispatchError> {
				let new_free_account =
					account.free.checked_sub(&value).ok_or(Error::<T, I>::InsufficientBalance)?;

				// bail if we need to keep the account alive and this would kill it.
				let ed = T::ExistentialDeposit::get();
				let would_be_dead = new_free_account < ed;
				let would_kill = would_be_dead && account.free >= ed;
				ensure!(liveness == AllowDeath || !would_kill, Error::<T, I>::Expendability);

				Self::ensure_can_withdraw(who, value, reasons, new_free_account)?;

				account.free = new_free_account;

				Self::deposit_event(Event::Withdraw { who: who.clone(), amount: value });
				Ok(NegativeImbalance::new(value))
			},
		)
	}

	/// Force the new free balance of a target account `who` to some new value `balance`.
	fn make_free_balance_be(
		who: &T::AccountId,
		value: Self::Balance,
	) -> SignedImbalance<Self::Balance, Self::PositiveImbalance> {
		Self::try_mutate_account_handling_dust(
			who,
			|account,
			 is_new|
			 -> Result<SignedImbalance<Self::Balance, Self::PositiveImbalance>, DispatchError> {
				let ed = T::ExistentialDeposit::get();
				// If we're attempting to set an existing account to less than ED, then
				// bypass the entire operation. It's a no-op if you follow it through, but
				// since this is an instance where we might account for a negative imbalance
				// (in the dust cleaner of set_account) before we account for its actual
				// equal and opposite cause (returned as an Imbalance), then in the
				// instance that there's no other accounts on the system at all, we might
				// underflow the issuance and our arithmetic will be off.
				ensure!(value >= ed || !is_new, Error::<T, I>::ExistentialDeposit);

				let imbalance = if account.free <= value {
					SignedImbalance::Positive(PositiveImbalance::new(value - account.free))
				} else {
					SignedImbalance::Negative(NegativeImbalance::new(account.free - value))
				};
				account.free = value;
				Self::deposit_event(Event::BalanceSet { who: who.clone(), free: account.free });
				Ok(imbalance)
			},
		)
		.unwrap_or_else(|_| SignedImbalance::Positive(Self::PositiveImbalance::zero()))
	}
}

impl<T: Config<I>, I: 'static> ReservableCurrency<T::AccountId> for Pallet<T, I>
where
	T::Balance: MaybeSerializeDeserialize + Debug,
{
	/// Check if `who` can reserve `value` from their free balance.
	///
	/// Always `true` if value to be reserved is zero.
	fn can_reserve(who: &T::AccountId, value: Self::Balance) -> bool {
		if value.is_zero() {
			return true
		}
		Self::account(who).free.checked_sub(&value).map_or(false, |new_balance| {
			Self::ensure_can_withdraw(who, value, WithdrawReasons::RESERVE, new_balance).is_ok()
		})
	}

	fn reserved_balance(who: &T::AccountId) -> Self::Balance {
		Self::account(who).reserved
	}

	/// Move `value` from the free balance from `who` to their reserved balance.
	///
	/// Is a no-op if value to be reserved is zero.
	fn reserve(who: &T::AccountId, value: Self::Balance) -> DispatchResult {
		if value.is_zero() {
			return Ok(())
		}

		Self::try_mutate_account_handling_dust(who, |account, _| -> DispatchResult {
			account.free =
				account.free.checked_sub(&value).ok_or(Error::<T, I>::InsufficientBalance)?;
			account.reserved =
				account.reserved.checked_add(&value).ok_or(ArithmeticError::Overflow)?;
			Self::ensure_can_withdraw(&who, value, WithdrawReasons::RESERVE, account.free)
		})?;

		Self::deposit_event(Event::Reserved { who: who.clone(), amount: value });
		Ok(())
	}

	/// Unreserve some funds, returning any amount that was unable to be unreserved.
	///
	/// Is a no-op if the value to be unreserved is zero or the account does not exist.
	///
	/// NOTE: returns amount value which wasn't successfully unreserved.
	fn unreserve(who: &T::AccountId, value: Self::Balance) -> Self::Balance {
		if value.is_zero() {
			return Zero::zero()
		}
		if Self::total_balance(who).is_zero() {
			return value
		}

		let actual = match Self::mutate_account_handling_dust(who, |account| {
			let actual = cmp::min(account.reserved, value);
			account.reserved -= actual;
			// defensive only: this can never fail since total issuance which is at least
			// free+reserved fits into the same data type.
			account.free = account.free.defensive_saturating_add(actual);
			actual
		}) {
			Ok(x) => x,
			Err(_) => {
				// This should never happen since we don't alter the total amount in the account.
				// If it ever does, then we should fail gracefully though, indicating that nothing
				// could be done.
				return value
			},
		};

		Self::deposit_event(Event::Unreserved { who: who.clone(), amount: actual });
		value - actual
	}

	/// Slash from reserved balance, returning the negative imbalance created,
	/// and any amount that was unable to be slashed.
	///
	/// Is a no-op if the value to be slashed is zero or the account does not exist.
	fn slash_reserved(
		who: &T::AccountId,
		value: Self::Balance,
	) -> (Self::NegativeImbalance, Self::Balance) {
		if value.is_zero() {
			return (NegativeImbalance::zero(), Zero::zero())
		}
		if Self::total_balance(who).is_zero() {
			return (NegativeImbalance::zero(), value)
		}

		// NOTE: `mutate_account` may fail if it attempts to reduce the balance to the point that an
		//   account is attempted to be illegally destroyed.

		match Self::mutate_account_handling_dust(who, |account| {
			let actual = value.min(account.reserved);
			account.reserved.saturating_reduce(actual);

			// underflow should never happen, but it if does, there's nothing to be done here.
			(NegativeImbalance::new(actual), value.saturating_sub(actual))
		}) {
			Ok((imbalance, not_slashed)) => {
				Self::deposit_event(Event::Slashed {
					who: who.clone(),
					amount: value.saturating_sub(not_slashed),
				});
				(imbalance, not_slashed)
			},
			Err(_) => (Self::NegativeImbalance::zero(), value),
		}
	}

	/// Move the reserved balance of one account into the balance of another, according to `status`.
	///
	/// Is a no-op if:
	/// - the value to be moved is zero; or
	/// - the `slashed` id equal to `beneficiary` and the `status` is `Reserved`.
	///
	/// This is `Polite` and thus will not repatriate any funds which would lead the total balance
	/// to be less than the frozen amount. Returns `Ok` with the actual amount of funds moved,
	/// which may be less than `value` since the operation is done an a `BestEffort` basis.
	fn repatriate_reserved(
		slashed: &T::AccountId,
		beneficiary: &T::AccountId,
		value: Self::Balance,
		status: Status,
	) -> Result<Self::Balance, DispatchError> {
		let actual =
			Self::do_transfer_reserved(slashed, beneficiary, value, BestEffort, Polite, status)?;
		Ok(value.saturating_sub(actual))
	}
}

impl<T: Config<I>, I: 'static> NamedReservableCurrency<T::AccountId> for Pallet<T, I>
where
	T::Balance: MaybeSerializeDeserialize + Debug,
{
	type ReserveIdentifier = T::ReserveIdentifier;

	fn reserved_balance_named(id: &Self::ReserveIdentifier, who: &T::AccountId) -> Self::Balance {
		let reserves = Self::reserves(who);
		reserves
			.binary_search_by_key(id, |data| data.id)
			.map(|index| reserves[index].amount)
			.unwrap_or_default()
	}

	/// Move `value` from the free balance from `who` to a named reserve balance.
	///
	/// Is a no-op if value to be reserved is zero.
	fn reserve_named(
		id: &Self::ReserveIdentifier,
		who: &T::AccountId,
		value: Self::Balance,
	) -> DispatchResult {
		if value.is_zero() {
			return Ok(())
		}

		Reserves::<T, I>::try_mutate(who, |reserves| -> DispatchResult {
			match reserves.binary_search_by_key(id, |data| data.id) {
				Ok(index) => {
					// this add can't overflow but just to be defensive.
					reserves[index].amount = reserves[index].amount.defensive_saturating_add(value);
				},
				Err(index) => {
					reserves
						.try_insert(index, ReserveData { id: *id, amount: value })
						.map_err(|_| Error::<T, I>::TooManyReserves)?;
				},
			};
			<Self as ReservableCurrency<_>>::reserve(who, value)?;
			Ok(())
		})
	}

	/// Unreserve some funds, returning any amount that was unable to be unreserved.
	///
	/// Is a no-op if the value to be unreserved is zero.
	fn unreserve_named(
		id: &Self::ReserveIdentifier,
		who: &T::AccountId,
		value: Self::Balance,
	) -> Self::Balance {
		if value.is_zero() {
			return Zero::zero()
		}

		Reserves::<T, I>::mutate_exists(who, |maybe_reserves| -> Self::Balance {
			if let Some(reserves) = maybe_reserves.as_mut() {
				match reserves.binary_search_by_key(id, |data| data.id) {
					Ok(index) => {
						let to_change = cmp::min(reserves[index].amount, value);

						let remain = <Self as ReservableCurrency<_>>::unreserve(who, to_change);

						// remain should always be zero but just to be defensive here.
						let actual = to_change.defensive_saturating_sub(remain);

						// `actual <= to_change` and `to_change <= amount`; qed;
						reserves[index].amount -= actual;

						if reserves[index].amount.is_zero() {
							if reserves.len() == 1 {
								// no more named reserves
								*maybe_reserves = None;
							} else {
								// remove this named reserve
								reserves.remove(index);
							}
						}

						value - actual
					},
					Err(_) => value,
				}
			} else {
				value
			}
		})
	}

	/// Slash from reserved balance, returning the negative imbalance created,
	/// and any amount that was unable to be slashed.
	///
	/// Is a no-op if the value to be slashed is zero.
	fn slash_reserved_named(
		id: &Self::ReserveIdentifier,
		who: &T::AccountId,
		value: Self::Balance,
	) -> (Self::NegativeImbalance, Self::Balance) {
		if value.is_zero() {
			return (NegativeImbalance::zero(), Zero::zero())
		}

		Reserves::<T, I>::mutate(who, |reserves| -> (Self::NegativeImbalance, Self::Balance) {
			match reserves.binary_search_by_key(id, |data| data.id) {
				Ok(index) => {
					let to_change = cmp::min(reserves[index].amount, value);

					let (imb, remain) =
						<Self as ReservableCurrency<_>>::slash_reserved(who, to_change);

					// remain should always be zero but just to be defensive here.
					let actual = to_change.defensive_saturating_sub(remain);

					// `actual <= to_change` and `to_change <= amount`; qed;
					reserves[index].amount -= actual;

					Self::deposit_event(Event::Slashed { who: who.clone(), amount: actual });
					(imb, value - actual)
				},
				Err(_) => (NegativeImbalance::zero(), value),
			}
		})
	}

	/// Move the reserved balance of one account into the balance of another, according to `status`.
	/// If `status` is `Reserved`, the balance will be reserved with given `id`.
	///
	/// Is a no-op if:
	/// - the value to be moved is zero; or
	/// - the `slashed` id equal to `beneficiary` and the `status` is `Reserved`.
	fn repatriate_reserved_named(
		id: &Self::ReserveIdentifier,
		slashed: &T::AccountId,
		beneficiary: &T::AccountId,
		value: Self::Balance,
		status: Status,
	) -> Result<Self::Balance, DispatchError> {
		if value.is_zero() {
			return Ok(Zero::zero())
		}

		if slashed == beneficiary {
			return match status {
				Status::Free => Ok(Self::unreserve_named(id, slashed, value)),
				Status::Reserved =>
					Ok(value.saturating_sub(Self::reserved_balance_named(id, slashed))),
			}
		}

		Reserves::<T, I>::try_mutate(slashed, |reserves| -> Result<Self::Balance, DispatchError> {
			match reserves.binary_search_by_key(id, |data| data.id) {
				Ok(index) => {
					let to_change = cmp::min(reserves[index].amount, value);

					let actual = if status == Status::Reserved {
						// make it the reserved under same identifier
						Reserves::<T, I>::try_mutate(
							beneficiary,
							|reserves| -> Result<T::Balance, DispatchError> {
								match reserves.binary_search_by_key(id, |data| data.id) {
									Ok(index) => {
										let remain =
											<Self as ReservableCurrency<_>>::repatriate_reserved(
												slashed,
												beneficiary,
												to_change,
												status,
											)?;

										// remain should always be zero but just to be defensive
										// here.
										let actual = to_change.defensive_saturating_sub(remain);

										// this add can't overflow but just to be defensive.
										reserves[index].amount =
											reserves[index].amount.defensive_saturating_add(actual);

										Ok(actual)
									},
									Err(index) => {
										let remain =
											<Self as ReservableCurrency<_>>::repatriate_reserved(
												slashed,
												beneficiary,
												to_change,
												status,
											)?;

										// remain should always be zero but just to be defensive
										// here
										let actual = to_change.defensive_saturating_sub(remain);

										reserves
											.try_insert(
												index,
												ReserveData { id: *id, amount: actual },
											)
											.map_err(|_| Error::<T, I>::TooManyReserves)?;

										Ok(actual)
									},
								}
							},
						)?
					} else {
						let remain = <Self as ReservableCurrency<_>>::repatriate_reserved(
							slashed,
							beneficiary,
							to_change,
							status,
						)?;

						// remain should always be zero but just to be defensive here
						to_change.defensive_saturating_sub(remain)
					};

					// `actual <= to_change` and `to_change <= amount`; qed;
					reserves[index].amount -= actual;

					Ok(value - actual)
				},
				Err(_) => Ok(value),
			}
		})
	}
}

impl<T: Config<I>, I: 'static> LockableCurrency<T::AccountId> for Pallet<T, I>
where
	T::Balance: MaybeSerializeDeserialize + Debug,
{
	type Moment = T::BlockNumber;

	type MaxLocks = T::MaxLocks;

	// Set a lock on the balance of `who`.
	// Is a no-op if lock amount is zero or `reasons` `is_none()`.
	fn set_lock(
		id: LockIdentifier,
		who: &T::AccountId,
		amount: T::Balance,
		reasons: WithdrawReasons,
	) {
		if amount.is_zero() || reasons.is_empty() {
			return
		}
		let mut new_lock = Some(BalanceLock { id, amount, reasons: reasons.into() });
		let mut locks = Self::locks(who)
			.into_iter()
			.filter_map(|l| if l.id == id { new_lock.take() } else { Some(l) })
			.collect::<Vec<_>>();
		if let Some(lock) = new_lock {
			locks.push(lock)
		}
		Self::update_locks(who, &locks[..]);
	}

	// Extend a lock on the balance of `who`.
	// Is a no-op if lock amount is zero or `reasons` `is_none()`.
	fn extend_lock(
		id: LockIdentifier,
		who: &T::AccountId,
		amount: T::Balance,
		reasons: WithdrawReasons,
	) {
		if amount.is_zero() || reasons.is_empty() {
			return
		}
		let mut new_lock = Some(BalanceLock { id, amount, reasons: reasons.into() });
		let mut locks = Self::locks(who)
			.into_iter()
			.filter_map(|l| {
				if l.id == id {
					new_lock.take().map(|nl| BalanceLock {
						id: l.id,
						amount: l.amount.max(nl.amount),
						reasons: l.reasons | nl.reasons,
					})
				} else {
					Some(l)
				}
			})
			.collect::<Vec<_>>();
		if let Some(lock) = new_lock {
			locks.push(lock)
		}
		Self::update_locks(who, &locks[..]);
	}

	fn remove_lock(id: LockIdentifier, who: &T::AccountId) {
		let mut locks = Self::locks(who);
		locks.retain(|l| l.id != id);
		Self::update_locks(who, &locks[..]);
	}
}
