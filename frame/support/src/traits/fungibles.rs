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

//! The traits for sets of fungible tokens and any associated types.

use super::*;

/// One of a number of consequences of withdrawing a fungible from an account.
#[derive(Copy, Clone, Eq, PartialEq)]
pub enum WithdrawConsequence<Balance> {
	/// Withdraw could not happen.
	Failed,
	/// Account balance would reduce to zero, potentially destroying it. The parameter is the
	/// amount of balance which is destroyed.
	ReducedToZero(Balance),
	/// Account continued in existence.
	Success,
}

pub trait AssetId: FullCodec + Copy + Default + Eq + PartialEq {}
impl<T: FullCodec + Copy + Default + Eq + PartialEq> AssetId for T {}

pub trait Balance: AtLeast32BitUnsigned + FullCodec + Copy + Default {}
impl<T: AtLeast32BitUnsigned + FullCodec + Copy + Default> Balance for T {}

/// Trait for providing balance-inspection access to a set of named fungible assets.
pub trait InspectFungibles<AccountId> {
	/// Means of identifying one asset class from another.
	type AssetId: AssetId;
	/// Scalar type for representing balance of an account.
	type Balance: Balance;
	/// The total amount of issuance in the system.
	fn total_issuance(asset: Self::AssetId) -> Self::Balance;
	/// The minimum balance any single account may have.
	fn minimum_balance(asset: Self::AssetId) -> Self::Balance;
	/// Get the `asset` balance of `who`.
	fn balance(asset: Self::AssetId, who: &AccountId) -> Self::Balance;
	/// Returns `true` if the `asset` balance of `who` may be increased by `amount`.
	fn can_deposit(asset: Self::AssetId, who: &AccountId, amount: Self::Balance) -> bool;
	/// Returns `Failed` if the `asset` balance of `who` may not be decreased by `amount`, otherwise
	/// the consequence.
	fn can_withdraw(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance,
	) -> WithdrawConsequence<Self::Balance>;
}

/// Trait for providing a set of named fungible assets which can be created and destroyed.
pub trait Fungibles<AccountId>: InspectFungibles<AccountId> {
	/// Increase the `asset` balance of `who` by `amount`.
	fn deposit(asset: Self::AssetId, who: &AccountId, amount: Self::Balance) -> DispatchResult;
	/// Attempt to reduce the `asset` balance of `who` by `amount`.
	fn withdraw(asset: Self::AssetId, who: &AccountId, amount: Self::Balance) -> DispatchResult;
	/// Transfer funds from one account into another.
	fn transfer(
		asset: Self::AssetId,
		source: &AccountId,
		dest: &AccountId,
		amount: Self::Balance,
	) -> DispatchResult {
		if !Self::can_deposit(asset, &dest, amount) {
			return Err(DispatchError::Other("Cannot deposit"))
		}
		Self::withdraw(asset, source, amount)?;
		let result = Self::deposit(asset, dest, amount);
		debug_assert!(result.is_ok(), "can_deposit returned true for a failing deposit!");
		result
	}
}

pub trait HandleImbalanceDrop<AssetId, Balance> {
	fn handle(asset: AssetId, amount: Balance);
}

pub struct Imbalance<
	A: AssetId,
	B: Balance,
	OnDrop: HandleImbalanceDrop<A, B>,
	OppositeOnDrop: HandleImbalanceDrop<A, B>,
> {
	asset: A,
	amount: B,
	_phantom: PhantomData<(OnDrop, OppositeOnDrop)>,
}

impl<
	A: AssetId,
	B: Balance,
	OnDrop: HandleImbalanceDrop<A, B>,
	OppositeOnDrop: HandleImbalanceDrop<A, B>
> Drop for Imbalance<A, B, OnDrop, OppositeOnDrop> {
	fn drop(&mut self) {
		if !self.amount.is_zero() {
			OnDrop::handle(self.asset, self.amount)
		}
	}
}

/// Return type used when we need to return one of two imbalances each in the opposite direction.
pub enum UnderOver<A, B> {
	/// There is no imbalance.
	Exact,
	/// An imbalance of the same type as the `Self` on which the return function was called.
	Under(A),
	/// An imbalance of the opposite type to the `Self` on which the return function was called.
	Over(B),
}

impl<A, B> UnderOver<A, B> {
	pub fn try_drop(self) -> Result<(), Self> {
		if let Self::Exact = self {
			Ok(())
		} else {
			Err(self)
		}
	}
}

impl<
	A: AssetId,
	B: Balance,
	OnDrop: HandleImbalanceDrop<A, B>,
	OppositeOnDrop: HandleImbalanceDrop<A, B>,
> Imbalance<A, B, OnDrop, OppositeOnDrop> {
	pub fn zero(asset: A) -> Self {
		Self { asset, amount: Zero::zero(), _phantom: PhantomData }
	}

	pub fn drop_zero(self) -> Result<(), Self> {
		if self.amount.is_zero() {
			sp_std::mem::forget(self);
			Ok(())
		} else {
			Err(self)
		}
	}

	pub fn split(self, amount: B) -> (Self, Self) {
		let first = self.amount.min(amount);
		let second = self.amount - first;
		let asset = self.asset;
		sp_std::mem::forget(self);
		(
			Imbalance { amount: first, asset, _phantom: PhantomData },
			Imbalance { amount: second, asset, _phantom: PhantomData },
		)
	}
	pub fn merge(mut self, other: Self) -> Result<Self, (Self, Self)> {
		if self.asset == other.asset {
			self.amount = self.amount.saturating_add(other.amount);
			sp_std::mem::forget(other);
			Ok(self)
		} else {
			Err((self, other))
		}
	}
	pub fn subsume(&mut self, other: Self) -> Result<(), Self> {
		if self.asset == other.asset {
			self.amount = self.amount.saturating_add(other.amount);
			sp_std::mem::forget(other);
			Ok(())
		} else {
			Err(other)
		}
	}
	pub fn offset(self, other: Imbalance<A, B, OppositeOnDrop, OnDrop>) -> Result<
		UnderOver<Self, Imbalance<A, B, OppositeOnDrop, OnDrop>>,
		(Self, Imbalance<A, B, OppositeOnDrop, OnDrop>),
	> {
		if self.asset == other.asset {
			let (a, b) = (self.amount, other.amount);
			let asset = self.asset;
			sp_std::mem::forget((self, other));

			if a == b {
				Ok(UnderOver::Exact)
			} else if a > b {
				Ok(UnderOver::Under(Imbalance { amount: a - b, asset, _phantom: PhantomData }))
			} else {
				Ok(UnderOver::Over(Imbalance::<A, B, OppositeOnDrop, OnDrop> {
					amount: b - a,
					asset,
					_phantom: PhantomData,
				}))
			}
		} else {
			Err((self, other))
		}
	}
	pub fn peek(&self) -> B {
		self.amount
	}
	pub fn asset(&self) -> A {
		self.asset
	}
}

/// Imbalance implying that the total_issuance value is less than the sum of all account balances.
pub type DebtOf<AccountId, B> = Imbalance<
	<B as InspectFungibles<AccountId>>::AssetId,
	<B as InspectFungibles<AccountId>>::Balance,
	// This will generally be implemented by increasing the total_issuance value.
	<B as BalancedFungibles<AccountId>>::OnDropDebt,
	<B as BalancedFungibles<AccountId>>::OnDropCredit,
>;

/// Imbalance implying that the total_issuance value is greater than the sum of all account balances.
pub type CreditOf<AccountId, B> = Imbalance<
	<B as InspectFungibles<AccountId>>::AssetId,
	<B as InspectFungibles<AccountId>>::Balance,
	// This will generally be implemented by decreasing the total_issuance value.
	<B as BalancedFungibles<AccountId>>::OnDropCredit,
	<B as BalancedFungibles<AccountId>>::OnDropDebt,
>;

pub trait BalancedFungibles<AccountId>: InspectFungibles<AccountId> {
	type OnDropDebt: HandleImbalanceDrop<Self::AssetId, Self::Balance>;
	type OnDropCredit: HandleImbalanceDrop<Self::AssetId, Self::Balance>;

	/// Reduce the total issuance by `amount` and return the according imbalance. The imbalance will
	/// typically be used to reduce an account by the same amount with e.g. `settle`.
	///
	/// This is infallible, but doesn't guarantee that the entire `amount` is burnt, for example
	/// in the case of underflow.
	fn rescind(asset: Self::AssetId, amount: Self::Balance) -> DebtOf<AccountId, Self>;

	/// Increase the total issuance by `amount` and return the according imbalance. The imbalance
	/// will typically be used to increase an account by the same amount with e.g.
	/// `resolve_into_existing` or `resolve_creating`.
	///
	/// This is infallible, but doesn't guarantee that the entire `amount` is issued, for example
	/// in the case of overflow.
	fn issue(asset: Self::AssetId, amount: Self::Balance) -> CreditOf<AccountId, Self>;

	/// Produce a pair of imbalances that cancel each other out exactly.
	///
	/// This is just the same as burning and issuing the same amount and has no effect on the
	/// total issuance.
	fn pair(asset: Self::AssetId, amount: Self::Balance)
		-> (DebtOf<AccountId, Self>, CreditOf<AccountId, Self>)
	{
		(Self::rescind(asset, amount), Self::issue(asset, amount))
	}

	/// Deducts up to `value` from the combined balance of `who`, preferring to deduct from the
	/// free balance. This function cannot fail.
	///
	/// The resulting imbalance is the first item of the tuple returned.
	///
	/// As much funds up to `value` will be deducted as possible. If this is less than `value`,
	/// then a non-zero second item will be returned.
	fn slash(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance,
	) -> (CreditOf<AccountId, Self>, Self::Balance);

	/// Mints exactly `value` into the `asset` account of `who`.
	///
	/// If `who` doesn't exist, nothing is done and an `Err` returned. This could happen because it
	/// the account doesn't yet exist and it isn't possible to create it under the current
	/// circumstances and with `value` in it.
	fn deposit(
		asset: Self::AssetId,
		who: &AccountId,
		value: Self::Balance,
	) -> Result<DebtOf<AccountId, Self>, DispatchError>;

	/// Removes `value` free `asset` balance from `who` account if possible.
	///
	/// If the removal is not possible, then it returns `Err` and nothing is changed.
	///
	/// If the operation is successful, this will return `Ok` with a `NegativeImbalance` whose value
	/// is no less than `value`. It may be more in the case that removing it reduced it below
	/// `Self::minimum_balance()`.
	fn withdraw(
		asset: Self::AssetId,
		who: &AccountId,
		value: Self::Balance,
		//TODO: liveness: ExistenceRequirement,
	) -> Result<CreditOf<AccountId, Self>, DispatchError>;

	/// The balance of `who` is increased in order to counter `credit`. If the whole of `credit`
	/// cannot be countered, then nothing is changed and the original `credit` is returned in an
	/// `Err`.
	///
	/// Please note: If `credit.peek()` is less than `Self::minimum_balance()`, then `who` must
	/// already exist for this to succeed.
	fn resolve(
		who: &AccountId,
		credit: CreditOf<AccountId, Self>,
	) -> result::Result<(), CreditOf<AccountId, Self>> {
		let v = credit.amount;
		let debt = match Self::deposit(credit.asset, who, v) {
			Err(_) => return Err(credit),
			Ok(d) => d,
		};
		if let Ok(result) = credit.offset(debt) {
			let result = result.try_drop();
			debug_assert!(result.is_ok(), "ok deposit return must be equal to credit value; qed");
		} else {
			debug_assert!(false, "debt.asset is credit.asset; qed");
		}
		Ok(())
	}

	/// The balance of `who` is decreased in order to counter `debt`. If the whole of `debt`
	/// cannot be countered, then nothing is changed and the original `debt` is returned in an
	/// `Err`.
	fn settle(
		who: &AccountId,
		debt: DebtOf<AccountId, Self>,
		//TODO: liveness: ExistenceRequirement,
	) -> result::Result<CreditOf<AccountId, Self>, DebtOf<AccountId, Self>> {
		let amount = debt.amount;
		let asset = debt.asset;
		let credit = match Self::withdraw(asset, who, amount) {
			Err(_) => return Err(debt),
			Ok(d) => d,
		};
		match credit.offset(debt) {
			Ok(UnderOver::Exact) => Ok(CreditOf::<AccountId, Self>::zero(asset)),
			Ok(UnderOver::Under(dust)) => Ok(dust),
			Ok(UnderOver::Over(rest)) => {
				debug_assert!(false, "ok withdraw return must be at least debt value; qed");
				Err(rest)
			}
			Err(_) => {
				debug_assert!(false, "debt.asset is credit.asset; qed");
				Ok(CreditOf::<AccountId, Self>::zero(asset))
			}
		}
	}
}

pub trait UnbalancedFungibles<AccountId>: InspectFungibles<AccountId> {
	/// Set the `asset` balance of `who` to `amount`. If this cannot be done for some reason (e.g.
	/// because the account cannot be created or an overflow) then an `Err` is returned.
	fn set_balance(asset: Self::AssetId, who: &AccountId, amount: Self::Balance) -> DispatchResult;

	/// Set the total issuance of `asset` to `amount`.
	fn set_total_issuance(asset: Self::AssetId, amount: Self::Balance);

	/// Reduce the `asset` balance of `who` by `amount`. If it cannot be reduced by that amount for
	/// some reason, return `Err` and don't reduce it at all. If Ok, return the imbalance.
	///
	/// Minimum balance will be respected and the returned imbalance may be up to
	/// `Self::minimum_balance() - 1` greater than `amount`.
	fn decrease_balance(asset: Self::AssetId, who: &AccountId, amount: Self::Balance)
		-> Result<Self::Balance, DispatchError>
	{
		let old_balance = Self::balance(asset, who);
		let (mut new_balance, mut amount) = if old_balance < amount {
			return Err(DispatchError::Other("BalanceLow"));
		} else {
			(old_balance - amount, amount)
		};
		if new_balance < Self::minimum_balance(asset) {
			amount = amount.saturating_add(new_balance);
			new_balance = Zero::zero();
		}
		// Defensive only - this should not fail now.
		Self::set_balance(asset, who, new_balance)?;
		Ok(amount)
	}

	/// Reduce the `asset` balance of `who` by the most that is possible, up to `amount`.
	///
	/// Minimum balance will be respected and the returned imbalance may be up to
	/// `Self::minimum_balance() - 1` greater than `amount`.
	///
	/// Return the imbalance by which the account was reduced.
	fn decrease_balance_at_most(asset: Self::AssetId, who: &AccountId, amount: Self::Balance)
		-> Self::Balance
	{
		let old_balance = Self::balance(asset, who);
		let (mut new_balance, mut amount) = if old_balance < amount {
			(Zero::zero(), old_balance)
		} else {
			(old_balance - amount, amount)
		};
		let minimum_balance = Self::minimum_balance(asset);
		if new_balance < minimum_balance {
			amount = amount.saturating_add(new_balance);
			new_balance = Zero::zero();
		}
		let mut r = Self::set_balance(asset, who, new_balance);
		if r.is_err() {
			// Some error, probably because we tried to destroy an account which cannot be destroyed.
			if amount > minimum_balance {
				new_balance += minimum_balance;
				amount -= minimum_balance;
				r = Self::set_balance(asset, who, new_balance);
			}
			if r.is_err() {
				// Still an error. Apparently it's not possibl to reduce at all.
				amount = Zero::zero();
			}
		}
		amount
	}

	/// Increase the `asset` balance of `who` by `amount`. If it cannot be increased by that amount
	/// for some reason, return `Err` and don't increase it at all. If Ok, return the imbalance.
	///
	/// Minimum balance will be respected and an error will be returned if
	/// `amount < Self::minimum_balance()` when the account of `who` is zero.
	fn increase_balance(asset: Self::AssetId, who: &AccountId, amount: Self::Balance)
		-> Result<Self::Balance, DispatchError>
	{
		let old_balance = Self::balance(asset, who);
		let new_balance = old_balance.saturating_add(amount);
		if new_balance < Self::minimum_balance(asset) {
			return Err(DispatchError::Other("AmountTooLow"))
		}
		if old_balance != new_balance {
			Self::set_balance(asset, who, new_balance)?;
		}
		Ok(amount)
	}

	/// Increase the `asset` balance of `who` by the most that is possible, up to `amount`.
	///
	/// Minimum balance will be respected and the returned imbalance will be zero in the case that
	/// `amount < Self::minimum_balance()`.
	///
	/// Return the imbalance by which the account was increased.
	fn increase_balance_at_most(asset: Self::AssetId, who: &AccountId, amount: Self::Balance)
		-> Self::Balance
	{
		let old_balance = Self::balance(asset, who);
		let mut new_balance = old_balance.saturating_add(amount);
		let mut amount = amount;
		if new_balance < Self::minimum_balance(asset) {
			new_balance = Zero::zero();
			amount = Zero::zero();
		}
		if old_balance == new_balance || Self::set_balance(asset, who, new_balance).is_ok() {
			amount
		} else {
			Zero::zero()
		}
	}
}

pub struct IncreaseIssuance<AccountId, U>(PhantomData<(AccountId, U)>);
impl<AccountId, U: UnbalancedFungibles<AccountId>> HandleImbalanceDrop<U::AssetId, U::Balance> for IncreaseIssuance<AccountId, U> {
	fn handle(asset: U::AssetId, amount: U::Balance) {
		U::set_total_issuance(asset, U::total_issuance(asset).saturating_add(amount))
	}
}
pub struct DecreaseIssuance<AccountId, U>(PhantomData<(AccountId, U)>);
impl<AccountId, U: UnbalancedFungibles<AccountId>> HandleImbalanceDrop<U::AssetId, U::Balance> for DecreaseIssuance<AccountId, U> {
	fn handle(asset: U::AssetId, amount: U::Balance) {
		U::set_total_issuance(asset, U::total_issuance(asset).saturating_sub(amount))
	}
}

type Credit<AccountId, U> = Imbalance<
	<U as InspectFungibles<AccountId>>::AssetId,
	<U as InspectFungibles<AccountId>>::Balance,
	DecreaseIssuance<AccountId, U>,
	IncreaseIssuance<AccountId, U>,
>;

type Debt<AccountId, U> = Imbalance<
	<U as InspectFungibles<AccountId>>::AssetId,
	<U as InspectFungibles<AccountId>>::Balance,
	IncreaseIssuance<AccountId, U>,
	DecreaseIssuance<AccountId, U>,
>;

fn credit<AccountId, U: UnbalancedFungibles<AccountId>>(
	asset: U::AssetId,
	amount: U::Balance,
) -> Credit<AccountId, U> {
	Imbalance { asset, amount, _phantom: PhantomData }
}

fn debt<AccountId, U: UnbalancedFungibles<AccountId>>(
	asset: U::AssetId,
	amount: U::Balance,
) -> Debt<AccountId, U> {
	Imbalance { asset, amount, _phantom: PhantomData }
}

impl<AccountId, U: UnbalancedFungibles<AccountId>> BalancedFungibles<AccountId> for U {
	type OnDropCredit = DecreaseIssuance<AccountId, U>;
	type OnDropDebt = IncreaseIssuance<AccountId, U>;
	fn rescind(asset: Self::AssetId, amount: Self::Balance) -> Debt<AccountId, Self> {
		U::set_total_issuance(asset, U::total_issuance(asset).saturating_sub(amount));
		debt(asset, amount)
	}
	fn issue(asset: Self::AssetId, amount: Self::Balance) -> Credit<AccountId, Self> {
		U::set_total_issuance(asset, U::total_issuance(asset).saturating_add(amount));
		credit(asset, amount)
	}
	fn slash(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance,
	) -> (Credit<AccountId, Self>, Self::Balance) {
		let slashed = U::decrease_balance_at_most(asset, who, amount);
		// `slashed` could be less than, greater than or equal to `amount`.
		// If slashed == amount, it means the account had at least amount in it and it could all be
		//   removed without a problem.
		// If slashed > amount, it means the account had more than amount in it, but not enough more
		//   to push it over minimum_balance.
		// If amount < slashed, it means the account didn't have enough in it to be reduced by
		//   `slashed` without being destroyed.
		(credit(asset, slashed), amount.saturating_sub(slashed))
	}
	fn deposit(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance
	) -> Result<Debt<AccountId, Self>, DispatchError> {
		let increase = U::increase_balance(asset, who, amount)?;
		Ok(debt(asset, increase))
	}
	fn withdraw(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance,
		//TODO: liveness: ExistenceRequirement,
	) -> Result<Credit<AccountId, Self>, DispatchError> {
		let decrease = U::decrease_balance(asset, who, amount)?;
		Ok(credit(asset, decrease))
	}
}

/// Trait for providing a set of named fungible assets which can only be transferred.
pub trait TransferFungibles<AccountId>: InspectFungibles<AccountId> {
	/// Transfer funds from one account into another.
	fn transfer(
		asset: Self::AssetId,
		source: &AccountId,
		dest: &AccountId,
		amount: Self::Balance,
	) -> DispatchResult;
}

/// Trait for providing a set of named fungible assets which can be reserved.
pub trait ReserveFungibles<AccountId>: InspectFungibles<AccountId> {
	/// Amount of funds held in reserve.
	fn reserved_balance(asset: Self::AssetId, who: &AccountId) -> Self::Balance;

	/// Amount of funds held in reserve.
	fn total_balance(asset: Self::AssetId, who: &AccountId) -> Self::Balance;

	/// Check to see if some `amount` of `asset` may be reserved on the account of `who`.
	fn can_reserve(asset: Self::AssetId, who: &AccountId, amount: Self::Balance) -> bool;

	/// Reserve some funds in an account.
	fn reserve(asset: Self::AssetId, who: &AccountId, amount: Self::Balance) -> DispatchResult;

	/// Unreserve some funds in an account.
	fn unreserve(asset: Self::AssetId, who: &AccountId, amount: Self::Balance) -> DispatchResult;

	/// Transfer reserved funds into another account.
	fn repatriate_reserved(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance,
		status: BalanceStatus,
	) -> DispatchResult;
}
