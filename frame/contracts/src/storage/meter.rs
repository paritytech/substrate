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

//! This module contains functions to meter the storage deposit.

use crate::{
	storage::{ContractInfo, DepositAccount},
	BalanceOf, Config, Error, Inspect, Pallet, System, LOG_TARGET,
};
use codec::Encode;
use frame_support::{
	dispatch::DispatchError,
	ensure,
	traits::{
		tokens::{Fortitude::Polite, Preservation::Protect, WithdrawConsequence},
		Currency, ExistenceRequirement, Get,
	},
	DefaultNoBound, RuntimeDebugNoBound,
};
use pallet_contracts_primitives::StorageDeposit as Deposit;
use sp_runtime::{traits::Saturating, FixedPointNumber, FixedU128};
use sp_std::{marker::PhantomData, vec::Vec};

/// Deposit that uses the native currency's balance type.
pub type DepositOf<T> = Deposit<BalanceOf<T>>;

/// A production root storage meter that actually charges from its origin.
pub type Meter<T> = RawMeter<T, ReservingExt, Root>;

/// A production nested storage meter that actually charges from its origin.
pub type NestedMeter<T> = RawMeter<T, ReservingExt, Nested>;

/// A production storage meter that actually charges from its origin.
///
/// This can be used where we want to be generic over the state (Root vs. Nested).
pub type GenericMeter<T, S> = RawMeter<T, ReservingExt, S>;

/// A trait that allows to decouple the metering from the charging of balance.
///
/// This mostly exists for testing so that the charging can be mocked.
pub trait Ext<T: Config> {
	/// This checks whether `origin` is able to afford the storage deposit limit.
	///
	/// It is necessary to do this check beforehand so that the charge won't fail later on.
	///
	/// `origin`: The origin of the call stack from which is responsible for putting down a deposit.
	/// `limit`: The limit with which the meter was constructed.
	/// `min_leftover`: How much `free_balance` in addition to the existential deposit (ed) should
	/// be left inside the `origin` account.
	///
	/// Returns the limit that should be used by the meter. If origin can't afford the `limit`
	/// it returns `Err`.
	fn check_limit(
		origin: &T::AccountId,
		limit: Option<BalanceOf<T>>,
		min_leftover: BalanceOf<T>,
	) -> Result<BalanceOf<T>, DispatchError>;
	/// This is called to inform the implementer that some balance should be charged due to
	/// some interaction of the `origin` with a `contract`.
	///
	/// The balance transfer can either flow from `origin` to `deposit_account` or the other way
	/// around depending on whether `amount` constitutes a `Charge` or a `Refund`.
	/// It is guaranteed that this succeeds because no more balance than returned by
	/// `check_limit` is ever charged. This is why this function is infallible.
	/// `terminated` designates whether the `contract` was terminated.
	fn charge(
		origin: &T::AccountId,
		deposit_account: &DepositAccount<T>,
		amount: &DepositOf<T>,
		terminated: bool,
	);
}

/// This [`Ext`] is used for actual on-chain execution when balance needs to be charged.
///
/// It uses [`ReservableCurrency`] in order to do accomplish the reserves.
pub enum ReservingExt {}

/// Used to implement a type state pattern for the meter.
///
/// It is sealed and cannot be implemented outside of this module.
pub trait State: private::Sealed {}

/// State parameter that constitutes a meter that is in its root state.
pub enum Root {}

/// State parameter that constitutes a meter that is in its nested state.
pub enum Nested {}

impl State for Root {}
impl State for Nested {}

/// A type that allows the metering of consumed or freed storage of a single contract call stack.
#[derive(DefaultNoBound, RuntimeDebugNoBound)]
pub struct RawMeter<T: Config, E, S: State> {
	/// The limit of how much balance this meter is allowed to consume.
	limit: BalanceOf<T>,
	/// The amount of balance that was used in this meter and all of its already absorbed children.
	total_deposit: DepositOf<T>,
	/// The amount of storage changes that were recorded in this meter alone.
	own_contribution: Contribution<T>,
	/// List of charges that should be applied at the end of a contract stack execution.
	///
	/// We only have one charge per contract hence the size of this vector is
	/// limited by the maximum call depth.
	charges: Vec<Charge<T>>,
	/// Type parameters are only used in impls.
	_phantom: PhantomData<(E, S)>,
}

/// This type is used to describe a storage change when charging from the meter.
#[derive(Default, RuntimeDebugNoBound)]
pub struct Diff {
	/// How many bytes were added to storage.
	pub bytes_added: u32,
	/// How many bytes were removed from storage.
	pub bytes_removed: u32,
	/// How many storage items were added to storage.
	pub items_added: u32,
	/// How many storage items were removed from storage.
	pub items_removed: u32,
}

impl Diff {
	/// Calculate how much of a charge or refund results from applying the diff and store it
	/// in the passed `info` if any.
	///
	/// # Note
	///
	/// In case `None` is passed for `info` only charges are calculated. This is because refunds
	/// are calculated pro rata of the existing storage within a contract and hence need extract
	/// this information from the passed `info`.
	pub fn update_contract<T: Config>(&self, info: Option<&mut ContractInfo<T>>) -> DepositOf<T> {
		let per_byte = T::DepositPerByte::get();
		let per_item = T::DepositPerItem::get();
		let bytes_added = self.bytes_added.saturating_sub(self.bytes_removed);
		let items_added = self.items_added.saturating_sub(self.items_removed);
		let mut bytes_deposit = Deposit::Charge(per_byte.saturating_mul((bytes_added).into()));
		let mut items_deposit = Deposit::Charge(per_item.saturating_mul((items_added).into()));

		// Without any contract info we can only calculate diffs which add storage
		let info = if let Some(info) = info {
			info
		} else {
			debug_assert_eq!(self.bytes_removed, 0);
			debug_assert_eq!(self.items_removed, 0);
			return bytes_deposit.saturating_add(&items_deposit)
		};

		// Refunds are calculated pro rata based on the accumulated storage within the contract
		let bytes_removed = self.bytes_removed.saturating_sub(self.bytes_added);
		let items_removed = self.items_removed.saturating_sub(self.items_added);
		let ratio = FixedU128::checked_from_rational(bytes_removed, info.storage_bytes)
			.unwrap_or_default()
			.min(FixedU128::from_u32(1));
		bytes_deposit = bytes_deposit
			.saturating_add(&Deposit::Refund(ratio.saturating_mul_int(info.storage_byte_deposit)));
		let ratio = FixedU128::checked_from_rational(items_removed, info.storage_items)
			.unwrap_or_default()
			.min(FixedU128::from_u32(1));
		items_deposit = items_deposit
			.saturating_add(&Deposit::Refund(ratio.saturating_mul_int(info.storage_item_deposit)));

		// We need to update the contract info structure with the new deposits
		info.storage_bytes =
			info.storage_bytes.saturating_add(bytes_added).saturating_sub(bytes_removed);
		info.storage_items =
			info.storage_items.saturating_add(items_added).saturating_sub(items_removed);
		match &bytes_deposit {
			Deposit::Charge(amount) =>
				info.storage_byte_deposit = info.storage_byte_deposit.saturating_add(*amount),
			Deposit::Refund(amount) =>
				info.storage_byte_deposit = info.storage_byte_deposit.saturating_sub(*amount),
		}
		match &items_deposit {
			Deposit::Charge(amount) =>
				info.storage_item_deposit = info.storage_item_deposit.saturating_add(*amount),
			Deposit::Refund(amount) =>
				info.storage_item_deposit = info.storage_item_deposit.saturating_sub(*amount),
		}

		bytes_deposit.saturating_add(&items_deposit)
	}
}

impl Diff {
	fn saturating_add(&self, rhs: &Self) -> Self {
		Self {
			bytes_added: self.bytes_added.saturating_add(rhs.bytes_added),
			bytes_removed: self.bytes_removed.saturating_add(rhs.bytes_removed),
			items_added: self.items_added.saturating_add(rhs.items_added),
			items_removed: self.items_removed.saturating_add(rhs.items_removed),
		}
	}
}

/// Records information to charge or refund a plain account.
///
/// All the charges are deferred to the end of a whole call stack. Reason is that by doing
/// this we can do all the refunds before doing any charge. This way a plain account can use
/// more deposit than it has balance as along as it is covered by a refund. This
/// essentially makes the order of storage changes irrelevant with regard to the deposit system.
#[derive(RuntimeDebugNoBound, Clone)]
struct Charge<T: Config> {
	deposit_account: DepositAccount<T>,
	amount: DepositOf<T>,
	terminated: bool,
}

/// Records the storage changes of a storage meter.
#[derive(RuntimeDebugNoBound)]
enum Contribution<T: Config> {
	/// The contract the meter belongs to is alive and accumulates changes using a [`Diff`].
	Alive(Diff),
	/// The meter was checked against its limit using [`RawMeter::enforce_limit`] at the end of
	/// its execution. In this process the [`Diff`] was converted into a [`Deposit`].
	Checked(DepositOf<T>),
	/// The contract was terminated. In this process the [`Diff`] was converted into a [`Deposit`]
	/// in order to calculate the refund.
	Terminated(DepositOf<T>),
}

impl<T: Config> Contribution<T> {
	/// See [`Diff::update_contract`].
	fn update_contract(&self, info: Option<&mut ContractInfo<T>>) -> DepositOf<T> {
		match self {
			Self::Alive(diff) => diff.update_contract::<T>(info),
			Self::Terminated(deposit) | Self::Checked(deposit) => deposit.clone(),
		}
	}
}

impl<T: Config> Default for Contribution<T> {
	fn default() -> Self {
		Self::Alive(Default::default())
	}
}

/// Functions that apply to all states.
impl<T, E, S> RawMeter<T, E, S>
where
	T: Config,
	E: Ext<T>,
	S: State,
{
	/// Create a new child that has its `limit` set to whatever is remaining of it.
	///
	/// This is called whenever a new subcall is initiated in order to track the storage
	/// usage for this sub call separately. This is necessary because we want to exchange balance
	/// with the current contract we are interacting with.
	pub fn nested(&self) -> RawMeter<T, E, Nested> {
		debug_assert!(self.is_alive());
		RawMeter { limit: self.available(), ..Default::default() }
	}

	/// Absorb a child that was spawned to handle a sub call.
	///
	/// This should be called whenever a sub call comes to its end and it is **not** reverted.
	/// This does the actual balance transfer from/to `origin` and `deposit_account` based on the
	/// overall storage consumption of the call. It also updates the supplied contract info.
	///
	/// In case a contract reverted the child meter should just be dropped in order to revert
	/// any changes it recorded.
	///
	/// # Parameters
	///
	/// - `absorbed`: The child storage meter that should be absorbed.
	/// - `origin`: The origin that spawned the original root meter.
	/// - `deposit_account`: The contract's deposit account that this sub call belongs to.
	/// - `info`: The info of the contract in question. `None` if the contract was terminated.
	pub fn absorb(
		&mut self,
		absorbed: RawMeter<T, E, Nested>,
		deposit_account: DepositAccount<T>,
		info: Option<&mut ContractInfo<T>>,
	) {
		let own_deposit = absorbed.own_contribution.update_contract(info);
		self.total_deposit = self
			.total_deposit
			.saturating_add(&absorbed.total_deposit)
			.saturating_add(&own_deposit);
		self.charges.extend_from_slice(&absorbed.charges);
		if !own_deposit.is_zero() {
			self.charges.push(Charge {
				deposit_account,
				amount: own_deposit,
				terminated: absorbed.is_terminated(),
			});
		}
	}

	/// The amount of balance that is still available from the original `limit`.
	fn available(&self) -> BalanceOf<T> {
		self.total_deposit.available(&self.limit)
	}

	/// True if the contract is alive.
	fn is_alive(&self) -> bool {
		matches!(self.own_contribution, Contribution::Alive(_))
	}

	/// True if the contract is terminated.
	fn is_terminated(&self) -> bool {
		matches!(self.own_contribution, Contribution::Terminated(_))
	}
}

/// Functions that only apply to the root state.
impl<T, E> RawMeter<T, E, Root>
where
	T: Config,
	E: Ext<T>,
{
	/// Create new storage meter for the specified `origin` and `limit`.
	///
	/// This tries to [`Ext::check_limit`] on `origin` and fails if this is not possible.
	pub fn new(
		origin: &T::AccountId,
		limit: Option<BalanceOf<T>>,
		min_leftover: BalanceOf<T>,
	) -> Result<Self, DispatchError> {
		let limit = E::check_limit(origin, limit, min_leftover)?;
		Ok(Self { limit, ..Default::default() })
	}

	/// The total amount of deposit that should change hands as result of the execution
	/// that this meter was passed into. This will also perform all the charges accumulated
	/// in the whole contract stack.
	///
	/// This drops the root meter in order to make sure it is only called when the whole
	/// execution did finish.
	pub fn into_deposit(self, origin: &T::AccountId) -> DepositOf<T> {
		for charge in self.charges.iter().filter(|c| matches!(c.amount, Deposit::Refund(_))) {
			E::charge(origin, &charge.deposit_account, &charge.amount, charge.terminated);
		}
		for charge in self.charges.iter().filter(|c| matches!(c.amount, Deposit::Charge(_))) {
			E::charge(origin, &charge.deposit_account, &charge.amount, charge.terminated);
		}
		self.total_deposit
	}
}

/// Functions that only apply to the nested state.
impl<T, E> RawMeter<T, E, Nested>
where
	T: Config,
	E: Ext<T>,
{
	/// Charge `diff` from the meter.
	pub fn charge(&mut self, diff: &Diff) {
		match &mut self.own_contribution {
			Contribution::Alive(own) => *own = own.saturating_add(diff),
			_ => panic!("Charge is never called after termination; qed"),
		};
	}

	/// Charge from `origin` a storage deposit for contract instantiation.
	///
	/// This immediately transfers the balance in order to create the account.
	pub fn charge_instantiate(
		&mut self,
		origin: &T::AccountId,
		contract: &T::AccountId,
		info: &mut ContractInfo<T>,
	) -> Result<DepositOf<T>, DispatchError> {
		debug_assert!(self.is_alive());

		let ed = Pallet::<T>::min_balance();
		let mut deposit =
			Diff { bytes_added: info.encoded_size() as u32, items_added: 1, ..Default::default() }
				.update_contract::<T>(None);

		// Instantiate needs to transfer at least the minimum balance in order to pull the
		// deposit account into existence.
		// We also add another `ed` here which goes to the contract's own account into existence.
		deposit = deposit.max(Deposit::Charge(ed)).saturating_add(&Deposit::Charge(ed));
		if deposit.charge_or_zero() > self.limit {
			return Err(<Error<T>>::StorageDepositLimitExhausted.into())
		}

		// We do not increase `own_contribution` because this will be charged later when the
		// contract execution does conclude and hence would lead to a double charge.
		self.total_deposit = deposit.clone();
		info.storage_base_deposit = deposit.charge_or_zero();

		// Usually, deposit charges are deferred to be able to coalesce them with refunds.
		// However, we need to charge immediately so that the account is created before
		// charges possibly below the ed are collected and fail.
		E::charge(
			origin,
			info.deposit_account(),
			&deposit.saturating_sub(&Deposit::Charge(ed)),
			false,
		);
		System::<T>::inc_consumers(info.deposit_account())?;

		// We also need to make sure that the contract's account itself exists.
		T::Currency::transfer(origin, contract, ed, ExistenceRequirement::KeepAlive)?;
		System::<T>::inc_consumers(contract)?;

		Ok(deposit)
	}

	/// Call to tell the meter that the currently executing contract was executed.
	///
	/// This will manipulate the meter so that all storage deposit accumulated in
	/// `contract_info` will be refunded to the `origin` of the meter.
	pub fn terminate(&mut self, info: &ContractInfo<T>) {
		debug_assert!(self.is_alive());
		self.own_contribution = Contribution::Terminated(Deposit::Refund(info.total_deposit()));
	}

	/// [`Self::charge`] does not enforce the storage limit since we want to do this check as late
	/// as possible to allow later refunds to offset earlier charges.
	///
	/// # Note
	///
	/// We only need to call this **once** for every call stack and not for every cross contract
	/// call. Hence this is only called when the last call frame returns.
	pub fn enforce_limit(
		&mut self,
		info: Option<&mut ContractInfo<T>>,
	) -> Result<(), DispatchError> {
		let deposit = self.own_contribution.update_contract(info);
		let total_deposit = self.total_deposit.saturating_add(&deposit);
		// We don't want to override a `Terminated` with a `Checked`.
		if self.is_alive() {
			self.own_contribution = Contribution::Checked(deposit);
		}
		if let Deposit::Charge(amount) = total_deposit {
			if amount > self.limit {
				return Err(<Error<T>>::StorageDepositLimitExhausted.into())
			}
		}
		Ok(())
	}
}

impl<T: Config> Ext<T> for ReservingExt {
	fn check_limit(
		origin: &T::AccountId,
		limit: Option<BalanceOf<T>>,
		min_leftover: BalanceOf<T>,
	) -> Result<BalanceOf<T>, DispatchError> {
		// We are sending the `min_leftover` and the `min_balance` from the origin
		// account as part of a contract call. Hence origin needs to have those left over
		// as free balance after accounting for all deposits.
		let max = T::Currency::reducible_balance(origin, Protect, Polite)
			.saturating_sub(min_leftover)
			.saturating_sub(Pallet::<T>::min_balance());
		let limit = limit.unwrap_or(max);
		ensure!(
			limit <= max &&
				matches!(T::Currency::can_withdraw(origin, limit), WithdrawConsequence::Success),
			<Error<T>>::StorageDepositNotEnoughFunds,
		);
		Ok(limit)
	}

	fn charge(
		origin: &T::AccountId,
		deposit_account: &DepositAccount<T>,
		amount: &DepositOf<T>,
		terminated: bool,
	) {
		// There is nothing we can do when this fails as this constitutes a bug in the runtime.
		// We need to settle for emitting an error log in this case.
		//
		// # Note
		//
		// This is infallible because it is called in a part of the execution where we cannot
		// simply roll back. It might make sense to do some refactoring to move the deposit
		// collection to the fallible part of execution.
		match amount {
			Deposit::Charge(amount) => {
				// This will never fail because a deposit account is required to exist
				// at all times. The pallet enforces this invariant by holding a consumer reference
				// on the deposit account as long as the contract exists.
				//
				// The sender always has enough balance because we checked that it had enough
				// balance when instantiating the storage meter. There is no way for the sender
				// which is a plain account to send away this balance in the meantime.
				let result = T::Currency::transfer(
					origin,
					deposit_account,
					*amount,
					ExistenceRequirement::KeepAlive,
				);
				if let Err(err) = result {
					log::error!(
						target: LOG_TARGET,
						"Failed to transfer storage deposit {:?} from origin {:?} to deposit account {:?}: {:?}",
						amount, origin, deposit_account, err,
					);
					if cfg!(debug_assertions) {
						panic!("Unable to collect storage deposit. This is a bug.");
					}
				}
			},
			// The receiver always exists because the initial value transfer from the
			// origin to the contract has a keep alive existence requirement. When taking a deposit
			// we make sure to leave at least the ed in the free balance.
			//
			// The sender always has enough balance because we track it in the `ContractInfo` and
			// never send more back than we have. No one has access to the deposit account. Hence no
			// other interaction with this account takes place.
			Deposit::Refund(amount) => {
				if terminated {
					System::<T>::dec_consumers(&deposit_account);
				}
				let result = T::Currency::transfer(
					deposit_account,
					origin,
					*amount,
					// We can safely use `AllowDeath` because our own consumer prevents an removal.
					ExistenceRequirement::AllowDeath,
				);
				if matches!(result, Err(_)) {
					log::error!(
						target: LOG_TARGET,
						"Failed to refund storage deposit {:?} from deposit account {:?} to origin {:?}: {:?}",
						amount, deposit_account, origin, result,
					);
					if cfg!(debug_assertions) {
						panic!("Unable to refund storage deposit. This is a bug.");
					}
				}
			},
		};
	}
}

mod private {
	pub trait Sealed {}
	impl Sealed for super::Root {}
	impl Sealed for super::Nested {}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		exec::AccountIdOf,
		tests::{Test, ALICE, BOB, CHARLIE},
	};
	use frame_support::parameter_types;
	use pretty_assertions::assert_eq;

	type TestMeter = RawMeter<Test, TestExt, Root>;

	parameter_types! {
		static TestExtTestValue: TestExt = Default::default();
	}

	#[derive(Debug, PartialEq, Eq, Clone)]
	struct LimitCheck {
		origin: AccountIdOf<Test>,
		limit: BalanceOf<Test>,
		min_leftover: BalanceOf<Test>,
	}

	#[derive(Debug, PartialEq, Eq, Clone)]
	struct Charge {
		origin: AccountIdOf<Test>,
		contract: DepositAccount<Test>,
		amount: DepositOf<Test>,
		terminated: bool,
	}

	#[derive(Default, Debug, PartialEq, Eq, Clone)]
	pub struct TestExt {
		limit_checks: Vec<LimitCheck>,
		charges: Vec<Charge>,
	}

	impl TestExt {
		fn clear(&mut self) {
			self.limit_checks.clear();
			self.charges.clear();
		}
	}

	impl Ext<Test> for TestExt {
		fn check_limit(
			origin: &AccountIdOf<Test>,
			limit: Option<BalanceOf<Test>>,
			min_leftover: BalanceOf<Test>,
		) -> Result<BalanceOf<Test>, DispatchError> {
			let limit = limit.unwrap_or(42);
			TestExtTestValue::mutate(|ext| {
				ext.limit_checks
					.push(LimitCheck { origin: origin.clone(), limit, min_leftover })
			});
			Ok(limit)
		}

		fn charge(
			origin: &AccountIdOf<Test>,
			contract: &DepositAccount<Test>,
			amount: &DepositOf<Test>,
			terminated: bool,
		) {
			TestExtTestValue::mutate(|ext| {
				ext.charges.push(Charge {
					origin: origin.clone(),
					contract: contract.clone(),
					amount: amount.clone(),
					terminated,
				})
			});
		}
	}

	fn clear_ext() {
		TestExtTestValue::mutate(|ext| ext.clear())
	}

	#[derive(Default)]
	struct StorageInfo {
		bytes: u32,
		items: u32,
		bytes_deposit: BalanceOf<Test>,
		items_deposit: BalanceOf<Test>,
	}

	fn new_info(info: StorageInfo) -> ContractInfo<Test> {
		ContractInfo::<Test> {
			trie_id: Default::default(),
			deposit_account: DepositAccount([0u8; 32].into()),
			code_hash: Default::default(),
			storage_bytes: info.bytes,
			storage_items: info.items,
			storage_byte_deposit: info.bytes_deposit,
			storage_item_deposit: info.items_deposit,
			storage_base_deposit: Default::default(),
		}
	}

	#[test]
	fn new_reserves_balance_works() {
		clear_ext();

		TestMeter::new(&ALICE, Some(1_000), 0).unwrap();

		assert_eq!(
			TestExtTestValue::get(),
			TestExt {
				limit_checks: vec![LimitCheck { origin: ALICE, limit: 1_000, min_leftover: 0 }],
				..Default::default()
			}
		)
	}

	#[test]
	fn empty_charge_works() {
		clear_ext();

		let mut meter = TestMeter::new(&ALICE, Some(1_000), 0).unwrap();
		assert_eq!(meter.available(), 1_000);

		// an empty charge does not create a `Charge` entry
		let mut nested0 = meter.nested();
		nested0.charge(&Default::default());
		meter.absorb(nested0, DepositAccount(BOB), None);

		assert_eq!(
			TestExtTestValue::get(),
			TestExt {
				limit_checks: vec![LimitCheck { origin: ALICE, limit: 1_000, min_leftover: 0 }],
				..Default::default()
			}
		)
	}

	#[test]
	fn charging_works() {
		clear_ext();

		let mut meter = TestMeter::new(&ALICE, Some(100), 0).unwrap();
		assert_eq!(meter.available(), 100);

		let mut nested0_info =
			new_info(StorageInfo { bytes: 100, items: 5, bytes_deposit: 100, items_deposit: 10 });
		let mut nested0 = meter.nested();
		nested0.charge(&Diff {
			bytes_added: 108,
			bytes_removed: 5,
			items_added: 1,
			items_removed: 2,
		});
		nested0.charge(&Diff { bytes_removed: 99, ..Default::default() });

		let mut nested1_info =
			new_info(StorageInfo { bytes: 100, items: 10, bytes_deposit: 100, items_deposit: 20 });
		let mut nested1 = nested0.nested();
		nested1.charge(&Diff { items_removed: 5, ..Default::default() });
		nested0.absorb(nested1, DepositAccount(CHARLIE), Some(&mut nested1_info));

		let mut nested2_info =
			new_info(StorageInfo { bytes: 100, items: 7, bytes_deposit: 100, items_deposit: 20 });
		let mut nested2 = nested0.nested();
		nested2.charge(&Diff { items_removed: 7, ..Default::default() });
		nested0.absorb(nested2, DepositAccount(CHARLIE), Some(&mut nested2_info));

		nested0.enforce_limit(Some(&mut nested0_info)).unwrap();
		meter.absorb(nested0, DepositAccount(BOB), Some(&mut nested0_info));

		meter.into_deposit(&ALICE);

		assert_eq!(nested0_info.extra_deposit(), 112);
		assert_eq!(nested1_info.extra_deposit(), 110);
		assert_eq!(nested2_info.extra_deposit(), 100);

		assert_eq!(
			TestExtTestValue::get(),
			TestExt {
				limit_checks: vec![LimitCheck { origin: ALICE, limit: 100, min_leftover: 0 }],
				charges: vec![
					Charge {
						origin: ALICE,
						contract: DepositAccount(CHARLIE),
						amount: Deposit::Refund(10),
						terminated: false
					},
					Charge {
						origin: ALICE,
						contract: DepositAccount(CHARLIE),
						amount: Deposit::Refund(20),
						terminated: false
					},
					Charge {
						origin: ALICE,
						contract: DepositAccount(BOB),
						amount: Deposit::Charge(2),
						terminated: false
					}
				]
			}
		)
	}

	#[test]
	fn termination_works() {
		clear_ext();

		let mut meter = TestMeter::new(&ALICE, Some(1_000), 0).unwrap();
		assert_eq!(meter.available(), 1_000);

		let mut nested0 = meter.nested();
		nested0.charge(&Diff {
			bytes_added: 5,
			bytes_removed: 1,
			items_added: 3,
			items_removed: 1,
		});
		nested0.charge(&Diff { items_added: 2, ..Default::default() });

		let mut nested1_info =
			new_info(StorageInfo { bytes: 100, items: 10, bytes_deposit: 100, items_deposit: 20 });
		let mut nested1 = nested0.nested();
		nested1.charge(&Diff { items_removed: 5, ..Default::default() });
		nested1.charge(&Diff { bytes_added: 20, ..Default::default() });
		nested1.terminate(&nested1_info);
		nested0.enforce_limit(Some(&mut nested1_info)).unwrap();
		nested0.absorb(nested1, DepositAccount(CHARLIE), None);

		meter.absorb(nested0, DepositAccount(BOB), None);
		meter.into_deposit(&ALICE);

		assert_eq!(
			TestExtTestValue::get(),
			TestExt {
				limit_checks: vec![LimitCheck { origin: ALICE, limit: 1_000, min_leftover: 0 }],
				charges: vec![
					Charge {
						origin: ALICE,
						contract: DepositAccount(CHARLIE),
						amount: Deposit::Refund(119),
						terminated: true
					},
					Charge {
						origin: ALICE,
						contract: DepositAccount(BOB),
						amount: Deposit::Charge(12),
						terminated: false
					}
				]
			}
		)
	}
}
