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

//! This module contains functions to meter the storage deposit.

use crate::{storage::ContractInfo, BalanceOf, Config, Error};
use codec::Encode;
use frame_support::{
	dispatch::DispatchError,
	traits::{tokens::BalanceStatus, Currency, ExistenceRequirement, Get, ReservableCurrency},
	DefaultNoBound,
};
use pallet_contracts_primitives::StorageDeposit as Deposit;
use sp_core::crypto::UncheckedFrom;
use sp_runtime::traits::{Saturating, Zero};
use sp_std::marker::PhantomData;

/// Deposit that uses the native currency's balance type.
pub type DepositOf<T> = Deposit<BalanceOf<T>>;

/// A production root storage meter that actually charges from its origin.
pub type Meter<T> = RawMeter<T, ReservingExt, Root>;

/// A poduction nested storage meter that actually charges from its origin.
pub type NestedMeter<T> = RawMeter<T, ReservingExt, Nested>;

/// A poduction storage meter that actually charges from its origin.
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
	/// `min_leftover`: How much `free_balance` in addition to the ed should be left inside the
	/// `origin` account.
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
	/// The balance transfer can either flow from `origin` to `contract` or the other way
	/// around depending on whether `amount` constitutes a `Charge` or a `Refund`.
	/// It is guaranteed that that this succeeds because no more balance than returned by
	/// `check_limit` is ever charged. This is why this function is infallible.
	/// `terminated` designates whether the `contract` was terminated.
	fn charge(
		origin: &T::AccountId,
		contract: &T::AccountId,
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
#[derive(DefaultNoBound)]
pub struct RawMeter<T: Config, E: Ext<T>, S: State> {
	/// The limit of how much balance this meter is allowed to consume.
	limit: BalanceOf<T>,
	/// The amount of balance that was used in this meter and all of its already absorbed children.
	total_deposit: DepositOf<T>,
	/// The amount of balance that was used in this meter alone.
	own_deposit: DepositOf<T>,
	/// Only when a contract was terminated we allow it to drop below the minimum balance.
	terminated: bool,
	/// Type parameters are only used in impls.
	_phantom: PhantomData<(E, S)>,
}

/// This type is used to describe a storage change when charging from the meter.
#[derive(Default)]
pub struct Diff {
	/// How many bytes were added to storage.
	pub bytes_added: u32,
	/// How many bytes were removed from storage.
	pub bytes_removed: u32,
	/// How many storage items were added to storage.
	pub items_added: u32,
	/// How many storage items were removed from storage.
	pub items_removed: u32,
	/// If set to true the derived deposit will always a `Charge` larger than the
	/// the existential deposit.
	pub require_ed: bool,
}

impl Diff {
	/// Calculate how much of a charge or refund results from applying the diff.
	pub fn to_deposit<T: Config>(&self) -> DepositOf<T> {
		let mut deposit = Deposit::default();
		let per_byte = T::DepositPerByte::get();
		let per_item = T::DepositPerItem::get();

		if self.bytes_added > self.bytes_removed {
			deposit = deposit.saturating_add(&Deposit::Charge(
				per_byte.saturating_mul((self.bytes_added - self.bytes_removed).into()),
			));
		} else if self.bytes_removed > self.bytes_added {
			deposit = deposit.saturating_add(&Deposit::Refund(
				per_byte.saturating_mul((self.bytes_removed - self.bytes_added).into()),
			));
		}

		if self.items_added > self.items_removed {
			deposit = deposit.saturating_add(&Deposit::Charge(
				per_item.saturating_mul((self.items_added - self.items_removed).into()),
			));
		} else if self.items_removed > self.items_added {
			deposit = deposit.saturating_add(&Deposit::Refund(
				per_item.saturating_mul((self.items_removed - self.items_added).into()),
			));
		}

		if self.require_ed {
			deposit = deposit.max(Deposit::Charge(T::Currency::minimum_balance()))
		}

		deposit
	}
}

/// Functions that apply to all states.
impl<T, E, S> RawMeter<T, E, S>
where
	T: Config,
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
	E: Ext<T>,
	S: State,
{
	/// Create a new child that has its `limit` set to whatever is remaining of it.
	///
	/// This is called whenever a new subcall is initiated in order to track the storage
	/// usage for this sub call separately. This is necessary because we want to exchange balance
	/// with the current contract we are interacting with.
	pub fn nested(&self) -> RawMeter<T, E, Nested> {
		RawMeter { limit: self.available(), ..Default::default() }
	}

	/// Absorb a child that was spawned to handle a sub call.
	///
	/// This should be called whenever a sub call comes to its end and it is **not** reverted.
	/// This does the actual balance transfer from/to `origin` and `contract` based on the overall
	/// storage consumption of the call. It also updates the supplied contract info.
	///
	/// In case a contract reverted the child meter should just be dropped in order to revert
	/// any changes it recorded.
	///
	/// # Parameters
	///
	/// `absorbed`: The child storage meter that should be absorbed.
	/// `origin`: The origin that spawned the original root meter.
	/// `contract`: The contract that this sub call belongs to.
	/// `info`: The info of the contract in question. `None` if the contract was terminated.
	pub fn absorb(
		&mut self,
		mut absorbed: RawMeter<T, E, Nested>,
		origin: &T::AccountId,
		contract: &T::AccountId,
		info: Option<&mut ContractInfo<T>>,
	) {
		// Absorbing from an existing (non terminated) contract.
		if let Some(info) = info {
			match &mut absorbed.own_deposit {
				Deposit::Charge(amount) =>
					info.storage_deposit = info.storage_deposit.saturating_add(*amount),
				Deposit::Refund(amount) => {
					// We need to make sure to never refund more than what was deposited and
					// still leave the existential deposit inside the contract's account.
					// This case can happen when costs change due to a runtime upgrade where
					// increased costs could remove an account due to refunds.
					let amount = {
						let corrected_amount = (*amount).min(
							info.storage_deposit.saturating_sub(T::Currency::minimum_balance()),
						);
						let correction = (*amount).saturating_sub(corrected_amount);
						absorbed.total_deposit =
							absorbed.total_deposit.saturating_sub(&Deposit::Refund(correction));
						*amount = corrected_amount;
						corrected_amount
					};
					info.storage_deposit = info.storage_deposit.saturating_sub(amount);
				},
			}
		}

		self.total_deposit = self.total_deposit.saturating_add(&absorbed.total_deposit);
		if !absorbed.own_deposit.is_zero() {
			E::charge(origin, &contract, &absorbed.own_deposit, absorbed.terminated);
		}
	}

	/// The amount of balance that is still available from the original `limit`.
	fn available(&self) -> BalanceOf<T> {
		self.total_deposit.available(&self.limit)
	}
}

/// Functions that only apply to the root state.
impl<T, E> RawMeter<T, E, Root>
where
	T: Config,
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
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
		let limit = E::check_limit(&origin, limit, min_leftover)?;
		Ok(Self { limit, ..Default::default() })
	}

	/// The total amount of deposit that should change hands as result of the execution
	/// that this meter was passed into.
	///
	/// This drops the root meter in order to make sure it is only called when the whole
	/// execution did finish.
	pub fn into_deposit(self) -> DepositOf<T> {
		self.total_deposit
	}
}

/// Functions that only apply to the nested state.
impl<T, E> RawMeter<T, E, Nested>
where
	T: Config,
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
	E: Ext<T>,
{
	/// Try to charge the `diff` from the meter. Fails if this would exceed the original limit.
	pub fn charge(&mut self, diff: &Diff) -> Result<DepositOf<T>, DispatchError> {
		debug_assert!(!self.terminated);
		let deposit = diff.to_deposit::<T>();
		let total_deposit = self.total_deposit.saturating_add(&deposit);
		if let Deposit::Charge(amount) = total_deposit {
			if amount > self.limit {
				return Err(<Error<T>>::StorageDepositLimitExhausted.into())
			}
		}
		self.total_deposit = total_deposit;
		self.own_deposit = self.own_deposit.saturating_add(&deposit);
		Ok(deposit)
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
		debug_assert!(!self.terminated);
		let deposit = Diff {
			bytes_added: info.encoded_size() as u32,
			items_added: 1,
			require_ed: true,
			..Default::default()
		}
		.to_deposit::<T>();
		debug_assert!(matches!(deposit, Deposit::Charge(_)));
		// We do not increase `own_deposit` because this will be charged later when the contract
		// execution does conclude.
		let total_deposit = self.total_deposit.saturating_add(&deposit);
		if let Deposit::Charge(amount) = &total_deposit {
			if amount > &self.limit {
				return Err(<Error<T>>::StorageDepositLimitExhausted.into())
			}
		}
		info.storage_deposit = info.storage_deposit.saturating_add(deposit.charge_or_zero());
		self.total_deposit = total_deposit;
		if !deposit.is_zero() {
			// We need to charge immediately so that the account is created before the `value`
			// is transferred from the caller to the contract.
			E::charge(origin, contract, &deposit, false);
		}
		Ok(deposit)
	}

	/// Call to tell the meter that the currently executing contract was executed.
	///
	/// This will manipulate the meter so that all storage deposit accumulated in
	/// `contract_info` will be refunded to the `origin` of the meter.
	pub fn terminate(&mut self, contract_info: &ContractInfo<T>) {
		debug_assert!(!self.terminated);
		let refund = Deposit::Refund(contract_info.storage_deposit);

		// The deposit for `own_deposit` isn't persisted into the contract info until the current
		// frame is dropped. This means that whatever changes were introduced during the
		// current frame are dicarded when terminating.
		self.total_deposit =
			self.total_deposit.saturating_add(&refund).saturating_sub(&self.own_deposit);
		self.own_deposit = refund;
		self.terminated = true;
	}
}

impl<T: Config> Ext<T> for ReservingExt {
	fn check_limit(
		origin: &T::AccountId,
		limit: Option<BalanceOf<T>>,
		min_leftover: BalanceOf<T>,
	) -> Result<BalanceOf<T>, DispatchError> {
		let max = T::Currency::free_balance(origin)
			.saturating_sub(T::Currency::minimum_balance())
			.saturating_sub(min_leftover);
		match limit {
			Some(limit) if limit <= max => Ok(limit),
			None => Ok(max),
			_ => Err(<Error<T>>::StorageDepositNotEnoughFunds.into()),
		}
	}

	fn charge(
		origin: &T::AccountId,
		contract: &T::AccountId,
		amount: &DepositOf<T>,
		terminated: bool,
	) {
		// There is nothing we can do when this fails as this constitutes a bug in the runtime:
		// Either the runtime does not hold up the invariant of never deleting a contract's account
		// or it does not honor reserved balances. We need to settle for emitting an error log
		// in this case.
		match amount {
			Deposit::Charge(amount) => {
				// This will never fail because a contract's account is required to exist
				// at all times. The pallet enforces this invariant by depositing at least the
				// existential deposit when instantiating and never refunds it unless the contract
				// is removed. This means the receiver always exists except when instantiating a
				// contract. In this case we made sure that at least the existential deposit is
				// sent. The sender always has enough balance because we checked that it had enough
				// balance when instantiating the storage meter.
				let result = T::Currency::transfer(
					origin,
					contract,
					*amount,
					ExistenceRequirement::KeepAlive,
				)
				.and_then(|_| T::Currency::reserve(contract, *amount));
				if let Err(err) = result {
					log::error!(
						target: "runtime::contracts",
						"Failed to transfer storage deposit {:?} from origin {:?} to contract {:?}: {:?}",
						amount, origin, contract, err,
					);
				}
			},
			// For `Refund(_)` no error happen because the initial value transfer from the
			// origin to the contract has a keep alive existence requirement and when reserving we
			// make sure to leave at least the ed in the free balance. Therefore the receiver always
			// exists because there is no way for it to be removed in between. The sender always has
			// enough reserved balance because we track it in the `ContractInfo` and never send more
			// back than we have.
			Deposit::Refund(amount) => {
				let amount = if terminated {
					*amount
				} else {
					// This is necessary when the `storage_deposit` tracked inside the account
					// info is out of sync with the actual balance. That can only happen due to
					// slashing. We make sure to never dust the contract's account through a
					// refund because we consider this unexpected behaviour.
					*amount.min(
						&T::Currency::reserved_balance(contract)
							.saturating_sub(T::Currency::minimum_balance()),
					)
				};
				let result =
					T::Currency::repatriate_reserved(contract, origin, amount, BalanceStatus::Free);
				if matches!(result, Ok(val) if !val.is_zero()) || matches!(result, Err(_)) {
					log::error!(
						target: "runtime::contracts",
						"Failed to repatriate storage deposit {:?} from contract {:?} to origin {:?}: {:?}",
						amount, contract, origin, result,
					);
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
	use pretty_assertions::assert_eq;
	use std::cell::RefCell;

	type TestMeter = RawMeter<Test, TestExt, Root>;

	thread_local! {
		static TEST_EXT: RefCell<TestExt> = RefCell::new(Default::default());
	}

	#[derive(Debug, PartialEq, Eq)]
	struct LimitCheck {
		origin: AccountIdOf<Test>,
		limit: BalanceOf<Test>,
		min_leftover: BalanceOf<Test>,
	}

	#[derive(Debug, PartialEq, Eq)]
	struct Charge {
		origin: AccountIdOf<Test>,
		contract: AccountIdOf<Test>,
		amount: DepositOf<Test>,
		terminated: bool,
	}

	#[derive(Default, Debug, PartialEq, Eq)]
	struct TestExt {
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
			TEST_EXT.with(|ext| {
				ext.borrow_mut().limit_checks.push(LimitCheck {
					origin: origin.clone(),
					limit,
					min_leftover,
				})
			});
			Ok(limit)
		}

		fn charge(
			origin: &AccountIdOf<Test>,
			contract: &AccountIdOf<Test>,
			amount: &DepositOf<Test>,
			terminated: bool,
		) {
			TEST_EXT.with(|ext| {
				ext.borrow_mut().charges.push(Charge {
					origin: origin.clone(),
					contract: contract.clone(),
					amount: amount.clone(),
					terminated,
				})
			});
		}
	}

	fn clear_ext() {
		TEST_EXT.with(|ext| ext.borrow_mut().clear())
	}

	fn new_info(deposit: BalanceOf<Test>) -> ContractInfo<Test> {
		use crate::storage::Storage;
		use sp_runtime::traits::Hash;

		ContractInfo::<Test> {
			trie_id: <Storage<Test>>::generate_trie_id(&ALICE, 42),
			code_hash: <Test as frame_system::Config>::Hashing::hash(b"42"),
			storage_deposit: deposit,
		}
	}

	#[test]
	fn new_reserves_balance_works() {
		clear_ext();

		TestMeter::new(&ALICE, Some(1_000), 0).unwrap();

		TEST_EXT.with(|ext| {
			assert_eq!(
				*ext.borrow(),
				TestExt {
					limit_checks: vec![LimitCheck { origin: ALICE, limit: 1_000, min_leftover: 0 }],
					..Default::default()
				}
			)
		});
	}

	#[test]
	fn empty_charge_works() {
		clear_ext();

		let mut meter = TestMeter::new(&ALICE, Some(1_000), 0).unwrap();
		assert_eq!(meter.available(), 1_000);

		// an empty charge foes not create a `Charge` entry
		let mut nested0 = meter.nested();
		nested0.charge(&Default::default()).unwrap();
		meter.absorb(nested0, &ALICE, &BOB, None);

		TEST_EXT.with(|ext| {
			assert_eq!(
				*ext.borrow(),
				TestExt {
					limit_checks: vec![LimitCheck { origin: ALICE, limit: 1_000, min_leftover: 0 }],
					..Default::default()
				}
			)
		});
	}

	#[test]
	fn existential_deposit_works() {
		clear_ext();

		let mut meter = TestMeter::new(&ALICE, Some(1_000), 0).unwrap();
		assert_eq!(meter.available(), 1_000);

		// a `Refund` will be turned into a `Charge(ed)` which is intended behaviour
		let mut nested0 = meter.nested();
		nested0.charge(&Diff { require_ed: true, ..Default::default() }).unwrap();
		nested0
			.charge(&Diff { bytes_removed: 1, require_ed: true, ..Default::default() })
			.unwrap();
		meter.absorb(nested0, &ALICE, &BOB, None);

		TEST_EXT.with(|ext| {
			assert_eq!(
				*ext.borrow(),
				TestExt {
					limit_checks: vec![LimitCheck { origin: ALICE, limit: 1_000, min_leftover: 0 }],
					charges: vec![Charge {
						origin: ALICE,
						contract: BOB,
						amount: Deposit::Charge(<Test as Config>::Currency::minimum_balance() * 2),
						terminated: false,
					}],
					..Default::default()
				}
			)
		});
	}

	#[test]
	fn charging_works() {
		clear_ext();

		let min_balance = <Test as Config>::Currency::minimum_balance();

		let mut meter = TestMeter::new(&ALICE, Some(1_000), 0).unwrap();
		assert_eq!(meter.available(), 1_000);

		let mut nested0_info = new_info(100);
		let mut nested0 = meter.nested();
		nested0
			.charge(&Diff {
				bytes_added: 10,
				bytes_removed: 5,
				items_added: 1,
				items_removed: 2,
				..Default::default()
			})
			.unwrap();
		nested0.charge(&Diff { bytes_removed: 1, ..Default::default() }).unwrap();

		let mut nested1_info = new_info(50);
		let mut nested1 = nested0.nested();
		nested1.charge(&Diff { items_removed: 5, ..Default::default() }).unwrap();
		nested0.absorb(nested1, &ALICE, &CHARLIE, Some(&mut nested1_info));

		// Trying to refund more than is available in the contract will cap the charge
		// to (deposit_in_contract - ed).
		let mut nested2_info = new_info(5);
		let mut nested2 = nested0.nested();
		nested2.charge(&Diff { bytes_removed: 7, ..Default::default() }).unwrap();
		nested0.absorb(nested2, &ALICE, &CHARLIE, Some(&mut nested2_info));

		meter.absorb(nested0, &ALICE, &BOB, Some(&mut nested0_info));

		assert_eq!(nested0_info.storage_deposit, 102);
		assert_eq!(nested1_info.storage_deposit, 40);
		assert_eq!(nested2_info.storage_deposit, min_balance);

		TEST_EXT.with(|ext| {
			assert_eq!(
				*ext.borrow(),
				TestExt {
					limit_checks: vec![LimitCheck { origin: ALICE, limit: 1_000, min_leftover: 0 }],
					charges: vec![
						Charge {
							origin: ALICE,
							contract: CHARLIE,
							amount: Deposit::Refund(10),
							terminated: false
						},
						Charge {
							origin: ALICE,
							contract: CHARLIE,
							amount: Deposit::Refund(4),
							terminated: false
						},
						Charge {
							origin: ALICE,
							contract: BOB,
							amount: Deposit::Charge(2),
							terminated: false
						}
					],
					..Default::default()
				}
			)
		});
	}

	#[test]
	fn termination_works() {
		clear_ext();

		let mut meter = TestMeter::new(&ALICE, Some(1_000), 0).unwrap();
		assert_eq!(meter.available(), 1_000);

		let mut nested0 = meter.nested();
		nested0
			.charge(&Diff {
				bytes_added: 5,
				bytes_removed: 1,
				items_added: 3,
				items_removed: 1,
				..Default::default()
			})
			.unwrap();
		nested0.charge(&Diff { items_added: 2, ..Default::default() }).unwrap();

		let nested1_info = new_info(400);
		let mut nested1 = nested0.nested();
		nested1.charge(&Diff { items_removed: 5, ..Default::default() }).unwrap();
		nested1.charge(&Diff { bytes_added: 20, ..Default::default() }).unwrap();
		nested1.terminate(&nested1_info);
		nested0.absorb(nested1, &ALICE, &CHARLIE, None);

		meter.absorb(nested0, &ALICE, &BOB, None);
		drop(meter);

		TEST_EXT.with(|ext| {
			assert_eq!(
				*ext.borrow(),
				TestExt {
					limit_checks: vec![LimitCheck { origin: ALICE, limit: 1_000, min_leftover: 0 }],
					charges: vec![
						Charge {
							origin: ALICE,
							contract: CHARLIE,
							amount: Deposit::Refund(400),
							terminated: true
						},
						Charge {
							origin: ALICE,
							contract: BOB,
							amount: Deposit::Charge(12),
							terminated: false
						}
					],
					..Default::default()
				}
			)
		});
	}
}
