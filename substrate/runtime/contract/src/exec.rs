// Copyright 2018 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

use super::{CodeOf, MaxDepth, ContractAddressFor, Module, Trait};
use account_db::{AccountDb, OverlayAccountDb};
use gas::GasMeter;
use vm;

use rstd::prelude::*;
use runtime_primitives::traits::{Zero, CheckedAdd, CheckedSub};
use runtime_support::{StorageMap, StorageValue};
use balances::{self, EnsureAccountLiquid};

pub struct CreateReceipt<T: Trait> {
	pub address: T::AccountId,
}

pub struct CallReceipt {
	pub return_data: Vec<u8>,
}

pub struct ExecutionContext<'a, T: Trait + 'a> {
	// typically should be dest
	pub self_account: T::AccountId,
	pub overlay: OverlayAccountDb<'a, T>,
	pub depth: usize,
}

impl<'a, T: Trait> ExecutionContext<'a, T> {
	/// Make a call to the specified address.
	pub fn call(
		&mut self,
		caller: T::AccountId,
		dest: T::AccountId,
		value: T::Balance,
		gas_meter: &mut GasMeter<T>,
		data: &[u8],
	) -> Result<CallReceipt, &'static str> {
		if self.depth == <MaxDepth<T>>::get() as usize {
			return Err("reached maximum depth, cannot make a call");
		}

		let call_base_fee = <Module<T>>::call_base_fee();
		if gas_meter.charge(call_base_fee).is_out_of_gas() {
			return Err("not enough gas to pay base call fee");
		}

		let dest_code = <CodeOf<T>>::get(&dest);

		let (exec_result, change_set) = {
			let mut overlay = OverlayAccountDb::new(&self.overlay);

			if value > T::Balance::zero() {
				transfer(
					gas_meter,
					false,
					&self.self_account,
					&dest,
					value,
					&mut overlay,
				)?;
			}

			let mut nested = ExecutionContext {
				overlay: overlay,
				self_account: dest.clone(),
				depth: self.depth + 1,
			};
			let exec_result = if !dest_code.is_empty() {
				vm::execute(
					&dest_code,
					data,
					&mut CallContext {
						ctx: &mut nested,
						_caller: caller,
					},
					gas_meter,
				).map_err(|_| "vm execute returned error while call")?
			} else {
				// that was a plain transfer
				vm::ExecutionResult {
					return_data: Vec::new(),
				}
			};

			(exec_result, nested.overlay.into_change_set())
		};

		self.overlay.commit(change_set);

		Ok(CallReceipt {
			return_data: exec_result.return_data,
		})
	}

	pub fn create(
		&mut self,
		caller: T::AccountId,
		endowment: T::Balance,
		gas_meter: &mut GasMeter<T>,
		ctor: &[u8],
		data: &[u8],
	) -> Result<CreateReceipt<T>, &'static str> {
		if self.depth == <MaxDepth<T>>::get() as usize {
			return Err("reached maximum depth, cannot create");
		}

		let create_base_fee = <Module<T>>::create_base_fee();
		if gas_meter.charge(create_base_fee).is_out_of_gas() {
			return Err("not enough gas to pay base create fee");
		}

		let dest = T::DetermineContractAddress::contract_address_for(ctor, &self.self_account);
		if <CodeOf<T>>::exists(&dest) {
			// TODO: Is it enough?
			return Err("contract already exists");
		}

		let change_set = {
			let mut overlay = OverlayAccountDb::new(&self.overlay);

			if endowment > T::Balance::zero() {
				transfer(
					gas_meter,
					true,
					&self.self_account,
					&dest,
					endowment,
					&mut overlay,
				)?;
			}

			let mut nested = ExecutionContext {
				overlay: overlay,
				self_account: dest.clone(),
				depth: self.depth + 1,
			};
			let exec_result = {
				vm::execute(
					ctor,
					data,
					&mut CallContext {
						ctx: &mut nested,
						_caller: caller,
					},
					gas_meter,
				).map_err(|_| "vm execute returned error while create")?
			};

			nested.overlay.set_code(&dest, exec_result.return_data);
			nested.overlay.into_change_set()
		};

		self.overlay.commit(change_set);

		Ok(CreateReceipt {
			address: dest,
		})
	}
}

fn transfer<T: Trait>(
	gas_meter: &mut GasMeter<T>,
	contract_create: bool,
	transactor: &T::AccountId,
	dest: &T::AccountId,
	value: T::Balance,
	overlay: &mut OverlayAccountDb<T>,
) -> Result<(), &'static str> {
	let would_create = overlay.get_balance(transactor).is_zero();

	let fee: T::Balance = if contract_create {
		<Module<T>>::contract_fee()
	} else {
		if would_create {
			<balances::Module<T>>::creation_fee()
		} else {
			<balances::Module<T>>::transfer_fee()
		}
	};

	if gas_meter.charge_by_balance(fee).is_out_of_gas() {
		return Err("not enough gas to pay transfer fee");
	}

	let from_balance = overlay.get_balance(transactor);
	let new_from_balance = match from_balance.checked_sub(&value) {
		Some(b) => b,
		None => return Err("balance too low to send value"),
	};
	if would_create && value < <balances::Module<T>>::existential_deposit() {
		return Err("value too low to create account");
	}
	<T as balances::Trait>::EnsureAccountLiquid::ensure_account_liquid(transactor)?;

	let to_balance = overlay.get_balance(dest);
	let new_to_balance = match to_balance.checked_add(&value) {
		Some(b) => b,
		None => return Err("destination balance too high to receive value"),
	};

	if transactor != dest {
		overlay.set_balance(transactor, new_from_balance);
		overlay.set_balance(dest, new_to_balance);
	}

	Ok(())
}

struct CallContext<'a, 'b: 'a, T: Trait + 'b> {
	ctx: &'a mut ExecutionContext<'b, T>,
	_caller: T::AccountId,
}

impl<'a, 'b: 'a, T: Trait + 'b> vm::Ext for CallContext<'a, 'b, T> {
	type T = T;

	fn get_storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.ctx.overlay.get_storage(&self.ctx.self_account, key)
	}

	fn set_storage(&mut self, key: &[u8], value: Option<Vec<u8>>) {
		self.ctx
			.overlay
			.set_storage(&self.ctx.self_account, key.to_vec(), value)
	}

	fn create(
		&mut self,
		code: &[u8],
		endowment: T::Balance,
		gas_meter: &mut GasMeter<T>,
		data: &[u8],
	) -> Result<CreateReceipt<T>, ()> {
		let caller = self.ctx.self_account.clone();
		self.ctx
			.create(caller, endowment, gas_meter, code, &data)
			.map_err(|_| ())
	}

	fn call(
		&mut self,
		to: &T::AccountId,
		value: T::Balance,
		gas_meter: &mut GasMeter<T>,
		data: &[u8],
	) -> Result<CallReceipt, ()> {
		let caller = self.ctx.self_account.clone();
		self.ctx
			.call(caller, to.clone(), value, gas_meter, data)
			.map_err(|_| ())
	}
}
