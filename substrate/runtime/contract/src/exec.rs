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

use super::{CodeOf, ContractAddressFor, Module, Trait};
use account_db::{AccountDb, OverlayAccountDb};
use gas::GasMeter;
use vm;

use rstd::prelude::*;
use runtime_primitives::traits::Zero;
use runtime_support::StorageMap;
use staking;
use system;

pub struct CreateReceipt<T: Trait> {
	pub address: T::AccountId,
	pub gas_left: T::Gas,
}

pub struct ExecutionContext<'a, 'b: 'a, T: Trait + 'b> {
	// aux for the first transaction.
	pub _caller: T::AccountId,
	// typically should be dest
	pub self_account: T::AccountId,
	pub account_db: &'a mut OverlayAccountDb<'b, T>,
	pub depth: usize,
}

impl<'a, 'b: 'a, T: Trait> ExecutionContext<'a, 'b, T> {
	/// Make a call to the specified address.
	pub fn call(
		&mut self,
		dest: T::AccountId,
		value: T::Balance,
		gas_meter: &mut GasMeter<T>,
		_data: Vec<u8>,
	) -> Result<vm::ExecutionResult, &'static str> {
		let dest_code = <CodeOf<T>>::get(&dest);

		// TODO: check the new depth

		let call_base_fee = <Module<T>>::call_base_fee();
		if gas_meter.charge(call_base_fee).is_out_of_gas() {
			return Err("not enough gas to pay base call fee");
		}

		let (exec_result, change_set) = {
			let mut overlay = OverlayAccountDb::new(self.account_db);

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

			let exec_result = if !dest_code.is_empty() {
				let mut nested = ExecutionContext {
					account_db: &mut overlay,
					_caller: self.self_account.clone(),
					self_account: dest.clone(),
					depth: self.depth + 1,
				};

				vm::execute(&dest_code, &mut nested, gas_meter)
					.map_err(|_| "vm execute returned error while call")?
			} else {
				// that was a plain transfer
				vm::ExecutionResult {
					return_data: Vec::new(),
				}
			};

			(exec_result, overlay.into_change_set())
		};

		self.account_db.commit(change_set);

		Ok(exec_result)
	}

	pub fn create(
		&mut self,
		endownment: T::Balance,
		gas_meter: &mut GasMeter<T>,
		ctor: &[u8],
		_data: &[u8],
	) -> Result<CreateReceipt<T>, &'static str> {
		// TODO: check the new depth

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
			let mut overlay = OverlayAccountDb::new(self.account_db);

			if endownment > T::Balance::zero() {
				transfer(
					gas_meter,
					true,
					&self.self_account,
					&dest,
					endownment,
					&mut overlay,
				)?;
			}

			let exec_result = {
				let mut nested = ExecutionContext {
					account_db: &mut overlay,
					_caller: self.self_account.clone(),
					self_account: dest.clone(),
					depth: self.depth + 1,
				};
				vm::execute(ctor, &mut nested, gas_meter)
					.map_err(|_| "vm execute returned error while call")?
			};

			overlay.set_code(&dest, exec_result.return_data().to_vec());

			overlay.into_change_set()
		};

		self.account_db.commit(change_set);

		Ok(CreateReceipt {
			address: dest,
			gas_left: gas_meter.gas_left(),
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
			<staking::Module<T>>::creation_fee()
		} else {
			<staking::Module<T>>::transfer_fee()
		}
	};

	if gas_meter.charge_by_balance(fee).is_out_of_gas() {
		return Err("not enough gas to pay transfer fee");
	}

	let from_balance = overlay.get_balance(transactor);
	if from_balance < value {
		return Err("balance too low to send value");
	}
	if would_create && value < <staking::Module<T>>::existential_deposit() {
		return Err("value too low to create account");
	}
	if <staking::Module<T>>::bondage(transactor) > <system::Module<T>>::block_number() {
		return Err("bondage too high to send value");
	}

	let to_balance = overlay.get_balance(dest);
	if to_balance + value <= to_balance {
		return Err("destination balance too high to receive value");
	}

	if transactor != dest {
		overlay.set_balance(transactor, from_balance - value);
		overlay.set_balance(dest, to_balance + value);
	}

	Ok(())
}

impl<'a, 'b: 'a, T: Trait + 'b> vm::Ext<T> for ExecutionContext<'a, 'b, T> {
	fn get_storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.account_db.get_storage(&self.self_account, key)
	}

	fn set_storage(&mut self, key: &[u8], value: Option<Vec<u8>>) {
		self.account_db
			.set_storage(&self.self_account, key.to_vec(), value)
	}

	fn create(
		&mut self,
		code: &[u8],
		endownment: T::Balance,
		gas_meter: &mut GasMeter<T>,
		data: Vec<u8>,
	) -> Result<vm::CreateReceipt<T::AccountId, T::Gas>, ()> {
		let receipt = self
			.create(endownment, gas_meter, code, &data)
			.map_err(|_| ())?;
		Ok(vm::CreateReceipt {
			address: receipt.address,
			gas_left: receipt.gas_left,
		})
	}

	fn call(
		&mut self,
		to: &T::AccountId,
		value: T::Balance,
		gas_meter: &mut GasMeter<T>,
		data: Vec<u8>,
	) -> Result<vm::ExecutionResult, ()> {
		self.call(to.clone(), value, gas_meter, data)
			.map_err(|_| ())
	}
}
