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

use super::{CodeOf, ContractAddressFor, Trait};
use account_db::{AccountDb, ChangeSet, OverlayAccountDb};
use rstd::prelude::*;
use runtime_support::StorageMap;
use vm;

//pub struct TransactionData {
// tx_origin
// tx_gas_price
// block_number
// timestamp
// etc
//}

pub struct CreateReceipt<T: Trait> {
	address: T::AccountId,
	gas_left: u64,
}

pub struct ExecutionContext<'a, 'b: 'a, T: Trait + 'b> {
	// aux for the first transaction.
	pub _caller: T::AccountId,
	// typically should be dest
	pub self_account: T::AccountId,
	pub account_db: &'a mut OverlayAccountDb<'b, T>,
	pub gas_price: u64,
	pub depth: usize,
}

impl<'a, 'b: 'a, T: Trait> ExecutionContext<'a, 'b, T> {
	/// Make a call to the specified address.
	pub fn call(
		&mut self,
		dest: T::AccountId,
		_value: T::Balance,
		gas_limit: u64,
		_data: Vec<u8>,
	) -> Result<vm::ExecutionResult, ()> {
		let dest_code = <CodeOf<T>>::get(&dest);

		// TODO: transfer `_value` using `overlay`. Return an error if failed.
		// TODO: check the new depth

		let (exec_result, change_set) = if !dest_code.is_empty() {
			let mut overlay = OverlayAccountDb::new(self.account_db);
			let exec_result = {
				let mut nested = ExecutionContext {
					account_db: &mut overlay,
					_caller: self.self_account.clone(),
					self_account: dest.clone(),
					gas_price: self.gas_price,
					depth: self.depth + 1,
				};
				vm::execute(&dest_code, &mut nested, gas_limit).map_err(|_| ())?
			};

			// TODO: Need to propagate gas_left.
			// TODO: Need to return result buffer.

			(exec_result, overlay.into_change_set())
		} else {
			// that was a plain transfer
			(
				vm::ExecutionResult {
					gas_left: gas_limit,
					return_data: Vec::new(),
				},
				ChangeSet::new(),
			)
		};

		self.account_db.commit(change_set);

		Ok(exec_result)
	}

	pub fn create(
		&mut self,
		_endownment: T::Balance,
		gas_limit: u64,
		ctor: &[u8],
		_data: &[u8],
	) -> Result<CreateReceipt<T>, ()> {
		let dest = T::DetermineContractAddress2::contract_address_for(ctor, &self.self_account);

		// TODO: staking::effect_create with endownment at the specified address with the specified
		// endownment.

		// TODO: What if the address already exists?
		// TODO: check the new depth

		let (exec_result, change_set) = {
			let mut overlay = OverlayAccountDb::new(self.account_db);
			let exec_result = {
				let mut nested = ExecutionContext {
					account_db: &mut overlay,
					_caller: self.self_account.clone(),
					self_account: dest.clone(),
					gas_price: self.gas_price,
					depth: self.depth + 1,
				};
				vm::execute(ctor, &mut nested, gas_limit).map_err(|_| ())?
			};

			(exec_result, overlay.into_change_set())
		};

		self.account_db
			.set_code(&dest, exec_result.return_data().to_vec());
		self.account_db.commit(change_set);

		Ok(CreateReceipt {
			address: dest,
			gas_left: exec_result.gas_left,
		})
	}
}

impl<'a, 'b: 'a, T: Trait + 'b> vm::Ext for ExecutionContext<'a, 'b, T> {
	type AccountId = T::AccountId;
	type Balance = T::Balance;

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
		endownment: Self::Balance,
	) -> Result<vm::CreateReceipt<T::AccountId>, ()> {
		// TODO: Pass it
		let gas_limit: u64 = 100_000;
		let input_data: Vec<u8> = Vec::new();

		let receipt = self.create(endownment, gas_limit, code, &input_data)?;
		Ok(vm::CreateReceipt {
			address: receipt.address,
			gas_left: receipt.gas_left,
		})
	}

	fn call(
		&mut self,
		to: &Self::AccountId,
		value: Self::Balance,
		gas_limit: u64,
		input_data: Vec<u8>,
	) -> Result<vm::ExecutionResult, ()> {
		self.call(to.clone(), value, gas_limit, input_data)
	}
}
