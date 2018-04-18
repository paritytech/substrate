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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Smart-contract execution module.

use codec::Slicable;
use primitives::traits::As;
use rstd::prelude::*;
use sandbox;
use {AccountDb, Module, OverlayAccountDb, Trait};

struct ExecutionExt<'a, 'b: 'a, T: Trait + 'b> {
	account_db: &'a mut OverlayAccountDb<'b, T>,
	account: T::AccountId,
	memory: sandbox::Memory,
}
impl<'a, 'b: 'a, T: Trait> ExecutionExt<'a, 'b, T> {
	fn account(&self) -> &T::AccountId {
		&self.account
	}
	fn account_db(&self) -> &OverlayAccountDb<T> {
		self.account_db
	}
	fn account_db_mut(&mut self) -> &mut OverlayAccountDb<'b, T> {
		self.account_db
	}
	fn memory(&self) -> &sandbox::Memory {
		&self.memory
	}
}

pub(crate) fn execute<'a, 'b: 'a, T: Trait>(
	code: &[u8],
	account: &T::AccountId,
	account_db: &'a mut OverlayAccountDb<'b, T>,
) -> bool {
	// ext_put_storage(location_ptr: u32, value_non_null: u32, value_ptr: u32);
	//
	// Change the value at the given location in storage or remove it.
	//
	// - location_ptr: pointer into the linear
	//   memory where the location of the requested value is placed.
	// - value_non_null: if set to 0, then the entry
	//   at the given location will be removed.
	// - value_ptr: pointer into the linear memory
	//   where the value to set is placed. If `value_non_null` is set to 0, then this parameter is ignored.
	fn ext_set_storage<T: Trait>(e: &mut ExecutionExt<T>, args: &[sandbox::TypedValue]) -> Result<sandbox::ReturnValue, sandbox::HostError> {
		let location_ptr = args[0].as_i32().unwrap() as u32;
		let value_non_null = args[1].as_i32().unwrap() as u32;
		let value_ptr = args[2].as_i32().unwrap() as u32;

		let mut location = [0; 32];

		e.memory().get(location_ptr, &mut location)?;
		let account = e.account().clone();

		if value_non_null != 0 {
			let mut value = [0; 32];
			e.memory().get(value_ptr, &mut value)?;
			e.account_db_mut()
				.set_storage(&account, location.to_vec(), Some(value.to_vec()));
		} else {
			e.account_db_mut()
				.set_storage(&account, location.to_vec(), None);
		}

		Ok(sandbox::ReturnValue::Unit)
	}

	// ext_get_storage(location_ptr: u32, dest_ptr: u32);
	//
	// Retrieve the value at the given location from the strorage.
	// If there is no entry at the given location then all-zero-value
	// will be returned.
	//
	// - location_ptr: pointer into the linear
	//   memory where the location of the requested value is placed.
	// - dest_ptr: pointer where contents of the specified storage location
	//   should be placed.
	fn ext_get_storage<T: Trait>(e: &mut ExecutionExt<T>, args: &[sandbox::TypedValue]) -> Result<sandbox::ReturnValue, sandbox::HostError> {
		let location_ptr = args[0].as_i32().unwrap() as u32;
		let dest_ptr = args[1].as_i32().unwrap() as u32;

		let mut location = [0; 32];
		e.memory().get(location_ptr, &mut location)?;

		let account = e.account().clone();
		if let Some(value) = e.account_db_mut().get_storage(&account, &location) {
			e.memory().set(dest_ptr, &value)?;
		} else {
			e.memory().set(dest_ptr, &[0u8; 32])?;
		}

		Ok(sandbox::ReturnValue::Unit)
	}

	// ext_transfer(transfer_to: u32, transfer_to_len: u32, value: u32)
	fn ext_transfer<T: Trait>(e: &mut ExecutionExt<T>, args: &[sandbox::TypedValue]) -> Result<sandbox::ReturnValue, sandbox::HostError> {
		let transfer_to_ptr = args[0].as_i32().unwrap() as u32;
		let transfer_to_len = args[1].as_i32().unwrap() as u32;
		let value = args[2].as_i32().unwrap() as u64;

		// TODO: slicable
		let mut transfer_to = Vec::new();
		transfer_to.resize(transfer_to_len as usize, 0);
		e.memory().get(transfer_to_ptr, &mut transfer_to)?;
		let value = T::Balance::sa(value as usize);
		let transfer_to = T::AccountId::decode(&mut &transfer_to[..]).unwrap();

		let account = e.account().clone();
		if let Some(commit_state) =
			Module::<T>::effect_transfer(&account, &transfer_to, value, e.account_db())
		{
			e.account_db_mut().merge(commit_state);
		}

		Ok(sandbox::ReturnValue::Unit)
	}

	// ext_create(code_ptr: u32, code_len: u32, value: u32)
	fn ext_create<T: Trait>(e: &mut ExecutionExt<T>, args: &[sandbox::TypedValue]) -> Result<sandbox::ReturnValue, sandbox::HostError> {
		let code_ptr = args[0].as_i32().unwrap() as u32;
		let code_len = args[1].as_i32().unwrap() as u32;
		let value = args[2].as_i32().unwrap() as u32;

		// TODO: slicable
		let value = T::Balance::sa(value as usize);

		let mut code = Vec::new();
		code.resize(code_len as usize, 0u8);
		e.memory().get(code_ptr, &mut code)?;

		let account = e.account().clone();
		if let Some(commit_state) =
			Module::<T>::effect_create(&account, &code, value, e.account_db())
		{
			e.account_db_mut().merge(commit_state);
		}

		Ok(sandbox::ReturnValue::Unit)
	}

	// TODO: Inspect the binary to extract the initial page count.
	let memory = match sandbox::Memory::new(1, None) {
		Ok(memory) => memory,
		Err(_) => return false,
	};

	let mut imports = sandbox::EnvironmentDefinitionBuilder::new();
	imports.add_host_func("env", "ext_set_storage", ext_set_storage::<T>);
	imports.add_host_func("env", "ext_get_storage", ext_get_storage::<T>);
	imports.add_host_func("env", "ext_transfer", ext_transfer::<T>);
	imports.add_host_func("env", "ext_create", ext_create::<T>);
	// TODO: ext_balance, ext_address, ext_callvalue, etc.
	imports.add_memory("env", "memory", memory.clone());

	let mut exec_ext = ExecutionExt {
		account: account.clone(),
		account_db,
		memory,
	};

	let mut instance = match sandbox::Instance::new(code, &imports, &mut exec_ext) {
		Ok(instance) => instance,
		Err(_err) => return false,
	};
	instance.invoke(b"call", &[], &mut exec_ext).is_ok()
}
