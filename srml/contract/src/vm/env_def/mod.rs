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

use super::{SpecialTrap, BalanceOf, CreateReceipt, Ext, GasMeterResult, Runtime};
use codec::{Encode, Decode};
use parity_wasm::elements::{FunctionType, ValueType};
use rstd::prelude::*;
use rstd::collections::btree_map::BTreeMap;
use runtime_primitives::traits::{As, CheckedMul};
use sandbox::{self, TypedValue};
use system;
use Trait;

#[macro_use]
mod macros;

pub trait ConvertibleToWasm: Sized {
	const VALUE_TYPE: ValueType;
	type NativeType;
	fn to_typed_value(self) -> TypedValue;
	fn from_typed_value(TypedValue) -> Option<Self>;
}
impl ConvertibleToWasm for i32 {
	type NativeType = i32;
	const VALUE_TYPE: ValueType = ValueType::I32;
	fn to_typed_value(self) -> TypedValue {
		TypedValue::I32(self)
	}
	fn from_typed_value(v: TypedValue) -> Option<Self> {
		v.as_i32()
	}
}
impl ConvertibleToWasm for u32 {
	type NativeType = u32;
	const VALUE_TYPE: ValueType = ValueType::I32;
	fn to_typed_value(self) -> TypedValue {
		TypedValue::I32(self as i32)
	}
	fn from_typed_value(v: TypedValue) -> Option<Self> {
		match v {
			TypedValue::I32(v) => Some(v as u32),
			_ => None,
		}
	}
}
impl ConvertibleToWasm for u64 {
	type NativeType = u64;
	const VALUE_TYPE: ValueType = ValueType::I64;
	fn to_typed_value(self) -> TypedValue {
		TypedValue::I64(self as i64)
	}
	fn from_typed_value(v: TypedValue) -> Option<Self> {
		match v {
			TypedValue::I64(v) => Some(v as u64),
			_ => None,
		}
	}
}

/// Represents a set of function that defined in this particular environment and
/// which can be imported and called by the module.
pub(crate) struct HostFunctionSet<E: Ext> {
	/// Functions which defined in the environment.
	pub funcs: BTreeMap<Vec<u8>, HostFunction<E>>,
}
impl<E: Ext> HostFunctionSet<E> {
	pub fn new() -> Self {
		HostFunctionSet {
			funcs: BTreeMap::new(),
		}
	}
}

pub(crate) struct HostFunction<E: Ext> {
	pub(crate) f: fn(&mut Runtime<E>, &[sandbox::TypedValue])
		-> Result<sandbox::ReturnValue, sandbox::HostError>,
	func_type: FunctionType,
}
impl<E: Ext> HostFunction<E> {
	/// Create a new instance of a host function.
	pub fn new(
		func_type: FunctionType,
		f: fn(&mut Runtime<E>, &[sandbox::TypedValue])
			-> Result<sandbox::ReturnValue, sandbox::HostError>,
	) -> Self {
		HostFunction { func_type, f }
	}

	/// Returns a function pointer of this host function.
	pub fn raw_fn_ptr(
		&self,
	) -> fn(&mut Runtime<E>, &[sandbox::TypedValue])
		-> Result<sandbox::ReturnValue, sandbox::HostError> {
		self.f
	}

	/// Check if the this function could be invoked with the given function signature.
	pub fn func_type_matches(&self, func_type: &FunctionType) -> bool {
		&self.func_type == func_type
	}
}

// TODO: ext_balance, ext_address, ext_callvalue, etc.

// Define a function `fn init_env<E: Ext>() -> HostFunctionSet<E>` that returns
// a function set which can be imported by an executed contract.
define_env!(init_env, <E: Ext>,

	// Account for used gas. Traps if gas used is greater than gas limit.
	//
	// - amount: How much gas is used.
	gas(ctx, amount: u32) => {
		let amount = <<<E as Ext>::T as Trait>::Gas as As<u32>>::sa(amount);

		match ctx.gas_meter.charge(amount) {
			GasMeterResult::Proceed => Ok(()),
			GasMeterResult::OutOfGas => Err(sandbox::HostError),
		}
	},

	// Change the value at the given location in storage or remove it.
	//
	// - location_ptr: pointer into the linear
	//   memory where the location of the requested value is placed.
	// - value_non_null: if set to 0, then the entry
	//   at the given location will be removed.
	// - value_ptr: pointer into the linear memory
	//   where the value to set is placed. If `value_non_null` is set to 0, then this parameter is ignored.
	// - value_len: the length of the value. If `value_non_null` is set to 0, then this parameter is ignored.
	ext_set_storage(ctx, key_ptr: u32, value_non_null: u32, value_ptr: u32, value_len: u32) => {
		let mut key = [0; 32];
		ctx.memory().get(key_ptr, &mut key)?;

		let value = if value_non_null != 0 {
			let mut value_buf = Vec::new();
			value_buf.resize(value_len as usize, 0);
			ctx.memory().get(value_ptr, &mut value_buf)?;
			Some(value_buf)
		} else {
			None
		};
		ctx.ext.set_storage(&key, value);

		Ok(())
	},

	// Retrieve the value at the given location from the strorage and return 0.
	// If there is no entry at the given location then this function will return 1 and
	// clear the scratch buffer.
	//
	// - key_ptr: pointer into the linear memory where the key
	//   of the requested value is placed.
	ext_get_storage(ctx, key_ptr: u32) -> u32 => {
		let mut key = [0; 32];
		ctx.memory().get(key_ptr, &mut key)?;

		if let Some(value) = ctx.ext.get_storage(&key) {
			ctx.scratch_buf = value;
			Ok(0)
		} else {
			ctx.scratch_buf.clear();
			Ok(1)
		}
	},

	// Make a call to another contract.
	//
	// Returns 0 on the successful execution and puts the result data returned
	// by the callee into the scratch buffer. Otherwise, returns 1 and clears the scratch
	// buffer.
	//
	// - callee_ptr: a pointer to the address of the callee contract.
	//   Should be decodable as an `T::AccountId`. Traps otherwise.
	// - callee_len: length of the address buffer.
	// - gas: how much gas to devote to the execution.
	// - value_ptr: a pointer to the buffer with value, how much value to send.
	//   Should be decodable as a `T::Balance`. Traps otherwise.
	// - value_len: length of the value buffer.
	// - input_data_ptr: a pointer to a buffer to be used as input data to the callee.
	// - input_data_len: length of the input data buffer.
	ext_call(
		ctx,
		callee_ptr: u32,
		callee_len: u32,
		gas: u64,
		value_ptr: u32,
		value_len: u32,
		input_data_ptr: u32,
		input_data_len: u32
	) -> u32 => {
		let mut callee = Vec::new();
		callee.resize(callee_len as usize, 0);
		ctx.memory().get(callee_ptr, &mut callee)?;
		let callee =
			<<E as Ext>::T as system::Trait>::AccountId::decode(&mut &callee[..])
				.ok_or_else(|| sandbox::HostError)?;

		let mut value_buf = Vec::new();
		value_buf.resize(value_len as usize, 0);
		ctx.memory().get(value_ptr, &mut value_buf)?;
		let value = BalanceOf::<<E as Ext>::T>::decode(&mut &value_buf[..])
			.ok_or_else(|| sandbox::HostError)?;

		let mut input_data = Vec::new();
		input_data.resize(input_data_len as usize, 0u8);
		ctx.memory().get(input_data_ptr, &mut input_data)?;

		// Clear the scratch buffer in any case.
		ctx.scratch_buf.clear();

		let nested_gas_limit = if gas == 0 {
			ctx.gas_meter.gas_left()
		} else {
			<<<E as Ext>::T as Trait>::Gas as As<u64>>::sa(gas)
		};
		let ext = &mut ctx.ext;
		let scratch_buf = &mut ctx.scratch_buf;
		let call_outcome = ctx.gas_meter.with_nested(nested_gas_limit, |nested_meter| {
			match nested_meter {
				Some(nested_meter) => ext.call(&callee, value, nested_meter, &input_data, scratch_buf),
				// there is not enough gas to allocate for the nested call.
				None => Err(()),
			}
		});

		match call_outcome {
			Ok(()) => Ok(0),
			Err(_) => Ok(1),
		}
	},

	// Create a contract with code returned by the specified initializer code.
	//
	// This function creates an account and executes initializer code. After the execution,
	// the returned buffer is saved as the code of the created account.
	//
	// Returns 0 on the successful contract creation and puts the address
	// of the created contract into the scratch buffer.
	// Otherwise, returns 1 and clears the scratch buffer.
	//
	// - init_code_ptr: a pointer to the buffer that contains the initializer code.
	// - init_code_len: length of the initializer code buffer.
	// - gas: how much gas to devote to the execution of the initializer code.
	// - value_ptr: a pointer to the buffer with value, how much value to send.
	//   Should be decodable as a `T::Balance`. Traps otherwise.
	// - value_len: length of the value buffer.
	// - input_data_ptr: a pointer to a buffer to be used as input data to the initializer code.
	// - input_data_len: length of the input data buffer.
	ext_create(
		ctx,
		init_code_ptr: u32,
		init_code_len: u32,
		gas: u64,
		value_ptr: u32,
		value_len: u32,
		input_data_ptr: u32,
		input_data_len: u32
	) -> u32 => {
		let mut value_buf = Vec::new();
		value_buf.resize(value_len as usize, 0);
		ctx.memory().get(value_ptr, &mut value_buf)?;
		let value = BalanceOf::<<E as Ext>::T>::decode(&mut &value_buf[..])
			.ok_or_else(|| sandbox::HostError)?;

		let mut init_code = Vec::new();
		init_code.resize(init_code_len as usize, 0u8);
		ctx.memory().get(init_code_ptr, &mut init_code)?;

		let mut input_data = Vec::new();
		input_data.resize(input_data_len as usize, 0u8);
		ctx.memory().get(input_data_ptr, &mut input_data)?;

		// Clear the scratch buffer in any case.
		ctx.scratch_buf.clear();

		let nested_gas_limit = if gas == 0 {
			ctx.gas_meter.gas_left()
		} else {
			<<<E as Ext>::T as Trait>::Gas as As<u64>>::sa(gas)
		};
		let ext = &mut ctx.ext;
		let create_outcome = ctx.gas_meter.with_nested(nested_gas_limit, |nested_meter| {
			match nested_meter {
				Some(nested_meter) => ext.create(&init_code, value, nested_meter, &input_data),
				// there is not enough gas to allocate for the nested call.
				None => Err(()),
			}
		});
		match create_outcome {
			Ok(CreateReceipt { address }) => {
				// Write the address to the scratch buffer.
				address.encode_to(&mut ctx.scratch_buf);
				Ok(0)
			},
			Err(_) => Ok(1),
		}
	},

	// Save a data buffer as a result of the execution.
	ext_return(ctx, data_ptr: u32, data_len: u32) => {
		let data_len_in_gas = <<<E as Ext>::T as Trait>::Gas as As<u64>>::sa(data_len as u64);
		let price = (ctx.config.return_data_per_byte_cost)
			.checked_mul(&data_len_in_gas)
			.ok_or_else(|| sandbox::HostError)?;

		match ctx.gas_meter.charge(price) {
			GasMeterResult::Proceed => (),
			GasMeterResult::OutOfGas => return Err(sandbox::HostError),
		}

		ctx.output_data.resize(data_len as usize, 0);
		ctx.memory.get(data_ptr, &mut ctx.output_data)?;

		ctx.special_trap = Some(SpecialTrap::Return);

		// The trap mechanism is used to immediately terminate the execution.
		// This trap should be handled appropriately before returning the result
		// to the user of this crate.
		Err(sandbox::HostError)
	},

	// Returns the size of the input buffer.
	ext_input_size(ctx) -> u32 => {
		Ok(ctx.input_data.len() as u32)
	},

	// Copy data from the input buffer starting from `offset` with length `len` into the contract memory.
	// The region at which the data should be put is specified by `dest_ptr`.
	ext_input_copy(ctx, dest_ptr: u32, offset: u32, len: u32) => {
		let offset = offset as usize;
		if offset > ctx.input_data.len() {
			// Offset can't be larger than input buffer length.
			return Err(sandbox::HostError);
		}

		// This can't panic since `offset <= ctx.input_data.len()`.
		let src = &ctx.input_data[offset..];
		if src.len() != len as usize {
			return Err(sandbox::HostError);
		}

		ctx.memory().set(dest_ptr, src)?;

		Ok(())
	},

	// Returns the size of the scratch buffer.
	ext_scratch_size(ctx) -> u32 => {
		Ok(ctx.scratch_buf.len() as u32)
	},

	// Copy data from the scratch buffer starting from `offset` with length `len` into the contract memory.
	// The region at which the data should be put is specified by `dest_ptr`.
	ext_scratch_copy(ctx, dest_ptr: u32, offset: u32, len: u32) => {
		let offset = offset as usize;
		if offset > ctx.scratch_buf.len() {
			// Offset can't be larger than scratch buffer length.
			return Err(sandbox::HostError);
		}

		// This can't panic since `offset <= ctx.scratch_buf.len()`.
		let src = &ctx.scratch_buf[offset..];
		if src.len() != len as usize {
			return Err(sandbox::HostError);
		}

		ctx.memory().set(dest_ptr, src)?;

		Ok(())
	},
);
