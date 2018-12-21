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

//! Environment definition of the wasm smart-contract runtime.

use super::{BalanceOf, Schedule, CreateReceipt, Error, Ext};
use rstd::prelude::*;
use codec::{Decode, Encode};
use gas::{GasMeter, GasMeterResult};
use runtime_primitives::traits::{As, CheckedMul};
use sandbox;
use system;
use Trait;

type GasOf<E> = <<E as Ext>::T as Trait>::Gas;

/// Enumerates all possible *special* trap conditions.
///
/// In this runtime traps used not only for signaling about errors but also
/// to just terminate quickly in some cases.
enum SpecialTrap {
	/// Signals that trap was generated in response to call `ext_return` host function.
	Return,
}

pub(crate) struct Runtime<'a, 'data, E: Ext + 'a> {
	ext: &'a mut E,
	input_data: &'data [u8],
	output_data: &'data mut Vec<u8>,
	scratch_buf: Vec<u8>,
	schedule: &'a Schedule<<E::T as Trait>::Gas>,
	memory: sandbox::Memory,
	gas_meter: &'a mut GasMeter<E::T>,
	special_trap: Option<SpecialTrap>,
}
impl<'a, 'data, E: Ext + 'a> Runtime<'a, 'data, E> {
	pub(crate) fn new(
		ext: &'a mut E,
		input_data: &'data [u8],
		output_data: &'data mut Vec<u8>,
		schedule: &'a Schedule<<E::T as Trait>::Gas>,
		memory: sandbox::Memory,
		gas_meter: &'a mut GasMeter<E::T>,
	) -> Self {
		Runtime {
			ext,
			input_data,
			output_data,
			scratch_buf: Vec::new(),
			schedule,
			memory,
			gas_meter,
			special_trap: None,
		}
	}

	fn memory(&self) -> &sandbox::Memory {
		&self.memory
	}
}

pub(crate) fn to_execution_result<E: Ext>(
	runtime: Runtime<E>,
	sandbox_err: Option<sandbox::Error>,
) -> Result<(), Error> {
	// Check the exact type of the error. It could be plain trap or
	// special runtime trap the we must recognize.
	match (sandbox_err, runtime.special_trap) {
		// No traps were generated. Proceed normally.
		(None, None) => Ok(()),
		// Special case. The trap was the result of the execution `return` host function.
		(Some(sandbox::Error::Execution), Some(SpecialTrap::Return)) => Ok(()),
		// Any other kind of a trap should result in a failure.
		(Some(_), _) => Err(Error::Invoke),
		// Any other case (such as special trap flag without actual trap) signifies
		// a logic error.
		_ => unreachable!(),
	}
}

/// Charge the specified amount of gas.
///
/// Returns `Err` if there is not enough gas.
fn charge_gas<T: Trait>(
	gas_meter: &mut GasMeter<T>,
	amount: T::Gas,
) -> Result<(), sandbox::HostError> {
	match gas_meter.charge(amount) {
		GasMeterResult::Proceed => Ok(()),
		GasMeterResult::OutOfGas => Err(sandbox::HostError),
	}
}

/// Read designated chunk from the sandbox memory, consuming an appropriate amount of
/// gas.
///
/// Returns `Err` if one of the following conditions occurs:
///
/// - calculating the gas cost resulted in overflow.
/// - out of gas
/// - requested buffer is not within the bounds of the sandbox memory.
fn read_sandbox_memory<E: Ext>(
	ctx: &mut Runtime<E>,
	ptr: u32,
	len: u32,
) -> Result<Vec<u8>, sandbox::HostError> {
	let price = (ctx.schedule.sandbox_data_read_cost)
		.checked_mul(&<GasOf<E> as As<u32>>::sa(len))
		.ok_or(sandbox::HostError)?;
	charge_gas(ctx.gas_meter, price)?;

	let mut buf = Vec::new();
	buf.resize(len as usize, 0);

	ctx.memory().get(ptr, &mut buf)?;

	Ok(buf)
}

/// Write the given buffer to the designated location in the sandbox memory, consuming
/// an appropriate amount of gas.
///
/// Returns `Err` if one of the following conditions occurs:
///
/// - calculating the gas cost resulted in overflow.
/// - out of gas
/// - designated area is not within the bounds of the sandbox memory.
fn write_sandbox_memory<T: Trait>(
	per_byte_cost: T::Gas,
	gas_meter: &mut GasMeter<T>,
	memory: &sandbox::Memory,
	ptr: u32,
	buf: &[u8],
) -> Result<(), sandbox::HostError> {
	let price = per_byte_cost
		.checked_mul(&<T::Gas as As<u32>>::sa(buf.len() as u32))
		.ok_or(sandbox::HostError)?;
	charge_gas(gas_meter, price)?;

	memory.set(ptr, buf)?;

	Ok(())
}

// ***********************************************************
// * AFTER MAKING A CHANGE MAKE SURE TO UPDATE COMPLEXITY.MD *
// ***********************************************************

// TODO: ext_balance, ext_address, ext_callvalue, etc.

// Define a function `fn init_env<E: Ext>() -> HostFunctionSet<E>` that returns
// a function set which can be imported by an executed contract.
define_env!(init_env, <E: Ext>,

	// Account for used gas. Traps if gas used is greater than gas limit.
	//
	// - amount: How much gas is used.
	gas(ctx, amount: u32) => {
		let amount = <<E::T as Trait>::Gas as As<u32>>::sa(amount);
		charge_gas(&mut ctx.gas_meter, amount)?;

		Ok(())
	},

	// Change the value at the given key in the storage or remove the entry.
	//
	// - key_ptr: pointer into the linear
	//   memory where the location of the requested value is placed.
	// - value_non_null: if set to 0, then the entry
	//   at the given location will be removed.
	// - value_ptr: pointer into the linear memory
	//   where the value to set is placed. If `value_non_null` is set to 0, then this parameter is ignored.
	// - value_len: the length of the value. If `value_non_null` is set to 0, then this parameter is ignored.
	ext_set_storage(ctx, key_ptr: u32, value_non_null: u32, value_ptr: u32, value_len: u32) => {
		let key = read_sandbox_memory(ctx, key_ptr, 32)?;
		let value =
			if value_non_null != 0 {
				Some(read_sandbox_memory(ctx, value_ptr, value_len)?)
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
		let key = read_sandbox_memory(ctx, key_ptr, 32)?;
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
		let callee = {
			let callee_buf = read_sandbox_memory(ctx, callee_ptr, callee_len)?;
			<<E as Ext>::T as system::Trait>::AccountId::decode(&mut &callee_buf[..])
				.ok_or_else(|| sandbox::HostError)?
		};
		let value = {
			let value_buf = read_sandbox_memory(ctx, value_ptr, value_len)?;
			BalanceOf::<<E as Ext>::T>::decode(&mut &value_buf[..])
				.ok_or_else(|| sandbox::HostError)?
		};
		let input_data = read_sandbox_memory(ctx, input_data_ptr, input_data_len)?;

		// Clear the scratch buffer in any case.
		ctx.scratch_buf.clear();

		let nested_gas_limit = if gas == 0 {
			ctx.gas_meter.gas_left()
		} else {
			<<E::T as Trait>::Gas as As<u64>>::sa(gas)
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
		let init_code = read_sandbox_memory(ctx, init_code_ptr, init_code_len)?;
		let value = {
			let value_buf = read_sandbox_memory(ctx, value_ptr, value_len)?;
			BalanceOf::<<E as Ext>::T>::decode(&mut &value_buf[..])
				.ok_or_else(|| sandbox::HostError)?
		};
		let input_data = read_sandbox_memory(ctx, input_data_ptr, input_data_len)?;

		// Clear the scratch buffer in any case.
		ctx.scratch_buf.clear();

		let nested_gas_limit = if gas == 0 {
			ctx.gas_meter.gas_left()
		} else {
			<<E::T as Trait>::Gas as As<u64>>::sa(gas)
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

	// Save a data buffer as a result of the execution, terminate the execution and return a
	// successful result to the caller.
	ext_return(ctx, data_ptr: u32, data_len: u32) => {
		let data_len_in_gas = <<E::T as Trait>::Gas as As<u64>>::sa(data_len as u64);
		let price = (ctx.schedule.return_data_per_byte_cost)
			.checked_mul(&data_len_in_gas)
			.ok_or(sandbox::HostError)?;

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

	// Stores the address of the caller into the scratch buffer.
	//
	// If this is a top-level call (i.e. initiated by an extrinsic) the origin address of the extrinsic
	// will be returned. Otherwise, if this call is initiated by another contract then the address
	// of the contract will be returned.
	ext_caller(ctx) => {
		ctx.scratch_buf = ctx.ext.caller().encode();
		Ok(())
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

		// Finally, perform the write.
		write_sandbox_memory(
			ctx.schedule.sandbox_data_write_cost,
			ctx.gas_meter,
			&ctx.memory,
			dest_ptr,
			src,
		)?;

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

		// Finally, perform the write.
		write_sandbox_memory(
			ctx.schedule.sandbox_data_write_cost,
			ctx.gas_meter,
			&ctx.memory,
			dest_ptr,
			src,
		)?;

		Ok(())
	},
);
