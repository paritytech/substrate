// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

use crate::{Schedule, Trait, CodeHash, BalanceOf, Error};
use crate::exec::{
	Ext, ExecResult, ExecReturnValue, StorageKey, TopicOf, ReturnFlags,
};
use crate::gas::{Gas, GasMeter, Token, GasMeterResult};
use crate::wasm::env_def::ConvertibleToWasm;
use sp_sandbox;
use parity_wasm::elements::ValueType;
use frame_system;
use frame_support::dispatch::DispatchError;
use sp_std::prelude::*;
use codec::{Decode, Encode};
use sp_runtime::traits::{Bounded, SaturatedConversion};
use sp_io::hashing::{
	keccak_256,
	blake2_256,
	blake2_128,
	sha2_256,
};

/// Every error that can be returned from a runtime API call.
#[repr(u32)]
pub enum ReturnCode {
	/// API call successful.
	Success = 0,
	/// The called function trapped and has its state changes reverted.
	/// In this case no output buffer is returned.
	/// Can only be returned from `ext_call` and `ext_instantiate`.
	CalleeTrapped = 1,
	/// The called function ran to completion but decided to revert its state.
	/// An output buffer is returned when one was supplied.
	/// Can only be returned from `ext_call` and `ext_instantiate`.
	CalleeReverted = 2,
	/// The passed key does not exist in storage.
	KeyNotFound = 3,
}

impl ConvertibleToWasm for ReturnCode {
	type NativeType = Self;
	const VALUE_TYPE: ValueType = ValueType::I32;
	fn to_typed_value(self) -> sp_sandbox::Value {
		sp_sandbox::Value::I32(self as i32)
	}
	fn from_typed_value(_: sp_sandbox::Value) -> Option<Self> {
		debug_assert!(false, "We will never receive a ReturnCode but only send it to wasm.");
		None
	}
}

impl From<ExecReturnValue> for ReturnCode {
	fn from(from: ExecReturnValue) -> ReturnCode {
		if from.flags.contains(ReturnFlags::REVERT) {
			Self::CalleeReverted
		} else {
			Self::Success
		}
	}
}

/// The data passed through when a contract uses `ext_return`.
struct ReturnData {
	/// The flags as passed through by the contract. They are still unchecked and
	/// will later be parsed into a `ReturnFlags` bitflags struct.
	flags: u32,
	/// The output buffer passed by the contract as return data.
	data: Vec<u8>,
}

/// Enumerates all possible reasons why a trap was generated.
///
/// This is either used to supply the caller with more information about why an error
/// occurred (the SupervisorError variant).
/// The other case is where the trap does not constitute an error but rather was invoked
/// as a quick way to terminate the application (all other variants).
enum TrapReason {
	/// The supervisor trapped the contract because of an error condition occurred during
	/// execution in privileged code.
	SupervisorError(DispatchError),
	/// Signals that trap was generated in response to call `ext_return` host function.
	Return(ReturnData),
	/// Signals that a trap was generated in response to a succesful call to the
	/// `ext_terminate` host function.
	Termination,
	/// Signals that a trap was generated because of a successful restoration.
	Restoration,
}

/// Can only be used for one call.
pub(crate) struct Runtime<'a, E: Ext + 'a> {
	ext: &'a mut E,
	input_data: Option<Vec<u8>>,
	schedule: &'a Schedule,
	memory: sp_sandbox::Memory,
	gas_meter: &'a mut GasMeter<E::T>,
	trap_reason: Option<TrapReason>,
}
impl<'a, E: Ext + 'a> Runtime<'a, E> {
	pub(crate) fn new(
		ext: &'a mut E,
		input_data: Vec<u8>,
		schedule: &'a Schedule,
		memory: sp_sandbox::Memory,
		gas_meter: &'a mut GasMeter<E::T>,
	) -> Self {
		Runtime {
			ext,
			input_data: Some(input_data),
			schedule,
			memory,
			gas_meter,
			trap_reason: None,
		}
	}
}

pub(crate) fn to_execution_result<E: Ext>(
	runtime: Runtime<E>,
	sandbox_result: Result<sp_sandbox::ReturnValue, sp_sandbox::Error>,
) -> ExecResult {
	match runtime.trap_reason {
		// The trap was the result of the execution `return` host function.
		Some(TrapReason::Return(ReturnData{ flags, data })) => {
			let flags = ReturnFlags::from_bits(flags).ok_or_else(||
				"used reserved bit in return flags"
			)?;
			return Ok(ExecReturnValue {
				flags,
				data,
			})
		},
		Some(TrapReason::Termination) => {
			return Ok(ExecReturnValue {
				flags: ReturnFlags::empty(),
				data: Vec::new(),
			})
		},
		Some(TrapReason::Restoration) => {
			return Ok(ExecReturnValue {
				flags: ReturnFlags::empty(),
				data: Vec::new(),
			})
		}
		Some(TrapReason::SupervisorError(error)) => Err(error)?,
		None => (),
	}

	// Check the exact type of the error.
	match sandbox_result {
		// No traps were generated. Proceed normally.
		Ok(_) => {
			Ok(ExecReturnValue { flags: ReturnFlags::empty(), data: Vec::new() })
		}
		// `Error::Module` is returned only if instantiation or linking failed (i.e.
		// wasm binary tried to import a function that is not provided by the host).
		// This shouldn't happen because validation process ought to reject such binaries.
		//
		// Because panics are really undesirable in the runtime code, we treat this as
		// a trap for now. Eventually, we might want to revisit this.
		Err(sp_sandbox::Error::Module) =>
			Err("validation error")?,
		// Any other kind of a trap should result in a failure.
		Err(sp_sandbox::Error::Execution) | Err(sp_sandbox::Error::OutOfBounds) =>
			Err("contract trapped during execution")?,
	}
}

#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
#[derive(Copy, Clone)]
pub enum RuntimeToken {
	/// Explicit call to the `gas` function. Charge the gas meter
	/// with the value provided.
	Explicit(u32),
	/// The given number of bytes is read from the sandbox memory.
	ReadMemory(u32),
	/// The given number of bytes is written to the sandbox memory.
	WriteMemory(u32),
	/// The given number of bytes is read from the sandbox memory and
	/// is returned as the return data buffer of the call.
	ReturnData(u32),
	/// (topic_count, data_bytes): A buffer of the given size is posted as an event indexed with the
	/// given number of topics.
	DepositEvent(u32, u32),
}

impl<T: Trait> Token<T> for RuntimeToken {
	type Metadata = Schedule;

	fn calculate_amount(&self, metadata: &Schedule) -> Gas {
		use self::RuntimeToken::*;
		let value = match *self {
			Explicit(amount) => Some(amount.into()),
			ReadMemory(byte_count) => metadata
				.sandbox_data_read_cost
				.checked_mul(byte_count.into()),
			WriteMemory(byte_count) => metadata
				.sandbox_data_write_cost
				.checked_mul(byte_count.into()),
			ReturnData(byte_count) => metadata
				.return_data_per_byte_cost
				.checked_mul(byte_count.into()),
			DepositEvent(topic_count, data_byte_count) => {
				let data_cost = metadata
					.event_data_per_byte_cost
					.checked_mul(data_byte_count.into());

				let topics_cost = metadata
					.event_per_topic_cost
					.checked_mul(topic_count.into());

				data_cost
					.and_then(|data_cost| {
						topics_cost.and_then(|topics_cost| {
							data_cost.checked_add(topics_cost)
						})
					})
					.and_then(|data_and_topics_cost|
						data_and_topics_cost.checked_add(metadata.event_base_cost)
					)
			},
		};

		value.unwrap_or_else(|| Bounded::max_value())
	}
}

/// Charge the gas meter with the specified token.
///
/// Returns `Err(HostError)` if there is not enough gas.
fn charge_gas<T: Trait, Tok: Token<T>>(
	gas_meter: &mut GasMeter<T>,
	metadata: &Tok::Metadata,
	trap_reason: &mut Option<TrapReason>,
	token: Tok,
) -> Result<(), sp_sandbox::HostError> {
	match gas_meter.charge(metadata, token) {
		GasMeterResult::Proceed => Ok(()),
		GasMeterResult::OutOfGas =>  {
			*trap_reason = Some(TrapReason::SupervisorError(Error::<T>::OutOfGas.into()));
			Err(sp_sandbox::HostError)
		},
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
) -> Result<Vec<u8>, sp_sandbox::HostError> {
	charge_gas(
		ctx.gas_meter,
		ctx.schedule,
		&mut ctx.trap_reason,
		RuntimeToken::ReadMemory(len),
	)?;

	let mut buf = vec![0u8; len as usize];
	ctx.memory.get(ptr, buf.as_mut_slice()).map_err(|_| sp_sandbox::HostError)?;
	Ok(buf)
}

/// Read designated chunk from the sandbox memory into the supplied buffer, consuming
/// an appropriate amount of gas.
///
/// Returns `Err` if one of the following conditions occurs:
///
/// - calculating the gas cost resulted in overflow.
/// - out of gas
/// - requested buffer is not within the bounds of the sandbox memory.
fn read_sandbox_memory_into_buf<E: Ext>(
	ctx: &mut Runtime<E>,
	ptr: u32,
	buf: &mut [u8],
) -> Result<(), sp_sandbox::HostError> {
	charge_gas(
		ctx.gas_meter,
		ctx.schedule,
		&mut ctx.trap_reason,
		RuntimeToken::ReadMemory(buf.len() as u32),
	)?;

	ctx.memory.get(ptr, buf).map_err(Into::into)
}

/// Read designated chunk from the sandbox memory, consuming an appropriate amount of
/// gas, and attempt to decode into the specified type.
///
/// Returns `Err` if one of the following conditions occurs:
///
/// - calculating the gas cost resulted in overflow.
/// - out of gas
/// - requested buffer is not within the bounds of the sandbox memory.
/// - the buffer contents cannot be decoded as the required type.
fn read_sandbox_memory_as<E: Ext, D: Decode>(
	ctx: &mut Runtime<E>,
	ptr: u32,
	len: u32,
) -> Result<D, sp_sandbox::HostError> {
	let buf = read_sandbox_memory(ctx, ptr, len)?;
	D::decode(&mut &buf[..]).map_err(|_| sp_sandbox::HostError)
}

/// Write the given buffer to the designated location in the sandbox memory, consuming
/// an appropriate amount of gas.
///
/// Returns `Err` if one of the following conditions occurs:
///
/// - calculating the gas cost resulted in overflow.
/// - out of gas
/// - designated area is not within the bounds of the sandbox memory.
fn write_sandbox_memory<E: Ext>(
	ctx: &mut Runtime<E>,
	ptr: u32,
	buf: &[u8],
) -> Result<(), sp_sandbox::HostError> {
	charge_gas(
		ctx.gas_meter,
		ctx.schedule,
		&mut ctx.trap_reason,
		RuntimeToken::WriteMemory(buf.len() as u32),
	)?;

	ctx.memory.set(ptr, buf)?;

	Ok(())
}

/// Write the given buffer and its length to the designated locations in sandbox memory.
//
/// `out_ptr` is the location in sandbox memory where `buf` should be written to.
/// `out_len_ptr` is an in-out location in sandbox memory. It is read to determine the
/// lenght of the buffer located at `out_ptr`. If that buffer is large enough the actual
/// `buf.len()` is written to this location.
///
/// If `out_ptr` is set to the sentinel value of `u32::max_value()`  and `allow_skip` is true the
/// operation is skipped and `Ok` is returned. This is supposed to help callers to make copying
/// output optional. For example to skip copying back the output buffer of an `ext_call`
/// when the caller is not interested in the result.
///
/// In addition to the error conditions of `write_sandbox_memory` this functions returns
/// `Err` if the size of the buffer located at `out_ptr` is too small to fit `buf`.
fn write_sandbox_output<E: Ext>(
	ctx: &mut Runtime<E>,
	out_ptr: u32,
	out_len_ptr: u32,
	buf: &[u8],
	allow_skip: bool,
) -> Result<(), sp_sandbox::HostError> {
	if allow_skip && out_ptr == u32::max_value() {
		return Ok(());
	}

	let buf_len = buf.len() as u32;
	let len: u32 = read_sandbox_memory_as(ctx, out_len_ptr, 4)?;

	if len < buf_len {
		Err(map_err(ctx, Error::<E::T>::OutputBufferTooSmall))?
	}

	charge_gas(
		ctx.gas_meter,
		ctx.schedule,
		&mut ctx.trap_reason,
		RuntimeToken::WriteMemory(buf_len.saturating_add(4)),
	)?;

	ctx.memory.set(out_ptr, buf)?;
	ctx.memory.set(out_len_ptr, &buf_len.encode())?;

	Ok(())
}

/// Stores a DispatchError returned from an Ext function into the trap_reason.
///
/// This allows through supervisor generated errors to the caller.
fn map_err<E, Error>(ctx: &mut Runtime<E>, err: Error) -> sp_sandbox::HostError where
	E: Ext,
	Error: Into<DispatchError>,
{
	ctx.trap_reason = Some(TrapReason::SupervisorError(err.into()));
	sp_sandbox::HostError
}

// ***********************************************************
// * AFTER MAKING A CHANGE MAKE SURE TO UPDATE COMPLEXITY.MD *
// ***********************************************************

// Define a function `fn init_env<E: Ext>() -> HostFunctionSet<E>` that returns
// a function set which can be imported by an executed contract.
define_env!(Env, <E: Ext>,

	// Account for used gas. Traps if gas used is greater than gas limit.
	//
	// NOTE: This is a implementation defined call and is NOT a part of the public API.
	// This call is supposed to be called only by instrumentation injected code.
	//
	// - amount: How much gas is used.
	gas(ctx, amount: u32) => {
		charge_gas(
			&mut ctx.gas_meter,
			ctx.schedule,
			&mut ctx.trap_reason,
			RuntimeToken::Explicit(amount)
		)?;
		Ok(())
	},

	// Set the value at the given key in the contract storage.
	//
	// The value length must not exceed the maximum defined by the contracts module parameters.
	// Storing an empty value is disallowed.
	//
	// # Parameters
	//
	// - `key_ptr`: pointer into the linear memory where the location to store the value is placed.
	// - `value_ptr`: pointer into the linear memory where the value to set is placed.
	// - `value_len`: the length of the value in bytes.
	//
	// # Errors
	//
	// - If value length exceeds the configured maximum value length of a storage entry.
	// - Upon trying to set an empty storage entry (value length is 0).
	ext_set_storage(ctx, key_ptr: u32, value_ptr: u32, value_len: u32) => {
		if value_len > ctx.ext.max_value_size() {
			// Bail out if value length exceeds the set maximum value size.
			return Err(sp_sandbox::HostError);
		}
		let mut key: StorageKey = [0; 32];
		read_sandbox_memory_into_buf(ctx, key_ptr, &mut key)?;
		let value = Some(read_sandbox_memory(ctx, value_ptr, value_len)?);
		ctx.ext.set_storage(key, value);
		Ok(())
	},

	// Clear the value at the given key in the contract storage.
	//
	// # Parameters
	//
	// - `key_ptr`: pointer into the linear memory where the location to clear the value is placed.
	ext_clear_storage(ctx, key_ptr: u32) => {
		let mut key: StorageKey = [0; 32];
		read_sandbox_memory_into_buf(ctx, key_ptr, &mut key)?;
		ctx.ext.set_storage(key, None);
		Ok(())
	},

	// Retrieve the value under the given key from storage.
	//
	// # Parameters
	//
	// - `key_ptr`: pointer into the linear memory where the key of the requested value is placed.
	// - `out_ptr`: pointer to the linear memory where the value is written to.
	// - `out_len_ptr`: in-out pointer into linear memory where the buffer length
	//   is read from and the value length is written to.
	//
	// # Errors
	//
	// If there is no entry under the given key then this function will return
	// `ReturnCode::KeyNotFound`.
	//
	// # Traps
	//
	// Traps if the supplied buffer length is smaller than the size of the stored value.
	ext_get_storage(ctx, key_ptr: u32, out_ptr: u32, out_len_ptr: u32) -> ReturnCode => {
		let mut key: StorageKey = [0; 32];
		read_sandbox_memory_into_buf(ctx, key_ptr, &mut key)?;
		if let Some(value) = ctx.ext.get_storage(&key) {
			write_sandbox_output(ctx, out_ptr, out_len_ptr, &value, false)?;
			Ok(ReturnCode::Success)
		} else {
			Ok(ReturnCode::KeyNotFound)
		}
	},

	// Transfer some value to another account.
	//
	// # Parameters
	//
	// - account_ptr: a pointer to the address of the beneficiary account
	//   Should be decodable as an `T::AccountId`. Traps otherwise.
	// - account_len: length of the address buffer.
	// - value_ptr: a pointer to the buffer with value, how much value to send.
	//   Should be decodable as a `T::Balance`. Traps otherwise.
	// - value_len: length of the value buffer.
	//
	// # Traps
	//
	// Traps if the transfer wasn't succesful. This can happen when the value transfered
	// brings the sender below the existential deposit. Use `ext_terminate` to remove
	// the caller contract.
	ext_transfer(
		ctx,
		account_ptr: u32,
		account_len: u32,
		value_ptr: u32,
		value_len: u32
	) => {
		let callee: <<E as Ext>::T as frame_system::Trait>::AccountId =
			read_sandbox_memory_as(ctx, account_ptr, account_len)?;
		let value: BalanceOf<<E as Ext>::T> =
			read_sandbox_memory_as(ctx, value_ptr, value_len)?;

		ctx.ext.transfer(&callee, value, ctx.gas_meter).map_err(|e| map_err(ctx, e))
	},

	// Make a call to another contract.
	//
	// The callees output buffer is copied to `output_ptr` and its length to `output_len_ptr`.
	// The copy of the output buffer can be skipped by supplying the sentinel value
	// of `u32::max_value()` to `output_ptr`.
	//
	// # Parameters
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
	// - output_ptr: a pointer where the output buffer is copied to.
	// - output_len_ptr: in-out pointer to where the length of the buffer is read from
	//   and the actual length is written to.
	//
	// # Errors
	//
	// `ReturnCode::CalleeReverted`: The callee ran to completion but decided to have its
	//  changes reverted. The delivery of the output buffer is still possible.
	// `ReturnCode::CalleeTrapped`: The callee trapped during execution. All changes are reverted
	//  and no output buffer is delivered.
	//
	// # Traps
	//
	// - Transfer of balance failed. This call can not bring the sender below the existential
	//   deposit. Use `ext_terminate` to remove the caller.
	// - Callee does not exist.
	// - Supplied output buffer is too small.
	ext_call(
		ctx,
		callee_ptr: u32,
		callee_len: u32,
		gas: u64,
		value_ptr: u32,
		value_len: u32,
		input_data_ptr: u32,
		input_data_len: u32,
		output_ptr: u32,
		output_len_ptr: u32
	) -> ReturnCode => {
		let callee: <<E as Ext>::T as frame_system::Trait>::AccountId =
			read_sandbox_memory_as(ctx, callee_ptr, callee_len)?;
		let value: BalanceOf<<E as Ext>::T> = read_sandbox_memory_as(ctx, value_ptr, value_len)?;
		let input_data = read_sandbox_memory(ctx, input_data_ptr, input_data_len)?;

		let nested_gas_limit = if gas == 0 {
			ctx.gas_meter.gas_left()
		} else {
			gas.saturated_into()
		};
		let ext = &mut ctx.ext;
		let call_outcome = ctx.gas_meter.with_nested(nested_gas_limit, |nested_meter| {
			match nested_meter {
				Some(nested_meter) => {
					ext.call(
						&callee,
						value,
						nested_meter,
						input_data,
					)
					.map_err(|_| ())
				}
				// there is not enough gas to allocate for the nested call.
				None => Err(()),
			}
		});

		match call_outcome {
			Ok(output) => {
				write_sandbox_output(ctx, output_ptr, output_len_ptr, &output.data, true)?;
				Ok(output.into())
			},
			Err(_) => {
				Ok(ReturnCode::CalleeTrapped)
			},
		}
	},

	// Instantiate a contract with the specified code hash.
	//
	// This function creates an account and executes the constructor defined in the code specified
	// by the code hash. The address of this new account is copied to `address_ptr` and its length
	// to `address_len_ptr`. The constructors output buffer is copied to `output_ptr` and its
	// length to `output_len_ptr`.
	//
	// The copy of the output buffer and address can be skipped by supplying the sentinel value
	// of `u32::max_value()` to `output_ptr` or `address_ptr`.
	//
	// # Parameters
	//
	// - code_hash_ptr: a pointer to the buffer that contains the initializer code.
	// - code_hash_len: length of the initializer code buffer.
	// - gas: how much gas to devote to the execution of the initializer code.
	// - value_ptr: a pointer to the buffer with value, how much value to send.
	//   Should be decodable as a `T::Balance`. Traps otherwise.
	// - value_len: length of the value buffer.
	// - input_data_ptr: a pointer to a buffer to be used as input data to the initializer code.
	// - input_data_len: length of the input data buffer.
	// - address_ptr: a pointer where the new account's address is copied to.
	// - address_len_ptr: in-out pointer to where the length of the buffer is read from
	//		and the actual length is written to.
	// - output_ptr: a pointer where the output buffer is copied to.
	// - output_len_ptr: in-out pointer to where the length of the buffer is read from
	//   and the actual length is written to.
	//
	// # Errors
	//
	// `ReturnCode::CalleeReverted`: The callee's constructor ran to completion but decided to have
	//		its changes reverted. The delivery of the output buffer is still possible but the
	//		account was not created and no address is returned.
	// `ReturnCode::CalleeTrapped`: The callee trapped during execution. All changes are reverted
	//		and no output buffer is delivered. The accounts was not created and no address is
	//		returned.
	//
	// # Traps
	//
	// - Transfer of balance failed. This call can not bring the sender below the existential
	//   deposit. Use `ext_terminate` to remove the caller.
	// - Code hash does not exist.
	// - Supplied output buffers are too small.
	ext_instantiate(
		ctx,
		code_hash_ptr: u32,
		code_hash_len: u32,
		gas: u64,
		value_ptr: u32,
		value_len: u32,
		input_data_ptr: u32,
		input_data_len: u32,
		address_ptr: u32,
		address_len_ptr: u32,
		output_ptr: u32,
		output_len_ptr: u32
	) -> ReturnCode => {
		let code_hash: CodeHash<<E as Ext>::T> =
			read_sandbox_memory_as(ctx, code_hash_ptr, code_hash_len)?;
		let value: BalanceOf<<E as Ext>::T> = read_sandbox_memory_as(ctx, value_ptr, value_len)?;
		let input_data = read_sandbox_memory(ctx, input_data_ptr, input_data_len)?;

		let nested_gas_limit = if gas == 0 {
			ctx.gas_meter.gas_left()
		} else {
			gas.saturated_into()
		};
		let ext = &mut ctx.ext;
		let instantiate_outcome = ctx.gas_meter.with_nested(nested_gas_limit, |nested_meter| {
			match nested_meter {
				Some(nested_meter) => {
					ext.instantiate(
						&code_hash,
						value,
						nested_meter,
						input_data
					)
					.map_err(|_| ())
				}
				// there is not enough gas to allocate for the nested call.
				None => Err(()),
			}
		});
		match instantiate_outcome {
			Ok((address, output)) => {
				if !output.flags.contains(ReturnFlags::REVERT) {
					write_sandbox_output(
						ctx, address_ptr, address_len_ptr, &address.encode(), true
					)?;
				}
				write_sandbox_output(ctx, output_ptr, output_len_ptr, &output.data, true)?;
				Ok(output.into())
			},
			Err(_) => {
				Ok(ReturnCode::CalleeTrapped)
			},
		}
	},

	// Remove the calling account and transfer remaining balance.
	//
	// This function never returns. Either the termination was successful and the
	// execution of the destroyed contract is halted. Or it failed during the termination
	// which is considered fatal and results in a trap + rollback.
	//
	// - beneficiary_ptr: a pointer to the address of the beneficiary account where all
	//   where all remaining funds of the caller are transfered.
	//   Should be decodable as an `T::AccountId`. Traps otherwise.
	// - beneficiary_len: length of the address buffer.
	ext_terminate(
		ctx,
		beneficiary_ptr: u32,
		beneficiary_len: u32
	) => {
		let beneficiary: <<E as Ext>::T as frame_system::Trait>::AccountId =
			read_sandbox_memory_as(ctx, beneficiary_ptr, beneficiary_len)?;

		if let Ok(_) = ctx.ext.terminate(&beneficiary, ctx.gas_meter) {
			ctx.trap_reason = Some(TrapReason::Termination);
		}
		Err(sp_sandbox::HostError)
	},

	ext_input(ctx, buf_ptr: u32, buf_len_ptr: u32) => {
		if let Some(input) = ctx.input_data.take() {
			write_sandbox_output(ctx, buf_ptr, buf_len_ptr, &input, false)
		} else {
			Err(sp_sandbox::HostError)
		}
	},

	// Cease contract execution and save a data buffer as a result of the execution.
	//
	// This function never retuns as it stops execution of the caller.
	// This is the only way to return a data buffer to the caller. Returning from
	// execution without calling this function is equivalent to calling:
	// ```
	// ext_return(0, 0, 0);
	// ```
	//
	// The flags argument is a bitfield that can be used to signal special return
	// conditions to the supervisor:
	// --- lsb ---
	// bit 0      : REVERT - Revert all storage changes made by the caller.
	// bit [1, 31]: Reserved for future use.
	// --- msb ---
	//
	// Using a reserved bit triggers a trap.
	ext_return(ctx, flags: u32, data_ptr: u32, data_len: u32) => {
		charge_gas(
			ctx.gas_meter,
			ctx.schedule,
			&mut ctx.trap_reason,
			RuntimeToken::ReturnData(data_len)
		)?;

		ctx.trap_reason = Some(TrapReason::Return(ReturnData {
			flags,
			data: read_sandbox_memory(ctx, data_ptr, data_len)?,
		}));

		// The trap mechanism is used to immediately terminate the execution.
		// This trap should be handled appropriately before returning the result
		// to the user of this crate.
		Err(sp_sandbox::HostError)
	},

	// Stores the address of the caller into the supplied buffer.
	//
	// The value is stored to linear memory at the address pointed to by `out_ptr`.
	// `out_len_ptr` must point to a u32 value that describes the available space at
	// `out_ptr`. This call overwrites it with the size of the value. If the available
	// space at `out_ptr` is less than the size of the value a trap is triggered.
	//
	// If this is a top-level call (i.e. initiated by an extrinsic) the origin address of the
	// extrinsic will be returned. Otherwise, if this call is initiated by another contract then the
	// address of the contract will be returned. The value is encoded as T::AccountId.
	ext_caller(ctx, out_ptr: u32, out_len_ptr: u32) => {
		write_sandbox_output(ctx, out_ptr, out_len_ptr, &ctx.ext.caller().encode(), false)
	},

	// Stores the address of the current contract into the supplied buffer.
	//
	// The value is stored to linear memory at the address pointed to by `out_ptr`.
	// `out_len_ptr` must point to a u32 value that describes the available space at
	// `out_ptr`. This call overwrites it with the size of the value. If the available
	// space at `out_ptr` is less than the size of the value a trap is triggered.
	ext_address(ctx, out_ptr: u32, out_len_ptr: u32) => {
		write_sandbox_output(ctx, out_ptr, out_len_ptr, &ctx.ext.address().encode(), false)
	},

	// Stores the price for the specified amount of gas into the supplied buffer.
	//
	// The value is stored to linear memory at the address pointed to by `out_ptr`.
	// `out_len_ptr` must point to a u32 value that describes the available space at
	// `out_ptr`. This call overwrites it with the size of the value. If the available
	// space at `out_ptr` is less than the size of the value a trap is triggered.
	//
	// The data is encoded as T::Balance.
	//
	// # Note
	//
	// It is recommended to avoid specifying very small values for `gas` as the prices for a single
	// gas can be smaller than one.
	ext_weight_to_fee(ctx, gas: u64, out_ptr: u32, out_len_ptr: u32) => {
		write_sandbox_output(
			ctx, out_ptr, out_len_ptr, &ctx.ext.get_weight_price(gas).encode(), false
		)
	},

	// Stores the amount of gas left into the supplied buffer.
	//
	// The value is stored to linear memory at the address pointed to by `out_ptr`.
	// `out_len_ptr` must point to a u32 value that describes the available space at
	// `out_ptr`. This call overwrites it with the size of the value. If the available
	// space at `out_ptr` is less than the size of the value a trap is triggered.
	//
	// The data is encoded as Gas.
	ext_gas_left(ctx, out_ptr: u32, out_len_ptr: u32) => {
		write_sandbox_output(ctx, out_ptr, out_len_ptr, &ctx.gas_meter.gas_left().encode(), false)
	},

	// Stores the balance of the current account into the supplied buffer.
	//
	// The value is stored to linear memory at the address pointed to by `out_ptr`.
	// `out_len_ptr` must point to a u32 value that describes the available space at
	// `out_ptr`. This call overwrites it with the size of the value. If the available
	// space at `out_ptr` is less than the size of the value a trap is triggered.
	//
	// The data is encoded as T::Balance.
	ext_balance(ctx, out_ptr: u32, out_len_ptr: u32) => {
		write_sandbox_output(ctx, out_ptr, out_len_ptr, &ctx.ext.balance().encode(), false)
	},

	// Stores the value transferred along with this call or as endowment into the supplied buffer.
	//
	// The value is stored to linear memory at the address pointed to by `out_ptr`.
	// `out_len_ptr` must point to a u32 value that describes the available space at
	// `out_ptr`. This call overwrites it with the size of the value. If the available
	// space at `out_ptr` is less than the size of the value a trap is triggered.
	//
	// The data is encoded as T::Balance.
	ext_value_transferred(ctx, out_ptr: u32, out_len_ptr: u32) => {
		write_sandbox_output(
			ctx, out_ptr, out_len_ptr, &ctx.ext.value_transferred().encode(), false
		)
	},

	// Stores a random number for the current block and the given subject into the supplied buffer.
	//
	// The value is stored to linear memory at the address pointed to by `out_ptr`.
	// `out_len_ptr` must point to a u32 value that describes the available space at
	// `out_ptr`. This call overwrites it with the size of the value. If the available
	// space at `out_ptr` is less than the size of the value a trap is triggered.
	//
	// The data is encoded as T::Hash.
	ext_random(ctx, subject_ptr: u32, subject_len: u32, out_ptr: u32, out_len_ptr: u32) => {
		// The length of a subject can't exceed `max_subject_len`.
		if subject_len > ctx.schedule.max_subject_len {
			return Err(sp_sandbox::HostError);
		}
		let subject_buf = read_sandbox_memory(ctx, subject_ptr, subject_len)?;
		write_sandbox_output(
			ctx, out_ptr, out_len_ptr, &ctx.ext.random(&subject_buf).encode(), false
		)
	},

	// Load the latest block timestamp into the supplied buffer
	//
	// The value is stored to linear memory at the address pointed to by `out_ptr`.
	// `out_len_ptr` must point to a u32 value that describes the available space at
	// `out_ptr`. This call overwrites it with the size of the value. If the available
	// space at `out_ptr` is less than the size of the value a trap is triggered.
	ext_now(ctx, out_ptr: u32, out_len_ptr: u32) => {
		write_sandbox_output(ctx, out_ptr, out_len_ptr, &ctx.ext.now().encode(), false)
	},

	// Stores the minimum balance (a.k.a. existential deposit) into the supplied buffer.
	//
	// The data is encoded as T::Balance.
	ext_minimum_balance(ctx, out_ptr: u32, out_len_ptr: u32) => {
		write_sandbox_output(ctx, out_ptr, out_len_ptr, &ctx.ext.minimum_balance().encode(), false)
	},

	// Stores the tombstone deposit into the supplied buffer.
	//
	// The value is stored to linear memory at the address pointed to by `out_ptr`.
	// `out_len_ptr` must point to a u32 value that describes the available space at
	// `out_ptr`. This call overwrites it with the size of the value. If the available
	// space at `out_ptr` is less than the size of the value a trap is triggered.
	//
	// The data is encoded as T::Balance.
	//
	// # Note
	//
	// The tombstone deposit is on top of the existential deposit. So in order for
	// a contract to leave a tombstone the balance of the contract must not go
	// below the sum of existential deposit and the tombstone deposit. The sum
	// is commonly referred as subsistence threshold in code.
	ext_tombstone_deposit(ctx, out_ptr: u32, out_len_ptr: u32) => {
		write_sandbox_output(
			ctx, out_ptr, out_len_ptr, &ctx.ext.tombstone_deposit().encode(), false
		)
	},

	// Try to restore the given destination contract sacrificing the caller.
	//
	// This function will compute a tombstone hash from the caller's storage and the given code hash
	// and if the hash matches the hash found in the tombstone at the specified address - kill
	// the caller contract and restore the destination contract and set the specified `rent_allowance`.
	// All caller's funds are transfered to the destination.
	//
	// If there is no tombstone at the destination address, the hashes don't match or this contract
	// instance is already present on the contract call stack, a trap is generated.
	//
	// Otherwise, the destination contract is restored. This function is diverging and stops execution
	// even on success.
	//
	// `dest_ptr`, `dest_len` - the pointer and the length of a buffer that encodes `T::AccountId`
	// with the address of the to be restored contract.
	// `code_hash_ptr`, `code_hash_len` - the pointer and the length of a buffer that encodes
	// a code hash of the to be restored contract.
	// `rent_allowance_ptr`, `rent_allowance_len` - the pointer and the length of a buffer that
	// encodes the rent allowance that must be set in the case of successful restoration.
	// `delta_ptr` is the pointer to the start of a buffer that has `delta_count` storage keys
	// laid out sequentially.
	ext_restore_to(
		ctx,
		dest_ptr: u32,
		dest_len: u32,
		code_hash_ptr: u32,
		code_hash_len: u32,
		rent_allowance_ptr: u32,
		rent_allowance_len: u32,
		delta_ptr: u32,
		delta_count: u32
	) => {
		let dest: <<E as Ext>::T as frame_system::Trait>::AccountId =
			read_sandbox_memory_as(ctx, dest_ptr, dest_len)?;
		let code_hash: CodeHash<<E as Ext>::T> =
			read_sandbox_memory_as(ctx, code_hash_ptr, code_hash_len)?;
		let rent_allowance: BalanceOf<<E as Ext>::T> =
			read_sandbox_memory_as(ctx, rent_allowance_ptr, rent_allowance_len)?;
		let delta = {
			// We don't use `with_capacity` here to not eagerly allocate the user specified amount
			// of memory.
			let mut delta = Vec::new();
			let mut key_ptr = delta_ptr;

			for _ in 0..delta_count {
				const KEY_SIZE: usize = 32;

				// Read the delta into the provided buffer and collect it into the buffer.
				let mut delta_key: StorageKey = [0; KEY_SIZE];
				read_sandbox_memory_into_buf(ctx, key_ptr, &mut delta_key)?;
				delta.push(delta_key);

				// Offset key_ptr to the next element.
				key_ptr = key_ptr.checked_add(KEY_SIZE as u32).ok_or_else(|| sp_sandbox::HostError)?;
			}

			delta
		};

		if let Ok(()) = ctx.ext.restore_to(
			dest,
			code_hash,
			rent_allowance,
			delta,
		) {
			ctx.trap_reason = Some(TrapReason::Restoration);
		}
		Err(sp_sandbox::HostError)
	},

	// Deposit a contract event with the data buffer and optional list of topics. There is a limit
	// on the maximum number of topics specified by `max_event_topics`.
	//
	// - topics_ptr - a pointer to the buffer of topics encoded as `Vec<T::Hash>`. The value of this
	//   is ignored if `topics_len` is set to 0. The topics list can't contain duplicates.
	// - topics_len - the length of the topics buffer. Pass 0 if you want to pass an empty vector.
	// - data_ptr - a pointer to a raw data buffer which will saved along the event.
	// - data_len - the length of the data buffer.
	ext_deposit_event(ctx, topics_ptr: u32, topics_len: u32, data_ptr: u32, data_len: u32) => {
		let mut topics: Vec::<TopicOf<<E as Ext>::T>> = match topics_len {
			0 => Vec::new(),
			_ => read_sandbox_memory_as(ctx, topics_ptr, topics_len)?,
		};

		// If there are more than `max_event_topics`, then trap.
		if topics.len() > ctx.schedule.max_event_topics as usize {
			return Err(sp_sandbox::HostError);
		}

		// Check for duplicate topics. If there are any, then trap.
		if has_duplicates(&mut topics) {
			return Err(sp_sandbox::HostError);
		}

		let event_data = read_sandbox_memory(ctx, data_ptr, data_len)?;

		charge_gas(
			ctx.gas_meter,
			ctx.schedule,
			&mut ctx.trap_reason,
			RuntimeToken::DepositEvent(topics.len() as u32, data_len)
		)?;
		ctx.ext.deposit_event(topics, event_data);

		Ok(())
	},

	// Set rent allowance of the contract
	//
	// - value_ptr: a pointer to the buffer with value, how much to allow for rent
	//   Should be decodable as a `T::Balance`. Traps otherwise.
	// - value_len: length of the value buffer.
	ext_set_rent_allowance(ctx, value_ptr: u32, value_len: u32) => {
		let value: BalanceOf<<E as Ext>::T> =
			read_sandbox_memory_as(ctx, value_ptr, value_len)?;
		ctx.ext.set_rent_allowance(value);

		Ok(())
	},

	// Stores the rent allowance into the supplied buffer.
	//
	// The value is stored to linear memory at the address pointed to by `out_ptr`.
	// `out_len_ptr` must point to a u32 value that describes the available space at
	// `out_ptr`. This call overwrites it with the size of the value. If the available
	// space at `out_ptr` is less than the size of the value a trap is triggered.
	//
	// The data is encoded as T::Balance.
	ext_rent_allowance(ctx, out_ptr: u32, out_len_ptr: u32) => {
		write_sandbox_output(ctx, out_ptr, out_len_ptr, &ctx.ext.rent_allowance().encode(), false)
	},

	// Prints utf8 encoded string from the data buffer.
	// Only available on `--dev` chains.
	// This function may be removed at any time, superseded by a more general contract debugging feature.
	ext_println(ctx, str_ptr: u32, str_len: u32) => {
		let data = read_sandbox_memory(ctx, str_ptr, str_len)?;
		if let Ok(utf8) = core::str::from_utf8(&data) {
			sp_runtime::print(utf8);
		}
		Ok(())
	},

	// Stores the current block number of the current contract into the supplied buffer.
	//
	// The value is stored to linear memory at the address pointed to by `out_ptr`.
	// `out_len_ptr` must point to a u32 value that describes the available space at
	// `out_ptr`. This call overwrites it with the size of the value. If the available
	// space at `out_ptr` is less than the size of the value a trap is triggered.
	ext_block_number(ctx, out_ptr: u32, out_len_ptr: u32) => {
		write_sandbox_output(ctx, out_ptr, out_len_ptr, &ctx.ext.block_number().encode(), false)
	},

	// Computes the SHA2 256-bit hash on the given input buffer.
	//
	// Returns the result directly into the given output buffer.
	//
	// # Note
	//
	// - The `input` and `output` buffer may overlap.
	// - The output buffer is expected to hold at least 32 bytes (256 bits).
	// - It is the callers responsibility to provide an output buffer that
	//   is large enough to hold the expected amount of bytes returned by the
	//   chosen hash function.
	//
	// # Parameters
	//
	// - `input_ptr`: the pointer into the linear memory where the input
	//                data is placed.
	// - `input_len`: the length of the input data in bytes.
	// - `output_ptr`: the pointer into the linear memory where the output
	//                 data is placed. The function will write the result
	//                 directly into this buffer.
	ext_hash_sha2_256(ctx, input_ptr: u32, input_len: u32, output_ptr: u32) => {
		compute_hash_on_intermediate_buffer(ctx, sha2_256, input_ptr, input_len, output_ptr)
	},

	// Computes the KECCAK 256-bit hash on the given input buffer.
	//
	// Returns the result directly into the given output buffer.
	//
	// # Note
	//
	// - The `input` and `output` buffer may overlap.
	// - The output buffer is expected to hold at least 32 bytes (256 bits).
	// - It is the callers responsibility to provide an output buffer that
	//   is large enough to hold the expected amount of bytes returned by the
	//   chosen hash function.
	//
	// # Parameters
	//
	// - `input_ptr`: the pointer into the linear memory where the input
	//                data is placed.
	// - `input_len`: the length of the input data in bytes.
	// - `output_ptr`: the pointer into the linear memory where the output
	//                 data is placed. The function will write the result
	//                 directly into this buffer.
	ext_hash_keccak_256(ctx, input_ptr: u32, input_len: u32, output_ptr: u32) => {
		compute_hash_on_intermediate_buffer(ctx, keccak_256, input_ptr, input_len, output_ptr)
	},

	// Computes the BLAKE2 256-bit hash on the given input buffer.
	//
	// Returns the result directly into the given output buffer.
	//
	// # Note
	//
	// - The `input` and `output` buffer may overlap.
	// - The output buffer is expected to hold at least 32 bytes (256 bits).
	// - It is the callers responsibility to provide an output buffer that
	//   is large enough to hold the expected amount of bytes returned by the
	//   chosen hash function.
	//
	// # Parameters
	//
	// - `input_ptr`: the pointer into the linear memory where the input
	//                data is placed.
	// - `input_len`: the length of the input data in bytes.
	// - `output_ptr`: the pointer into the linear memory where the output
	//                 data is placed. The function will write the result
	//                 directly into this buffer.
	ext_hash_blake2_256(ctx, input_ptr: u32, input_len: u32, output_ptr: u32) => {
		compute_hash_on_intermediate_buffer(ctx, blake2_256, input_ptr, input_len, output_ptr)
	},

	// Computes the BLAKE2 128-bit hash on the given input buffer.
	//
	// Returns the result directly into the given output buffer.
	//
	// # Note
	//
	// - The `input` and `output` buffer may overlap.
	// - The output buffer is expected to hold at least 16 bytes (128 bits).
	// - It is the callers responsibility to provide an output buffer that
	//   is large enough to hold the expected amount of bytes returned by the
	//   chosen hash function.
	//
	// # Parameters
	//
	// - `input_ptr`: the pointer into the linear memory where the input
	//                data is placed.
	// - `input_len`: the length of the input data in bytes.
	// - `output_ptr`: the pointer into the linear memory where the output
	//                 data is placed. The function will write the result
	//                 directly into this buffer.
	ext_hash_blake2_128(ctx, input_ptr: u32, input_len: u32, output_ptr: u32) => {
		compute_hash_on_intermediate_buffer(ctx, blake2_128, input_ptr, input_len, output_ptr)
	},
);

/// Computes the given hash function on the supplied input.
///
/// Reads from the sandboxed input buffer into an intermediate buffer.
/// Returns the result directly to the output buffer of the sandboxed memory.
///
/// It is the callers responsibility to provide an output buffer that
/// is large enough to hold the expected amount of bytes returned by the
/// chosen hash function.
///
/// # Note
///
/// The `input` and `output` buffers may overlap.
fn compute_hash_on_intermediate_buffer<E, F, R>(
	ctx: &mut Runtime<E>,
	hash_fn: F,
	input_ptr: u32,
	input_len: u32,
	output_ptr: u32,
) -> Result<(), sp_sandbox::HostError>
where
	E: Ext,
	F: FnOnce(&[u8]) -> R,
	R: AsRef<[u8]>,
{
	// Copy input into supervisor memory.
	let input = read_sandbox_memory(ctx, input_ptr, input_len)?;
	// Compute the hash on the input buffer using the given hash function.
	let hash = hash_fn(&input);
	// Write the resulting hash back into the sandboxed output buffer.
	write_sandbox_memory(
		ctx,
		output_ptr,
		hash.as_ref(),
	)?;
	Ok(())
}

/// Finds duplicates in a given vector.
///
/// This function has complexity of O(n log n) and no additional memory is required, although
/// the order of items is not preserved.
fn has_duplicates<T: PartialEq + AsRef<[u8]>>(items: &mut Vec<T>) -> bool {
	// Sort the vector
	items.sort_unstable_by(|a, b| {
		Ord::cmp(a.as_ref(), b.as_ref())
	});
	// And then find any two consecutive equal elements.
	items.windows(2).any(|w| {
		match w {
			&[ref a, ref b] => a == b,
			_ => false,
		}
	})
}
