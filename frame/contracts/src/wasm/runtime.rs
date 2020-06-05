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

use crate::{Schedule, Trait, CodeHash, BalanceOf};
use crate::exec::{
	Ext, ExecResult, ExecError, ExecReturnValue, StorageKey, TopicOf, STATUS_SUCCESS,
};
use crate::gas::{Gas, GasMeter, Token, GasMeterResult};
use sp_sandbox;
use frame_system;
use sp_std::{prelude::*, mem, convert::TryInto};
use codec::{Decode, Encode};
use sp_runtime::traits::{Bounded, SaturatedConversion};
use sp_io::hashing::{
	keccak_256,
	blake2_256,
	blake2_128,
	sha2_256,
};
use frame_support::weights::GetDispatchInfo;

/// The value returned from ext_call and ext_instantiate contract external functions if the call or
/// instantiation traps. This value is chosen as if the execution does not trap, the return value
/// will always be an 8-bit integer, so 0x0100 is the smallest value that could not be returned.
const TRAP_RETURN_CODE: u32 = 0x0100;

/// Enumerates all possible *special* trap conditions.
///
/// In this runtime traps used not only for signaling about errors but also
/// to just terminate quickly in some cases.
enum SpecialTrap {
	/// Signals that trap was generated in response to call `ext_return` host function.
	Return(Vec<u8>),
	/// Signals that trap was generated because the contract exhausted its gas limit.
	OutOfGas,
	/// Signals that a trap was generated in response to a succesful call to the
	/// `ext_terminate` host function.
	Termination,
}

/// Can only be used for one call.
pub(crate) struct Runtime<'a, E: Ext + 'a> {
	ext: &'a mut E,
	scratch_buf: Vec<u8>,
	schedule: &'a Schedule,
	memory: sp_sandbox::Memory,
	gas_meter: &'a mut GasMeter<E::T>,
	special_trap: Option<SpecialTrap>,
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
			// Put the input data into the scratch buffer immediately.
			scratch_buf: input_data,
			schedule,
			memory,
			gas_meter,
			special_trap: None,
		}
	}
}

pub(crate) fn to_execution_result<E: Ext>(
	runtime: Runtime<E>,
	sandbox_result: Result<sp_sandbox::ReturnValue, sp_sandbox::Error>,
) -> ExecResult {
	match runtime.special_trap {
		// The trap was the result of the execution `return` host function.
		Some(SpecialTrap::Return(data)) => {
			return Ok(ExecReturnValue {
				status: STATUS_SUCCESS,
				data,
			})
		},
		Some(SpecialTrap::Termination) => {
			return Ok(ExecReturnValue {
				status: STATUS_SUCCESS,
				data: Vec::new(),
			})
		},
		Some(SpecialTrap::OutOfGas) => {
			return Err(ExecError {
				reason: "ran out of gas during contract execution".into(),
				buffer: runtime.scratch_buf,
			})
		},
		None => (),
	}

	// Check the exact type of the error.
	match sandbox_result {
		// No traps were generated. Proceed normally.
		Ok(sp_sandbox::ReturnValue::Unit) => {
			let mut buffer = runtime.scratch_buf;
			buffer.clear();
			Ok(ExecReturnValue { status: STATUS_SUCCESS, data: buffer })
		}
		Ok(sp_sandbox::ReturnValue::Value(sp_sandbox::Value::I32(exit_code))) => {
			let status = (exit_code & 0xFF).try_into()
				.expect("exit_code is masked into the range of a u8; qed");
			Ok(ExecReturnValue { status, data: runtime.scratch_buf })
		}
		// This should never happen as the return type of exported functions should have been
		// validated by the code preparation process. However, because panics are really
		// undesirable in the runtime code, we treat this as a trap for now. Eventually, we might
		// want to revisit this.
		Ok(_) => Err(ExecError { reason: "return type error".into(), buffer: runtime.scratch_buf }),
		// `Error::Module` is returned only if instantiation or linking failed (i.e.
		// wasm binary tried to import a function that is not provided by the host).
		// This shouldn't happen because validation process ought to reject such binaries.
		//
		// Because panics are really undesirable in the runtime code, we treat this as
		// a trap for now. Eventually, we might want to revisit this.
		Err(sp_sandbox::Error::Module) =>
			Err(ExecError { reason: "validation error".into(), buffer: runtime.scratch_buf }),
		// Any other kind of a trap should result in a failure.
		Err(sp_sandbox::Error::Execution) | Err(sp_sandbox::Error::OutOfBounds) =>
			Err(ExecError { reason: "contract trapped during execution".into(), buffer: runtime.scratch_buf }),
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
	/// Dispatched a call with the given weight.
	DispatchWithWeight(Gas),
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
			DispatchWithWeight(gas) => gas.checked_add(metadata.dispatch_base_cost),
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
	special_trap: &mut Option<SpecialTrap>,
	token: Tok,
) -> Result<(), sp_sandbox::HostError> {
	match gas_meter.charge(metadata, token) {
		GasMeterResult::Proceed => Ok(()),
		GasMeterResult::OutOfGas =>  {
			*special_trap = Some(SpecialTrap::OutOfGas);
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
		&mut ctx.special_trap,
		RuntimeToken::ReadMemory(len),
	)?;

	let mut buf = vec![0u8; len as usize];
	ctx.memory.get(ptr, buf.as_mut_slice()).map_err(|_| sp_sandbox::HostError)?;
	Ok(buf)
}

/// Read designated chunk from the sandbox memory into the scratch buffer, consuming an
/// appropriate amount of gas. Resizes the scratch buffer to the specified length on success.
///
/// Returns `Err` if one of the following conditions occurs:
///
/// - calculating the gas cost resulted in overflow.
/// - out of gas
/// - requested buffer is not within the bounds of the sandbox memory.
fn read_sandbox_memory_into_scratch<E: Ext>(
	ctx: &mut Runtime<E>,
	ptr: u32,
	len: u32,
) -> Result<(), sp_sandbox::HostError> {
	charge_gas(
		ctx.gas_meter,
		ctx.schedule,
		&mut ctx.special_trap,
		RuntimeToken::ReadMemory(len),
	)?;

	ctx.scratch_buf.resize(len as usize, 0);
	ctx.memory.get(ptr, ctx.scratch_buf.as_mut_slice()).map_err(|_| sp_sandbox::HostError)?;
	Ok(())
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
		&mut ctx.special_trap,
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
fn write_sandbox_memory<T: Trait>(
	schedule: &Schedule,
	special_trap: &mut Option<SpecialTrap>,
	gas_meter: &mut GasMeter<T>,
	memory: &sp_sandbox::Memory,
	ptr: u32,
	buf: &[u8],
) -> Result<(), sp_sandbox::HostError> {
	charge_gas(
		gas_meter,
		schedule,
		special_trap,
		RuntimeToken::WriteMemory(buf.len() as u32),
	)?;

	memory.set(ptr, buf)?;

	Ok(())
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
			&mut ctx.special_trap,
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
		ctx.ext.set_storage(key, value).map_err(|_| sp_sandbox::HostError)?;
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
		ctx.ext.set_storage(key, None).map_err(|_| sp_sandbox::HostError)?;
		Ok(())
	},

	// Retrieve the value under the given key from the storage and return 0.
	// If there is no entry under the given key then this function will return 1 and
	// clear the scratch buffer.
	//
	// - key_ptr: pointer into the linear memory where the key
	//   of the requested value is placed.
	ext_get_storage(ctx, key_ptr: u32) -> u32 => {
		let mut key: StorageKey = [0; 32];
		read_sandbox_memory_into_buf(ctx, key_ptr, &mut key)?;
		if let Some(value) = ctx.ext.get_storage(&key) {
			ctx.scratch_buf = value;
			Ok(0)
		} else {
			ctx.scratch_buf.clear();
			Ok(1)
		}
	},

	// Transfer some value to another account.
	//
	// If the value transfer was succesful zero is returned. Otherwise one is returned.
	// The scratch buffer is not touched. The receiver can be a plain account or
	// a contract.
	//
	// - account_ptr: a pointer to the address of the beneficiary account
	//   Should be decodable as an `T::AccountId`. Traps otherwise.
	// - account_len: length of the address buffer.
	// - value_ptr: a pointer to the buffer with value, how much value to send.
	//   Should be decodable as a `T::Balance`. Traps otherwise.
	// - value_len: length of the value buffer.
	ext_transfer(
		ctx,
		account_ptr: u32,
		account_len: u32,
		value_ptr: u32,
		value_len: u32
	) -> u32 => {
		let callee: <<E as Ext>::T as frame_system::Trait>::AccountId =
			read_sandbox_memory_as(ctx, account_ptr, account_len)?;
		let value: BalanceOf<<E as Ext>::T> =
			read_sandbox_memory_as(ctx, value_ptr, value_len)?;

		match ctx.ext.transfer(&callee, value, ctx.gas_meter) {
			Ok(_) => Ok(0),
			Err(_) => Ok(1),
		}
	},

	// Make a call to another contract.
	//
	// If the called contract runs to completion, then this returns the status code the callee
	// returns on exit in the bottom 8 bits of the return value. The top 24 bits are 0s. A status
	// code of 0 indicates success, and any other code indicates a failure. On failure, any state
	// changes made by the called contract are reverted. The scratch buffer is filled with the
	// output data returned by the called contract, even in the case of a failure status.
	//
	// This call fails if it would bring the calling contract below the existential deposit.
	// In order to destroy a contract `ext_terminate` must be used.
	//
	// If the contract traps during execution or otherwise fails to complete successfully, then
	// this function clears the scratch buffer and returns 0x0100. As with a failure status, any
	// state changes made by the called contract are reverted.
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
		let callee: <<E as Ext>::T as frame_system::Trait>::AccountId =
			read_sandbox_memory_as(ctx, callee_ptr, callee_len)?;
		let value: BalanceOf<<E as Ext>::T> =
			read_sandbox_memory_as(ctx, value_ptr, value_len)?;

		// Read input data into the scratch buffer, then take ownership of it.
		read_sandbox_memory_into_scratch(ctx, input_data_ptr, input_data_len)?;
		let input_data = mem::replace(&mut ctx.scratch_buf, Vec::new());

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
					.map_err(|err| err.buffer)
				}
				// there is not enough gas to allocate for the nested call.
				None => Err(input_data),
			}
		});

		match call_outcome {
			Ok(output) => {
				ctx.scratch_buf = output.data;
				Ok(output.status.into())
			},
			Err(buffer) => {
				ctx.scratch_buf = buffer;
				ctx.scratch_buf.clear();
				Ok(TRAP_RETURN_CODE)
			},
		}
	},

	// Instantiate a contract with the specified code hash.
	//
	// This function creates an account and executes the constructor defined in the code specified
	// by the code hash.
	//
	// If the constructor runs to completion, then this returns the status code that the newly
	// instantiated contract returns on exit in the bottom 8 bits of the return value. The top 24
	// bits are 0s. A status code of 0 indicates success, and any other code indicates a failure.
	// On failure, any state changes made by the called contract are reverted and the contract is
	// not instantiated. On a success status, the scratch buffer is filled with the encoded address
	// of the newly instantiated contract. In the case of a failure status, the scratch buffer is
	// cleared.
	//
	// This call fails if it would bring the calling contract below the existential deposit.
	// In order to destroy a contract `ext_terminate` must be used.
	//
	// If the contract traps during execution or otherwise fails to complete successfully, then
	// this function clears the scratch buffer and returns 0x0100. As with a failure status, any
	// state changes made by the called contract are reverted.

	// This function creates an account and executes initializer code. After the execution,
	// the returned buffer is saved as the code of the created account.
	//
	// Returns 0 on the successful contract instantiation and puts the address of the instantiated
	// contract into the scratch buffer. Otherwise, returns non-zero value and clears the scratch
	// buffer.
	//
	// - code_hash_ptr: a pointer to the buffer that contains the initializer code.
	// - code_hash_len: length of the initializer code buffer.
	// - gas: how much gas to devote to the execution of the initializer code.
	// - value_ptr: a pointer to the buffer with value, how much value to send.
	//   Should be decodable as a `T::Balance`. Traps otherwise.
	// - value_len: length of the value buffer.
	// - input_data_ptr: a pointer to a buffer to be used as input data to the initializer code.
	// - input_data_len: length of the input data buffer.
	ext_instantiate(
		ctx,
		code_hash_ptr: u32,
		code_hash_len: u32,
		gas: u64,
		value_ptr: u32,
		value_len: u32,
		input_data_ptr: u32,
		input_data_len: u32
	) -> u32 => {
		let code_hash: CodeHash<<E as Ext>::T> =
			read_sandbox_memory_as(ctx, code_hash_ptr, code_hash_len)?;
		let value: BalanceOf<<E as Ext>::T> =
			read_sandbox_memory_as(ctx, value_ptr, value_len)?;

		// Read input data into the scratch buffer, then take ownership of it.
		read_sandbox_memory_into_scratch(ctx, input_data_ptr, input_data_len)?;
		let input_data = mem::replace(&mut ctx.scratch_buf, Vec::new());

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
					.map_err(|err| err.buffer)
				}
				// there is not enough gas to allocate for the nested call.
				None => Err(input_data),
			}
		});
		match instantiate_outcome {
			Ok((address, output)) => {
				let is_success = output.is_success();
				ctx.scratch_buf = output.data;
				ctx.scratch_buf.clear();
				if is_success {
					// Write the address to the scratch buffer.
					address.encode_to(&mut ctx.scratch_buf);
				}
				Ok(output.status.into())
			},
			Err(buffer) => {
				ctx.scratch_buf = buffer;
				ctx.scratch_buf.clear();
				Ok(TRAP_RETURN_CODE)
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
			ctx.special_trap = Some(SpecialTrap::Termination);
		}
		Err(sp_sandbox::HostError)
	},

	// Save a data buffer as a result of the execution, terminate the execution and return a
	// successful result to the caller.
	//
	// This is the only way to return a data buffer to the caller.
	ext_return(ctx, data_ptr: u32, data_len: u32) => {
		charge_gas(
			ctx.gas_meter,
			ctx.schedule,
			&mut ctx.special_trap,
			RuntimeToken::ReturnData(data_len)
		)?;

		read_sandbox_memory_into_scratch(ctx, data_ptr, data_len)?;
		let output_buf = mem::replace(&mut ctx.scratch_buf, Vec::new());

		ctx.special_trap = Some(SpecialTrap::Return(output_buf));

		// The trap mechanism is used to immediately terminate the execution.
		// This trap should be handled appropriately before returning the result
		// to the user of this crate.
		Err(sp_sandbox::HostError)
	},

	// Stores the address of the caller into the scratch buffer.
	//
	// If this is a top-level call (i.e. initiated by an extrinsic) the origin address of the
	// extrinsic will be returned. Otherwise, if this call is initiated by another contract then the
	// address of the contract will be returned.
	ext_caller(ctx) => {
		ctx.scratch_buf.clear();
		ctx.ext.caller().encode_to(&mut ctx.scratch_buf);
		Ok(())
	},

	// Stores the address of the current contract into the scratch buffer.
	ext_address(ctx) => {
		ctx.scratch_buf.clear();
		ctx.ext.address().encode_to(&mut ctx.scratch_buf);
		Ok(())
	},

	// Stores the gas price for the current transaction into the scratch buffer.
	//
	// The data is encoded as T::Balance. The current contents of the scratch buffer are overwritten.
	ext_gas_price(ctx) => {
		ctx.scratch_buf.clear();
		ctx.ext.get_weight_price().encode_to(&mut ctx.scratch_buf);
		Ok(())
	},

	// Stores the amount of gas left into the scratch buffer.
	//
	// The data is encoded as Gas. The current contents of the scratch buffer are overwritten.
	ext_gas_left(ctx) => {
		ctx.scratch_buf.clear();
		ctx.gas_meter.gas_left().encode_to(&mut ctx.scratch_buf);
		Ok(())
	},

	// Stores the balance of the current account into the scratch buffer.
	//
	// The data is encoded as T::Balance. The current contents of the scratch buffer are overwritten.
	ext_balance(ctx) => {
		ctx.scratch_buf.clear();
		ctx.ext.balance().encode_to(&mut ctx.scratch_buf);
		Ok(())
	},

	// Stores the value transferred along with this call or as endowment into the scratch buffer.
	//
	// The data is encoded as T::Balance. The current contents of the scratch buffer are overwritten.
	ext_value_transferred(ctx) => {
		ctx.scratch_buf.clear();
		ctx.ext.value_transferred().encode_to(&mut ctx.scratch_buf);
		Ok(())
	},

	// Stores the random number for the current block for the given subject into the scratch
	// buffer.
	//
	// The data is encoded as T::Hash. The current contents of the scratch buffer are
	// overwritten.
	ext_random(ctx, subject_ptr: u32, subject_len: u32) => {
		// The length of a subject can't exceed `max_subject_len`.
		if subject_len > ctx.schedule.max_subject_len {
			return Err(sp_sandbox::HostError);
		}

		let subject_buf = read_sandbox_memory(ctx, subject_ptr, subject_len)?;
		ctx.scratch_buf.clear();
		ctx.ext.random(&subject_buf).encode_to(&mut ctx.scratch_buf);
		Ok(())
	},

	// Load the latest block timestamp into the scratch buffer
	ext_now(ctx) => {
		ctx.scratch_buf.clear();
		ctx.ext.now().encode_to(&mut ctx.scratch_buf);
		Ok(())
	},

	// Stores the minimum balance (a.k.a. existential deposit) into the scratch buffer.
	//
	// The data is encoded as T::Balance. The current contents of the scratch buffer are
	// overwritten.
	ext_minimum_balance(ctx) => {
		ctx.scratch_buf.clear();
		ctx.ext.minimum_balance().encode_to(&mut ctx.scratch_buf);
		Ok(())
	},

	// Stores the tombstone deposit into the scratch buffer.
	//
	// The data is encoded as T::Balance. The current contents of the scratch
	// buffer are overwritten.
	//
	// # Note
	//
	// The tombstone deposit is on top of the existential deposit. So in order for
	// a contract to leave a tombstone the balance of the contract must not go
	// below the sum of existential deposit and the tombstone deposit. The sum
	// is commonly referred as subsistence threshold in code.
	ext_tombstone_deposit(ctx) => {
		ctx.scratch_buf.clear();
		ctx.ext.tombstone_deposit().encode_to(&mut ctx.scratch_buf);
		Ok(())
	},

	// Decodes the given buffer as a `T::Call` and adds it to the list
	// of to-be-dispatched calls.
	//
	// All calls made it to the top-level context will be dispatched before
	// finishing the execution of the calling extrinsic.
	ext_dispatch_call(ctx, call_ptr: u32, call_len: u32) => {
		let call: <<E as Ext>::T as Trait>::Call =
			read_sandbox_memory_as(ctx, call_ptr, call_len)?;

		// We already deducted the len costs when reading from the sandbox.
		// Bill on the actual weight of the dispatched call.
		let info = call.get_dispatch_info();
		charge_gas(
			&mut ctx.gas_meter,
			ctx.schedule,
			&mut ctx.special_trap,
			RuntimeToken::DispatchWithWeight(info.weight)
		)?;

		ctx.ext.note_dispatch_call(call);

		Ok(())
	},

	// Record a request to restore the caller contract to the specified contract.
	//
	// At the finalization stage, i.e. when all changes from the extrinsic that invoked this
	// contract are committed, this function will compute a tombstone hash from the caller's
	// storage and the given code hash and if the hash matches the hash found in the tombstone at
	// the specified address - kill the caller contract and restore the destination contract and set
	// the specified `rent_allowance`. All caller's funds are transferred to the destination.
	//
	// This function doesn't perform restoration right away but defers it to the end of the
	// transaction. If there is no tombstone in the destination address or if the hashes don't match
	// then restoration is cancelled and no changes are made.
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

		ctx.ext.note_restore_to(
			dest,
			code_hash,
			rent_allowance,
			delta,
		);

		Ok(())
	},

	// Returns the size of the scratch buffer.
	//
	// For more details on the scratch buffer see `ext_scratch_read`.
	ext_scratch_size(ctx) -> u32 => {
		Ok(ctx.scratch_buf.len() as u32)
	},

	// Copy data from the scratch buffer starting from `offset` with length `len` into the contract
	// memory. The region at which the data should be put is specified by `dest_ptr`.
	//
	// In order to get size of the scratch buffer use `ext_scratch_size`. At the start of contract
	// execution, the scratch buffer is filled with the input data. Whenever a contract calls
	// function that uses the scratch buffer the contents of the scratch buffer are overwritten.
	ext_scratch_read(ctx, dest_ptr: u32, offset: u32, len: u32) => {
		let offset = offset as usize;
		if offset > ctx.scratch_buf.len() {
			// Offset can't be larger than scratch buffer length.
			return Err(sp_sandbox::HostError);
		}

		// This can't panic since `offset <= ctx.scratch_buf.len()`.
		let src = &ctx.scratch_buf[offset..];
		if src.len() != len as usize {
			return Err(sp_sandbox::HostError);
		}

		// Finally, perform the write.
		write_sandbox_memory(
			ctx.schedule,
			&mut ctx.special_trap,
			ctx.gas_meter,
			&ctx.memory,
			dest_ptr,
			src,
		)?;

		Ok(())
	},

	// Copy data from contract memory starting from `src_ptr` with length `len` into the scratch
	// buffer. This overwrites the entire scratch buffer and resizes to `len`. Specifying a `len`
	// of zero clears the scratch buffer.
	//
	// This should be used before exiting a call or instantiation in order to set the return data.
	ext_scratch_write(ctx, src_ptr: u32, len: u32) => {
		read_sandbox_memory_into_scratch(ctx, src_ptr, len)
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
			&mut ctx.special_trap,
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

	// Stores the rent allowance into the scratch buffer.
	//
	// The data is encoded as T::Balance. The current contents of the scratch buffer are overwritten.
	ext_rent_allowance(ctx) => {
		ctx.scratch_buf.clear();
		ctx.ext.rent_allowance().encode_to(&mut ctx.scratch_buf);

		Ok(())
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

	// Stores the current block number of the current contract into the scratch buffer.
	ext_block_number(ctx) => {
		ctx.scratch_buf.clear();
		ctx.ext.block_number().encode_to(&mut ctx.scratch_buf);
		Ok(())
	},

	// Retrieve the value under the given key from the **runtime** storage and return 0.
	// If there is no entry under the given key then this function will return 1 and
	// clear the scratch buffer.
	//
	// - key_ptr: the pointer into the linear memory where the requested value is placed.
	// - key_len: the length of the key in bytes.
	ext_get_runtime_storage(ctx, key_ptr: u32, key_len: u32) -> u32 => {
		// Steal the scratch buffer so that we hopefully save an allocation for the `key_buf`.
		read_sandbox_memory_into_scratch(ctx, key_ptr, key_len)?;
		let key_buf = mem::replace(&mut ctx.scratch_buf, Vec::new());

		match ctx.ext.get_runtime_storage(&key_buf) {
			Some(value_buf) => {
				// The given value exists.
				ctx.scratch_buf = value_buf;
				Ok(0)
			}
			None => {
				// Put back the `key_buf` and allow its allocation to be reused.
				ctx.scratch_buf = key_buf;
				ctx.scratch_buf.clear();
				Ok(1)
			}
		}
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

/// Computes the given hash function on the scratch buffer.
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
	// Copy the input buffer directly into the scratch buffer to avoid
	// heap allocations.
	let input = read_sandbox_memory(ctx, input_ptr, input_len)?;
	// Compute the hash on the scratch buffer using the given hash function.
	let hash = hash_fn(&input);
	// Write the resulting hash back into the sandboxed output buffer.
	write_sandbox_memory(
		ctx.schedule,
		&mut ctx.special_trap,
		ctx.gas_meter,
		&ctx.memory,
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
