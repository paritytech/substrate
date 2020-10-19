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

use crate::{HostFnWeights, Schedule, Trait, CodeHash, BalanceOf, Error};
use crate::exec::{
	Ext, ExecResult, ExecReturnValue, StorageKey, TopicOf, ReturnFlags, ExecError
};
use crate::gas::{Gas, GasMeter, Token, GasMeterResult};
use crate::wasm::env_def::ConvertibleToWasm;
use sp_sandbox;
use parity_wasm::elements::ValueType;
use frame_system;
use frame_support::dispatch::DispatchError;
use sp_std::prelude::*;
use codec::{Decode, Encode};
use sp_runtime::traits::SaturatedConversion;
use sp_io::hashing::{
	keccak_256,
	blake2_256,
	blake2_128,
	sha2_256,
};

/// Every error that can be returned to a contract when it calls any of the host functions.
#[repr(u32)]
pub enum ReturnCode {
	/// API call successful.
	Success = 0,
	/// The called function trapped and has its state changes reverted.
	/// In this case no output buffer is returned.
	CalleeTrapped = 1,
	/// The called function ran to completion but decided to revert its state.
	/// An output buffer is returned when one was supplied.
	CalleeReverted = 2,
	/// The passed key does not exist in storage.
	KeyNotFound = 3,
	/// Transfer failed because it would have brought the sender's total balance below the
	/// subsistence threshold.
	BelowSubsistenceThreshold = 4,
	/// Transfer failed for other reasons. Most probably reserved or locked balance of the
	/// sender prevents the transfer.
	TransferFailed = 5,
	/// The newly created contract is below the subsistence threshold after executing
	/// its constructor.
	NewContractNotFunded = 6,
	/// No code could be found at the supplied code hash.
	CodeNotFound = 7,
	/// The contract that was called is either no contract at all (a plain account)
	/// or is a tombstone.
	NotCallable = 8,
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
	fn from(from: ExecReturnValue) -> Self {
		if from.flags.contains(ReturnFlags::REVERT) {
			Self::CalleeReverted
		} else {
			Self::Success
		}
	}
}

/// The data passed through when a contract uses `seal_return`.
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
	/// Signals that trap was generated in response to call `seal_return` host function.
	Return(ReturnData),
	/// Signals that a trap was generated in response to a successful call to the
	/// `seal_terminate` host function.
	Termination,
	/// Signals that a trap was generated because of a successful restoration.
	Restoration,
}

/// Can only be used for one call.
pub(crate) struct Runtime<'a, E: Ext + 'a> {
	ext: &'a mut E,
	input_data: Option<Vec<u8>>,
	schedule: &'a Schedule<E::T>,
	memory: sp_sandbox::Memory,
	gas_meter: &'a mut GasMeter<E::T>,
	trap_reason: Option<TrapReason>,
}
impl<'a, E: Ext + 'a> Runtime<'a, E> {
	pub(crate) fn new(
		ext: &'a mut E,
		input_data: Vec<u8>,
		schedule: &'a Schedule<E::T>,
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

/// Converts the sandbox result and the runtime state into the execution outcome.
///
/// It evaluates information stored in the `trap_reason` variable of the runtime and
/// bases the outcome on the value if this variable. Only if `trap_reason` is `None`
/// the result of the sandbox is evaluated.
pub(crate) fn to_execution_result<E: Ext>(
	runtime: Runtime<E>,
	sandbox_result: Result<sp_sandbox::ReturnValue, sp_sandbox::Error>,
) -> ExecResult {
	// If a trap reason is set we base our decision solely on that.
	if let Some(trap_reason) = runtime.trap_reason {
		return match trap_reason {
			// The trap was the result of the execution `return` host function.
			TrapReason::Return(ReturnData{ flags, data }) => {
				let flags = ReturnFlags::from_bits(flags).ok_or_else(||
					"used reserved bit in return flags"
				)?;
				Ok(ExecReturnValue {
					flags,
					data,
				})
			},
			TrapReason::Termination => {
				Ok(ExecReturnValue {
					flags: ReturnFlags::empty(),
					data: Vec::new(),
				})
			},
			TrapReason::Restoration => {
				Ok(ExecReturnValue {
					flags: ReturnFlags::empty(),
					data: Vec::new(),
				})
			},
			TrapReason::SupervisorError(error) => Err(error)?,
		}
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
			Err(Error::<E::T>::ContractTrapped)?
	}
}

#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
#[derive(Copy, Clone)]
pub enum RuntimeToken {
	/// Charge the gas meter with the cost of a metering block. The charged costs are
	/// the supplied cost of the block plus the overhead of the metering itself.
	MeteringBlock(u32),
	/// Weight of calling `seal_caller`.
	Caller,
	/// Weight of calling `seal_address`.
	Address,
	/// Weight of calling `seal_gas_left`.
	GasLeft,
	/// Weight of calling `seal_balance`.
	Balance,
	/// Weight of calling `seal_value_transferred`.
	ValueTransferred,
	/// Weight of calling `seal_minimum_balance`.
	MinimumBalance,
	/// Weight of calling `seal_tombstone_deposit`.
	TombstoneDeposit,
	/// Weight of calling `seal_rent_allowance`.
	RentAllowance,
	/// Weight of calling `seal_block_number`.
	BlockNumber,
	/// Weight of calling `seal_now`.
	Now,
	/// Weight of calling `seal_weight_to_fee`.
	WeightToFee,
	/// Weight of calling `seal_input` without the weight of copying the input.
	InputBase,
	/// Weight of copying the input data for the given size.
	InputCopyOut(u32),
	/// Weight of calling `seal_return` for the given output size.
	Return(u32),
	/// Weight of calling `seal_terminate`.
	Terminate,
	/// Weight of calling `seal_restore_to` per number of supplied delta entries.
	RestoreTo(u32),
	/// Weight of calling `seal_random`. It includes the weight for copying the subject.
	Random,
	/// Weight of calling `seal_reposit_event` with the given number of topics and event size.
	DepositEvent{num_topic: u32, len: u32},
	/// Weight of calling `seal_set_rent_allowance`.
	SetRentAllowance,
	/// Weight of calling `seal_set_storage` for the given storage item size.
	SetStorage(u32),
	/// Weight of calling `seal_clear_storage`.
	ClearStorage,
	/// Weight of calling `seal_get_storage` without output weight.
	GetStorageBase,
	/// Weight of an item received via `seal_get_storage` for the given size.
	GetStorageCopyOut(u32),
	/// Weight of calling `seal_transfer`.
	Transfer,
	/// Weight of calling `seal_call` for the given input size.
	CallBase(u32),
	/// Weight of the transfer performed during a call.
	CallSurchargeTransfer,
	/// Weight of output received through `seal_call` for the given size.
	CallCopyOut(u32),
	/// Weight of calling `seal_instantiate` for the given input size without output weight.
	/// This includes the transfer as an instantiate without a value will always be below
	/// the existential deposit and is disregarded as corner case.
	InstantiateBase(u32),
	/// Weight of output received through `seal_instantiate` for the given size.
	InstantiateCopyOut(u32),
	/// Weight of calling `seal_hash_sha_256` for the given input size.
	HashSha256(u32),
	/// Weight of calling `seal_hash_keccak_256` for the given input size.
	HashKeccak256(u32),
	/// Weight of calling `seal_hash_blake2_256` for the given input size.
	HashBlake256(u32),
	/// Weight of calling `seal_hash_blake2_128` for the given input size.
	HashBlake128(u32),
}

impl<T: Trait> Token<T> for RuntimeToken {
	type Metadata = HostFnWeights;

	fn calculate_amount(&self, s: &Self::Metadata) -> Gas {
		use self::RuntimeToken::*;
		match *self {
			MeteringBlock(amount) => s.gas.saturating_add(amount.into()),
			Caller => s.caller,
			Address => s.address,
			GasLeft => s.gas_left,
			Balance => s.balance,
			ValueTransferred => s.value_transferred,
			MinimumBalance => s.minimum_balance,
			TombstoneDeposit => s.tombstone_deposit,
			RentAllowance => s.rent_allowance,
			BlockNumber => s.block_number,
			Now => s.now,
			WeightToFee => s.weight_to_fee,
			InputBase => s.input,
			InputCopyOut(len) => s.input_per_byte.saturating_mul(len.into()),
			Return(len) => s.r#return
				.saturating_add(s.return_per_byte.saturating_mul(len.into())),
			Terminate => s.terminate,
			RestoreTo(delta) => s.restore_to
				.saturating_add(s.restore_to_per_delta.saturating_mul(delta.into())),
			Random => s.random,
			DepositEvent{num_topic, len} => s.deposit_event
				.saturating_add(s.deposit_event_per_topic.saturating_mul(num_topic.into()))
				.saturating_add(s.deposit_event_per_byte.saturating_mul(len.into())),
			SetRentAllowance => s.set_rent_allowance,
			SetStorage(len) => s.set_storage
				.saturating_add(s.set_storage_per_byte.saturating_mul(len.into())),
			ClearStorage => s.clear_storage,
			GetStorageBase => s.get_storage,
			GetStorageCopyOut(len) => s.get_storage_per_byte.saturating_mul(len.into()),
			Transfer => s.transfer,
			CallBase(len) => s.call
				.saturating_add(s.call_per_input_byte.saturating_mul(len.into())),
			CallSurchargeTransfer => s.call_transfer_surcharge,
			CallCopyOut(len) => s.call_per_output_byte.saturating_mul(len.into()),
			InstantiateBase(len) => s.instantiate
				.saturating_add(s.instantiate_per_input_byte.saturating_mul(len.into())),
			InstantiateCopyOut(len) => s.instantiate_per_output_byte
				.saturating_mul(len.into()),
			HashSha256(len) => s.hash_sha2_256
				.saturating_add(s.hash_sha2_256_per_byte.saturating_mul(len.into())),
			HashKeccak256(len) => s.hash_keccak_256
				.saturating_add(s.hash_keccak_256_per_byte.saturating_mul(len.into())),
			HashBlake256(len) => s.hash_blake2_256
				.saturating_add(s.hash_blake2_256_per_byte.saturating_mul(len.into())),
			HashBlake128(len) => s.hash_blake2_128
				.saturating_add(s.hash_blake2_128_per_byte.saturating_mul(len.into())),
		}
	}
}

/// Charge the gas meter with the specified token.
///
/// Returns `Err(HostError)` if there is not enough gas.
fn charge_gas<E, Tok>(ctx: &mut Runtime<E>, token: Tok) -> Result<(), sp_sandbox::HostError>
where
	E: Ext,
	Tok: Token<E::T, Metadata=HostFnWeights>,
{
	match ctx.gas_meter.charge(&ctx.schedule.host_fn_weights, token) {
		GasMeterResult::Proceed => Ok(()),
		GasMeterResult::OutOfGas =>  {
			ctx.trap_reason = Some(TrapReason::SupervisorError(Error::<E::T>::OutOfGas.into()));
			Err(sp_sandbox::HostError)
		},
	}
}

/// Read designated chunk from the sandbox memory.
///
/// Returns `Err` if one of the following conditions occurs:
///
/// - requested buffer is not within the bounds of the sandbox memory.
fn read_sandbox_memory<E: Ext>(
	ctx: &mut Runtime<E>,
	ptr: u32,
	len: u32,
) -> Result<Vec<u8>, sp_sandbox::HostError> {
	let mut buf = vec![0u8; len as usize];
	ctx.memory.get(ptr, buf.as_mut_slice())
		.map_err(|_| store_err(ctx, Error::<E::T>::OutOfBounds))?;
	Ok(buf)
}

/// Read designated chunk from the sandbox memory into the supplied buffer.
///
/// Returns `Err` if one of the following conditions occurs:
///
/// - requested buffer is not within the bounds of the sandbox memory.
fn read_sandbox_memory_into_buf<E: Ext>(
	ctx: &mut Runtime<E>,
	ptr: u32,
	buf: &mut [u8],
) -> Result<(), sp_sandbox::HostError> {
	ctx.memory.get(ptr, buf).map_err(|_| store_err(ctx, Error::<E::T>::OutOfBounds))
}

/// Read designated chunk from the sandbox memory and attempt to decode into the specified type.
///
/// Returns `Err` if one of the following conditions occurs:
///
/// - requested buffer is not within the bounds of the sandbox memory.
/// - the buffer contents cannot be decoded as the required type.
fn read_sandbox_memory_as<E: Ext, D: Decode>(
	ctx: &mut Runtime<E>,
	ptr: u32,
	len: u32,
) -> Result<D, sp_sandbox::HostError> {
	let buf = read_sandbox_memory(ctx, ptr, len)?;
	D::decode(&mut &buf[..]).map_err(|_| store_err(ctx, Error::<E::T>::DecodingFailed))
}

/// Write the given buffer to the designated location in the sandbox memory.
///
/// Returns `Err` if one of the following conditions occurs:
///
/// - designated area is not within the bounds of the sandbox memory.
fn write_sandbox_memory<E: Ext>(
	ctx: &mut Runtime<E>,
	ptr: u32,
	buf: &[u8],
) -> Result<(), sp_sandbox::HostError> {
	ctx.memory.set(ptr, buf).map_err(|_| store_err(ctx, Error::<E::T>::OutOfBounds))
}

/// Write the given buffer and its length to the designated locations in sandbox memory and
/// charge gas according to the token returned by `create_token`.
//
/// `out_ptr` is the location in sandbox memory where `buf` should be written to.
/// `out_len_ptr` is an in-out location in sandbox memory. It is read to determine the
/// length of the buffer located at `out_ptr`. If that buffer is large enough the actual
/// `buf.len()` is written to this location.
///
/// If `out_ptr` is set to the sentinel value of `u32::max_value()` and `allow_skip` is true the
/// operation is skipped and `Ok` is returned. This is supposed to help callers to make copying
/// output optional. For example to skip copying back the output buffer of an `seal_call`
/// when the caller is not interested in the result.
///
/// `create_token` can optionally instruct this function to charge the gas meter with the token
/// it returns. `create_token` receives the variable amount of bytes that are about to be copied by
/// this function.
///
/// In addition to the error conditions of `write_sandbox_memory` this functions returns
/// `Err` if the size of the buffer located at `out_ptr` is too small to fit `buf`.
fn write_sandbox_output<E: Ext>(
	ctx: &mut Runtime<E>,
	out_ptr: u32,
	out_len_ptr: u32,
	buf: &[u8],
	allow_skip: bool,
	create_token: impl FnOnce(u32) -> Option<RuntimeToken>,
) -> Result<(), sp_sandbox::HostError> {
	if allow_skip && out_ptr == u32::max_value() {
		return Ok(());
	}

	let buf_len = buf.len() as u32;
	let len: u32 = read_sandbox_memory_as(ctx, out_len_ptr, 4)?;

	if len < buf_len {
		Err(store_err(ctx, Error::<E::T>::OutputBufferTooSmall))?
	}

	if let Some(token) = create_token(buf_len) {
		charge_gas(ctx, token)?;
	}

	ctx.memory.set(out_ptr, buf).and_then(|_| {
		ctx.memory.set(out_len_ptr, &buf_len.encode())
	})
	.map_err(|_| store_err(ctx, Error::<E::T>::OutOfBounds))?;

	Ok(())
}

/// Supply to `write_sandbox_output` to indicate that the gas meter should not be charged.
///
/// This is only appropriate when writing out data of constant size that does not depend on user
/// input. In this case the costs for this copy was already charged as part of the token at
/// the beginning of the API entry point.
fn already_charged(_: u32) -> Option<RuntimeToken> {
	None
}

/// Stores a DispatchError returned from an Ext function into the trap_reason.
///
/// This allows through supervisor generated errors to the caller.
fn store_err<E, Error>(ctx: &mut Runtime<E>, err: Error) -> sp_sandbox::HostError where
	E: Ext,
	Error: Into<DispatchError>,
{
	ctx.trap_reason = Some(TrapReason::SupervisorError(err.into()));
	sp_sandbox::HostError
}

/// Fallible conversion of `DispatchError` to `ReturnCode`.
fn err_into_return_code<T: Trait>(from: DispatchError) -> Result<ReturnCode, DispatchError> {
	use ReturnCode::*;

	let below_sub = Error::<T>::BelowSubsistenceThreshold.into();
	let transfer_failed = Error::<T>::TransferFailed.into();
	let not_funded = Error::<T>::NewContractNotFunded.into();
	let no_code = Error::<T>::CodeNotFound.into();
	let invalid_contract = Error::<T>::NotCallable.into();

	match from {
		x if x == below_sub => Ok(BelowSubsistenceThreshold),
		x if x == transfer_failed => Ok(TransferFailed),
		x if x == not_funded => Ok(NewContractNotFunded),
		x if x == no_code => Ok(CodeNotFound),
		x if x == invalid_contract => Ok(NotCallable),
		err => Err(err)
	}
}

/// Fallible conversion of a `ExecResult` to `ReturnCode`.
fn exec_into_return_code<T: Trait>(from: ExecResult) -> Result<ReturnCode, DispatchError> {
	use crate::exec::ErrorOrigin::Callee;

	let ExecError { error, origin } = match from {
		Ok(retval) => return Ok(retval.into()),
		Err(err) => err,
	};

	match (error, origin) {
		(_, Callee) => Ok(ReturnCode::CalleeTrapped),
		(err, _) => err_into_return_code::<T>(err)
	}
}

/// Used by Runtime API that calls into other contracts.
///
/// Those need to transform the the `ExecResult` returned from the execution into
/// a `ReturnCode`. If this conversion fails because the `ExecResult` constitutes a
/// a fatal error then this error is stored in the `ExecutionContext` so it can be
/// extracted for display in the UI.
fn map_exec_result<E: Ext>(ctx: &mut Runtime<E>, result: ExecResult)
	-> Result<ReturnCode, sp_sandbox::HostError>
{
	match exec_into_return_code::<E::T>(result) {
		Ok(code) => Ok(code),
		Err(err) => Err(store_err(ctx, err)),
	}
}

/// Try to convert an error into a `ReturnCode`.
///
/// Used to decide between fatal and non-fatal errors.
fn map_dispatch_result<T, E: Ext>(ctx: &mut Runtime<E>, result: Result<T, DispatchError>)
	-> Result<ReturnCode, sp_sandbox::HostError>
{
	let err = if let Err(err) = result {
		err
	} else {
		return Ok(ReturnCode::Success)
	};

	match err_into_return_code::<E::T>(err) {
		Ok(code) => Ok(code),
		Err(err) => Err(store_err(ctx, err)),
	}
}

// ***********************************************************
// * AFTER MAKING A CHANGE MAKE SURE TO UPDATE COMPLEXITY.MD *
// ***********************************************************

// Define a function `fn init_env<E: Ext>() -> HostFunctionSet<E>` that returns
// a function set which can be imported by an executed contract.
//
// # Note
//
// Any input that leads to a out of bound error (reading or writing) or failing to decode
// data passed to the supervisor will lead to a trap. This is not documented explicitly
// for every function.
define_env!(Env, <E: Ext>,

	// Account for used gas. Traps if gas used is greater than gas limit.
	//
	// NOTE: This is a implementation defined call and is NOT a part of the public API.
	// This call is supposed to be called only by instrumentation injected code.
	//
	// - amount: How much gas is used.
	gas(ctx, amount: u32) => {
		charge_gas(ctx, RuntimeToken::MeteringBlock(amount))?;
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
	// # Traps
	//
	// - If value length exceeds the configured maximum value length of a storage entry.
	// - Upon trying to set an empty storage entry (value length is 0).
	seal_set_storage(ctx, key_ptr: u32, value_ptr: u32, value_len: u32) => {
		charge_gas(ctx, RuntimeToken::SetStorage(value_len))?;
		if value_len > ctx.ext.max_value_size() {
			Err(store_err(ctx, Error::<E::T>::ValueTooLarge))?;
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
	seal_clear_storage(ctx, key_ptr: u32) => {
		charge_gas(ctx, RuntimeToken::ClearStorage)?;
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
	// `ReturnCode::KeyNotFound`
	seal_get_storage(ctx, key_ptr: u32, out_ptr: u32, out_len_ptr: u32) -> ReturnCode => {
		charge_gas(ctx, RuntimeToken::GetStorageBase)?;
		let mut key: StorageKey = [0; 32];
		read_sandbox_memory_into_buf(ctx, key_ptr, &mut key)?;
		if let Some(value) = ctx.ext.get_storage(&key) {
			write_sandbox_output(ctx, out_ptr, out_len_ptr, &value, false, |len| {
				Some(RuntimeToken::GetStorageCopyOut(len))
			})?;
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
	// # Errors
	//
	// `ReturnCode::BelowSubsistenceThreshold`
	// `ReturnCode::TransferFailed`
	seal_transfer(
		ctx,
		account_ptr: u32,
		account_len: u32,
		value_ptr: u32,
		value_len: u32
	) -> ReturnCode => {
		charge_gas(ctx, RuntimeToken::Transfer)?;
		let callee: <<E as Ext>::T as frame_system::Trait>::AccountId =
			read_sandbox_memory_as(ctx, account_ptr, account_len)?;
		let value: BalanceOf<<E as Ext>::T> =
			read_sandbox_memory_as(ctx, value_ptr, value_len)?;

		let result = ctx.ext.transfer(&callee, value);
		map_dispatch_result(ctx, result)
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
	// An error means that the call wasn't successful output buffer is returned unless
	// stated otherwise.
	//
	// `ReturnCode::CalleeReverted`: Output buffer is returned.
	// `ReturnCode::CalleeTrapped`
	// `ReturnCode::BelowSubsistenceThreshold`
	// `ReturnCode::TransferFailed`
	// `ReturnCode::NotCallable`
	seal_call(
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
		charge_gas(ctx, RuntimeToken::CallBase(input_data_len))?;
		let callee: <<E as Ext>::T as frame_system::Trait>::AccountId =
			read_sandbox_memory_as(ctx, callee_ptr, callee_len)?;
		let value: BalanceOf<<E as Ext>::T> = read_sandbox_memory_as(ctx, value_ptr, value_len)?;
		let input_data = read_sandbox_memory(ctx, input_data_ptr, input_data_len)?;

		if value > 0.into() {
			charge_gas(ctx, RuntimeToken::CallSurchargeTransfer)?;
		}

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
				}
				// there is not enough gas to allocate for the nested call.
				None => Err(Error::<<E as Ext>::T>::OutOfGas.into()),
			}
		});

		if let Ok(output) = &call_outcome {
			write_sandbox_output(ctx, output_ptr, output_len_ptr, &output.data, true, |len| {
				Some(RuntimeToken::CallCopyOut(len))
			})?;
		}
		map_exec_result(ctx, call_outcome)
	},

	// Instantiate a contract with the specified code hash.
	//
	// This function creates an account and executes the constructor defined in the code specified
	// by the code hash. The address of this new account is copied to `address_ptr` and its length
	// to `address_len_ptr`. The constructors output buffer is copied to `output_ptr` and its
	// length to `output_len_ptr`. The copy of the output buffer and address can be skipped by
	// supplying the sentinel value of `u32::max_value()` to `output_ptr` or `address_ptr`.
	//
	// After running the constructor it is verfied that the contract account holds at
	// least the subsistence threshold. If that is not the case the instantion fails and
	// the contract is not created.
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
	// Please consult the `ReturnCode` enum declaration for more information on those
	// errors. Here we only note things specific to this function.
	//
	// An error means that the account wasn't created and no address or output buffer
	// is returned unless stated otherwise.
	//
	// `ReturnCode::CalleeReverted`: Output buffer is returned.
	// `ReturnCode::CalleeTrapped`
	// `ReturnCode::BelowSubsistenceThreshold`
	// `ReturnCode::TransferFailed`
	// `ReturnCode::NewContractNotFunded`
	// `ReturnCode::CodeNotFound`
	seal_instantiate(
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
		charge_gas(ctx, RuntimeToken::InstantiateBase(input_data_len))?;
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
				}
				// there is not enough gas to allocate for the nested call.
				None => Err(Error::<<E as Ext>::T>::OutOfGas.into()),
			}
		});
		if let Ok((address, output)) = &instantiate_outcome {
			if !output.flags.contains(ReturnFlags::REVERT) {
				write_sandbox_output(
					ctx, address_ptr, address_len_ptr, &address.encode(), true, already_charged,
				)?;
			}
			write_sandbox_output(ctx, output_ptr, output_len_ptr, &output.data, true, |len| {
				Some(RuntimeToken::InstantiateCopyOut(len))
			})?;
		}
		map_exec_result(ctx, instantiate_outcome.map(|(_id, retval)| retval))
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
	//
	// # Traps
	//
	// - The contract is live i.e is already on the call stack.
	seal_terminate(
		ctx,
		beneficiary_ptr: u32,
		beneficiary_len: u32
	) => {
		charge_gas(ctx, RuntimeToken::Terminate)?;
		let beneficiary: <<E as Ext>::T as frame_system::Trait>::AccountId =
			read_sandbox_memory_as(ctx, beneficiary_ptr, beneficiary_len)?;

		if let Ok(_) = ctx.ext.terminate(&beneficiary) {
			ctx.trap_reason = Some(TrapReason::Termination);
		}
		Err(sp_sandbox::HostError)
	},

	seal_input(ctx, buf_ptr: u32, buf_len_ptr: u32) => {
		charge_gas(ctx, RuntimeToken::InputBase)?;
		if let Some(input) = ctx.input_data.take() {
			write_sandbox_output(ctx, buf_ptr, buf_len_ptr, &input, false, |len| {
				Some(RuntimeToken::InputCopyOut(len))
			})
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
	// seal_return(0, 0, 0);
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
	seal_return(ctx, flags: u32, data_ptr: u32, data_len: u32) => {
		charge_gas(ctx, RuntimeToken::Return(data_len))?;
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
	seal_caller(ctx, out_ptr: u32, out_len_ptr: u32) => {
		charge_gas(ctx, RuntimeToken::Caller)?;
		write_sandbox_output(
			ctx, out_ptr, out_len_ptr, &ctx.ext.caller().encode(), false, already_charged
		)
	},

	// Stores the address of the current contract into the supplied buffer.
	//
	// The value is stored to linear memory at the address pointed to by `out_ptr`.
	// `out_len_ptr` must point to a u32 value that describes the available space at
	// `out_ptr`. This call overwrites it with the size of the value. If the available
	// space at `out_ptr` is less than the size of the value a trap is triggered.
	seal_address(ctx, out_ptr: u32, out_len_ptr: u32) => {
		charge_gas(ctx, RuntimeToken::Address)?;
		write_sandbox_output(
			ctx, out_ptr, out_len_ptr, &ctx.ext.address().encode(), false, already_charged
		)
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
	seal_weight_to_fee(ctx, gas: u64, out_ptr: u32, out_len_ptr: u32) => {
		charge_gas(ctx, RuntimeToken::WeightToFee)?;
		write_sandbox_output(
			ctx, out_ptr, out_len_ptr, &ctx.ext.get_weight_price(gas).encode(), false,
			already_charged
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
	seal_gas_left(ctx, out_ptr: u32, out_len_ptr: u32) => {
		charge_gas(ctx, RuntimeToken::GasLeft)?;
		write_sandbox_output(
			ctx, out_ptr, out_len_ptr, &ctx.gas_meter.gas_left().encode(), false, already_charged
		)
	},

	// Stores the balance of the current account into the supplied buffer.
	//
	// The value is stored to linear memory at the address pointed to by `out_ptr`.
	// `out_len_ptr` must point to a u32 value that describes the available space at
	// `out_ptr`. This call overwrites it with the size of the value. If the available
	// space at `out_ptr` is less than the size of the value a trap is triggered.
	//
	// The data is encoded as T::Balance.
	seal_balance(ctx, out_ptr: u32, out_len_ptr: u32) => {
		charge_gas(ctx, RuntimeToken::Balance)?;
		write_sandbox_output(
			ctx, out_ptr, out_len_ptr, &ctx.ext.balance().encode(), false, already_charged
		)
	},

	// Stores the value transferred along with this call or as endowment into the supplied buffer.
	//
	// The value is stored to linear memory at the address pointed to by `out_ptr`.
	// `out_len_ptr` must point to a u32 value that describes the available space at
	// `out_ptr`. This call overwrites it with the size of the value. If the available
	// space at `out_ptr` is less than the size of the value a trap is triggered.
	//
	// The data is encoded as T::Balance.
	seal_value_transferred(ctx, out_ptr: u32, out_len_ptr: u32) => {
		charge_gas(ctx, RuntimeToken::ValueTransferred)?;
		write_sandbox_output(
			ctx, out_ptr, out_len_ptr, &ctx.ext.value_transferred().encode(), false,
			already_charged
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
	seal_random(ctx, subject_ptr: u32, subject_len: u32, out_ptr: u32, out_len_ptr: u32) => {
		charge_gas(ctx, RuntimeToken::Random)?;
		// The length of a subject can't exceed `max_subject_len`.
		if subject_len > ctx.schedule.max_subject_len {
			return Err(sp_sandbox::HostError);
		}
		let subject_buf = read_sandbox_memory(ctx, subject_ptr, subject_len)?;
		write_sandbox_output(
			ctx, out_ptr, out_len_ptr, &ctx.ext.random(&subject_buf).encode(), false,
			already_charged
		)
	},

	// Load the latest block timestamp into the supplied buffer
	//
	// The value is stored to linear memory at the address pointed to by `out_ptr`.
	// `out_len_ptr` must point to a u32 value that describes the available space at
	// `out_ptr`. This call overwrites it with the size of the value. If the available
	// space at `out_ptr` is less than the size of the value a trap is triggered.
	seal_now(ctx, out_ptr: u32, out_len_ptr: u32) => {
		charge_gas(ctx, RuntimeToken::Now)?;
		write_sandbox_output(
			ctx, out_ptr, out_len_ptr, &ctx.ext.now().encode(), false, already_charged
		)
	},

	// Stores the minimum balance (a.k.a. existential deposit) into the supplied buffer.
	//
	// The data is encoded as T::Balance.
	seal_minimum_balance(ctx, out_ptr: u32, out_len_ptr: u32) => {
		charge_gas(ctx, RuntimeToken::MinimumBalance)?;
		write_sandbox_output(
			ctx, out_ptr, out_len_ptr, &ctx.ext.minimum_balance().encode(), false, already_charged
		)
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
	seal_tombstone_deposit(ctx, out_ptr: u32, out_len_ptr: u32) => {
		charge_gas(ctx, RuntimeToken::TombstoneDeposit)?;
		write_sandbox_output(
			ctx, out_ptr, out_len_ptr, &ctx.ext.tombstone_deposit().encode(), false,
			already_charged
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
	//
	// # Traps
	//
	// - Tombstone hashes do not match
	// - Calling cantract is live i.e is already on the call stack.
	seal_restore_to(
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
		charge_gas(ctx, RuntimeToken::RestoreTo(delta_count))?;
		let dest: <<E as Ext>::T as frame_system::Trait>::AccountId =
			read_sandbox_memory_as(ctx, dest_ptr, dest_len)?;
		let code_hash: CodeHash<<E as Ext>::T> =
			read_sandbox_memory_as(ctx, code_hash_ptr, code_hash_len)?;
		let rent_allowance: BalanceOf<<E as Ext>::T> =
			read_sandbox_memory_as(ctx, rent_allowance_ptr, rent_allowance_len)?;
		let delta = {
			// We can eagerly allocate because we charged for the complete delta count already
			let mut delta = Vec::with_capacity(delta_count as usize);
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
	seal_deposit_event(ctx, topics_ptr: u32, topics_len: u32, data_ptr: u32, data_len: u32) => {
		let num_topic = topics_len
			.checked_div(sp_std::mem::size_of::<TopicOf<E::T>>() as u32)
			.ok_or_else(|| store_err(ctx, "Zero sized topics are not allowed"))?;
		charge_gas(ctx, RuntimeToken::DepositEvent {
			num_topic,
			len: data_len,
		})?;
		if data_len > ctx.ext.max_value_size() {
			Err(store_err(ctx, Error::<E::T>::ValueTooLarge))?;
		}

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

		ctx.ext.deposit_event(topics, event_data);

		Ok(())
	},

	// Set rent allowance of the contract
	//
	// - value_ptr: a pointer to the buffer with value, how much to allow for rent
	//   Should be decodable as a `T::Balance`. Traps otherwise.
	// - value_len: length of the value buffer.
	seal_set_rent_allowance(ctx, value_ptr: u32, value_len: u32) => {
		charge_gas(ctx, RuntimeToken::SetRentAllowance)?;
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
	seal_rent_allowance(ctx, out_ptr: u32, out_len_ptr: u32) => {
		charge_gas(ctx, RuntimeToken::RentAllowance)?;
		write_sandbox_output(
			ctx, out_ptr, out_len_ptr, &ctx.ext.rent_allowance().encode(), false, already_charged
		)
	},

	// Prints utf8 encoded string from the data buffer.
	// Only available on `--dev` chains.
	// This function may be removed at any time, superseded by a more general contract debugging feature.
	seal_println(ctx, str_ptr: u32, str_len: u32) => {
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
	seal_block_number(ctx, out_ptr: u32, out_len_ptr: u32) => {
		charge_gas(ctx, RuntimeToken::BlockNumber)?;
		write_sandbox_output(
			ctx, out_ptr, out_len_ptr, &ctx.ext.block_number().encode(), false, already_charged
		)
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
	seal_hash_sha2_256(ctx, input_ptr: u32, input_len: u32, output_ptr: u32) => {
		charge_gas(ctx, RuntimeToken::HashSha256(input_len))?;
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
	seal_hash_keccak_256(ctx, input_ptr: u32, input_len: u32, output_ptr: u32) => {
		charge_gas(ctx, RuntimeToken::HashKeccak256(input_len))?;
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
	seal_hash_blake2_256(ctx, input_ptr: u32, input_len: u32, output_ptr: u32) => {
		charge_gas(ctx, RuntimeToken::HashBlake256(input_len))?;
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
	seal_hash_blake2_128(ctx, input_ptr: u32, input_len: u32, output_ptr: u32) => {
		charge_gas(ctx, RuntimeToken::HashBlake128(input_len))?;
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
	items.sort_by(|a, b| {
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
