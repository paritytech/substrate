// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

//! Environment definition of the wasm smart-contract runtime.

use crate::{
	HostFnWeights, Schedule, Config, CodeHash, BalanceOf, Error,
	exec::{Ext, StorageKey, TopicOf},
	gas::{Gas, GasMeter, Token, GasMeterResult, ChargedAmount},
	wasm::env_def::ConvertibleToWasm,
};
use parity_wasm::elements::ValueType;
use frame_support::{dispatch::DispatchError, ensure};
use sp_std::prelude::*;
use codec::{Decode, DecodeAll, Encode};
use sp_runtime::traits::SaturatedConversion;
use sp_core::crypto::UncheckedFrom;
use sp_io::hashing::{
	keccak_256,
	blake2_256,
	blake2_128,
	sha2_256,
};
use pallet_contracts_primitives::{ExecResult, ExecReturnValue, ReturnFlags, ExecError};

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
pub struct ReturnData {
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
pub enum TrapReason {
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

impl<T: Into<DispatchError>> From<T> for TrapReason {
	fn from(from: T) -> Self {
		Self::SupervisorError(from.into())
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
	/// Weight of calling `seal_instantiate` for the given input and salt without output weight.
	/// This includes the transfer as an instantiate without a value will always be below
	/// the existential deposit and is disregarded as corner case.
	InstantiateBase{input_data_len: u32, salt_len: u32},
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
	/// Weight charged by a chain extension through `seal_call_chain_extension`.
	ChainExtension(u64),
	/// Weight charged for copying data from the sandbox.
	CopyIn(u32),
}

impl<T: Config> Token<T> for RuntimeToken
where
	T::AccountId: UncheckedFrom<T::Hash>, T::AccountId: AsRef<[u8]>
{
	type Metadata = HostFnWeights<T>;

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
			InstantiateBase{input_data_len, salt_len} => s.instantiate
				.saturating_add(s.instantiate_per_input_byte.saturating_mul(input_data_len.into()))
				.saturating_add(s.instantiate_per_salt_byte.saturating_mul(salt_len.into())),
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
			ChainExtension(amount) => amount,
			CopyIn(len) => s.return_per_byte.saturating_mul(len.into()),
		}
	}
}

/// This is only appropriate when writing out data of constant size that does not depend on user
/// input. In this case the costs for this copy was already charged as part of the token at
/// the beginning of the API entry point.
fn already_charged(_: u32) -> Option<RuntimeToken> {
	None
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

/// Can only be used for one call.
pub struct Runtime<'a, E: Ext + 'a> {
	ext: &'a mut E,
	input_data: Option<Vec<u8>>,
	schedule: &'a Schedule<E::T>,
	memory: sp_sandbox::Memory,
	gas_meter: &'a mut GasMeter<E::T>,
	trap_reason: Option<TrapReason>,
}

impl<'a, E> Runtime<'a, E>
where
	E: Ext + 'a,
	<E::T as frame_system::Config>::AccountId:
		UncheckedFrom<<E::T as frame_system::Config>::Hash> + AsRef<[u8]>
{
	pub fn new(
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

	/// Converts the sandbox result and the runtime state into the execution outcome.
	///
	/// It evaluates information stored in the `trap_reason` variable of the runtime and
	/// bases the outcome on the value if this variable. Only if `trap_reason` is `None`
	/// the result of the sandbox is evaluated.
	pub fn to_execution_result(
		self,
		sandbox_result: Result<sp_sandbox::ReturnValue, sp_sandbox::Error>,
	) -> ExecResult {
		// If a trap reason is set we base our decision solely on that.
		if let Some(trap_reason) = self.trap_reason {
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

	/// Get a mutable reference to the inner `Ext`.
	///
	/// This is mainly for the chain extension to have access to the environment the
	/// contract is executing in.
	pub fn ext(&mut self) -> &mut E {
		self.ext
	}

	/// Store the reason for a host function triggered trap.
	///
	/// This is called by the `define_env` macro in order to store any error returned by
	/// the host functions defined through the said macro. It should **not** be called
	/// manually.
	pub fn set_trap_reason(&mut self, reason: TrapReason) {
		self.trap_reason = Some(reason);
	}

	/// Charge the gas meter with the specified token.
	///
	/// Returns `Err(HostError)` if there is not enough gas.
	pub fn charge_gas<Tok>(&mut self, token: Tok) -> Result<ChargedAmount, DispatchError>
	where
		Tok: Token<E::T, Metadata=HostFnWeights<E::T>>,
	{
		match self.gas_meter.charge(&self.schedule.host_fn_weights, token) {
			GasMeterResult::Proceed(amount) => Ok(amount),
			GasMeterResult::OutOfGas => Err(Error::<E::T>::OutOfGas.into())
		}
	}

	/// Read designated chunk from the sandbox memory.
	///
	/// Returns `Err` if one of the following conditions occurs:
	///
	/// - requested buffer is not within the bounds of the sandbox memory.
	pub fn read_sandbox_memory(&self, ptr: u32, len: u32)
	-> Result<Vec<u8>, DispatchError>
	{
		ensure!(len <= self.schedule.limits.max_memory_size(), Error::<E::T>::OutOfBounds);
		let mut buf = vec![0u8; len as usize];
		self.memory.get(ptr, buf.as_mut_slice())
			.map_err(|_| Error::<E::T>::OutOfBounds)?;
		Ok(buf)
	}

	/// Read designated chunk from the sandbox memory into the supplied buffer.
	///
	/// Returns `Err` if one of the following conditions occurs:
	///
	/// - requested buffer is not within the bounds of the sandbox memory.
	pub fn read_sandbox_memory_into_buf(&self, ptr: u32, buf: &mut [u8])
	-> Result<(), DispatchError>
	{
		self.memory.get(ptr, buf).map_err(|_| Error::<E::T>::OutOfBounds.into())
	}

	/// Read designated chunk from the sandbox memory and attempt to decode into the specified type.
	///
	/// Returns `Err` if one of the following conditions occurs:
	///
	/// - requested buffer is not within the bounds of the sandbox memory.
	/// - the buffer contents cannot be decoded as the required type.
	///
	/// # Note
	///
	/// It is safe to forgo benchmarking and charging weight relative to `len` for fixed
	/// size types (basically everything not containing a heap collection):
	/// Despite the fact that we are usually about to read the encoding of a fixed size
	/// type, we cannot know the encoded size of that type. We therefore are required to
	/// use the length provided by the contract. This length is untrusted and therefore
	/// we charge weight relative to the provided size upfront that covers the copy costs.
	/// On success this cost is refunded as the copying was already covered in the
	/// overall cost of the host function. This is different from `read_sandbox_memory`
	/// where the size is dynamic and the costs resulting from that dynamic size must
	/// be charged relative to this dynamic size anyways (before reading) by constructing
	/// the benchmark for that.
	pub fn read_sandbox_memory_as<D: Decode>(&mut self, ptr: u32, len: u32)
	-> Result<D, DispatchError>
	{
		let amount = self.charge_gas(RuntimeToken::CopyIn(len))?;
		let buf = self.read_sandbox_memory(ptr, len)?;
		let decoded = D::decode_all(&mut &buf[..])
			.map_err(|_| DispatchError::from(Error::<E::T>::DecodingFailed))?;
		self.gas_meter.refund(amount);
		Ok(decoded)
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
	pub fn write_sandbox_output(
		&mut self,
		out_ptr: u32,
		out_len_ptr: u32,
		buf: &[u8],
		allow_skip: bool,
		create_token: impl FnOnce(u32) -> Option<RuntimeToken>,
	) -> Result<(), DispatchError>
	{
		if allow_skip && out_ptr == u32::max_value() {
			return Ok(());
		}

		let buf_len = buf.len() as u32;
		let len: u32 = self.read_sandbox_memory_as(out_len_ptr, 4)?;

		if len < buf_len {
			Err(Error::<E::T>::OutputBufferTooSmall)?
		}

		if let Some(token) = create_token(buf_len) {
			self.charge_gas(token)?;
		}

		self.memory.set(out_ptr, buf).and_then(|_| {
			self.memory.set(out_len_ptr, &buf_len.encode())
		})
		.map_err(|_| Error::<E::T>::OutOfBounds)?;

		Ok(())
	}

	/// Write the given buffer to the designated location in the sandbox memory.
	///
	/// Returns `Err` if one of the following conditions occurs:
	///
	/// - designated area is not within the bounds of the sandbox memory.
	fn write_sandbox_memory(&mut self, ptr: u32, buf: &[u8]) -> Result<(), DispatchError> {
		self.memory.set(ptr, buf).map_err(|_| Error::<E::T>::OutOfBounds.into())
	}

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
	fn compute_hash_on_intermediate_buffer<F, R>(
		&mut self,
		hash_fn: F,
		input_ptr: u32,
		input_len: u32,
		output_ptr: u32,
	) -> Result<(), DispatchError>
	where
		F: FnOnce(&[u8]) -> R,
		R: AsRef<[u8]>,
	{
		// Copy input into supervisor memory.
		let input = self.read_sandbox_memory(input_ptr, input_len)?;
		// Compute the hash on the input buffer using the given hash function.
		let hash = hash_fn(&input);
		// Write the resulting hash back into the sandboxed output buffer.
		self.write_sandbox_memory(output_ptr, hash.as_ref())?;
		Ok(())
	}

	/// Fallible conversion of `DispatchError` to `ReturnCode`.
	fn err_into_return_code(from: DispatchError) -> Result<ReturnCode, DispatchError> {
		use ReturnCode::*;

		let below_sub = Error::<E::T>::BelowSubsistenceThreshold.into();
		let transfer_failed = Error::<E::T>::TransferFailed.into();
		let not_funded = Error::<E::T>::NewContractNotFunded.into();
		let no_code = Error::<E::T>::CodeNotFound.into();
		let invalid_contract = Error::<E::T>::NotCallable.into();

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
	fn exec_into_return_code(from: ExecResult) -> Result<ReturnCode, DispatchError> {
		use pallet_contracts_primitives::ErrorOrigin::Callee;

		let ExecError { error, origin } = match from {
			Ok(retval) => return Ok(retval.into()),
			Err(err) => err,
		};

		match (error, origin) {
			(_, Callee) => Ok(ReturnCode::CalleeTrapped),
			(err, _) => Self::err_into_return_code(err)
		}
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
		ctx.charge_gas(RuntimeToken::MeteringBlock(amount))?;
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
		ctx.charge_gas(RuntimeToken::SetStorage(value_len))?;
		if value_len > ctx.ext.max_value_size() {
			Err(Error::<E::T>::ValueTooLarge)?;
		}
		let mut key: StorageKey = [0; 32];
		ctx.read_sandbox_memory_into_buf(key_ptr, &mut key)?;
		let value = Some(ctx.read_sandbox_memory(value_ptr, value_len)?);
		ctx.ext.set_storage(key, value).map_err(Into::into)
	},

	// Clear the value at the given key in the contract storage.
	//
	// # Parameters
	//
	// - `key_ptr`: pointer into the linear memory where the location to clear the value is placed.
	seal_clear_storage(ctx, key_ptr: u32) => {
		ctx.charge_gas(RuntimeToken::ClearStorage)?;
		let mut key: StorageKey = [0; 32];
		ctx.read_sandbox_memory_into_buf(key_ptr, &mut key)?;
		ctx.ext.set_storage(key, None).map_err(Into::into)
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
		ctx.charge_gas(RuntimeToken::GetStorageBase)?;
		let mut key: StorageKey = [0; 32];
		ctx.read_sandbox_memory_into_buf(key_ptr, &mut key)?;
		if let Some(value) = ctx.ext.get_storage(&key) {
			ctx.write_sandbox_output(out_ptr, out_len_ptr, &value, false, |len| {
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
		ctx.charge_gas(RuntimeToken::Transfer)?;
		let callee: <<E as Ext>::T as frame_system::Config>::AccountId =
			ctx.read_sandbox_memory_as(account_ptr, account_len)?;
		let value: BalanceOf<<E as Ext>::T> =
			ctx.read_sandbox_memory_as(value_ptr, value_len)?;

		let result = ctx.ext.transfer(&callee, value);
		match result {
			Ok(()) => Ok(ReturnCode::Success),
			Err(err) => {
				let code = Runtime::<E>::err_into_return_code(err)?;
				Ok(code)
			}
		}
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
		ctx.charge_gas(RuntimeToken::CallBase(input_data_len))?;
		let callee: <<E as Ext>::T as frame_system::Config>::AccountId =
			ctx.read_sandbox_memory_as(callee_ptr, callee_len)?;
		let value: BalanceOf<<E as Ext>::T> = ctx.read_sandbox_memory_as(value_ptr, value_len)?;
		let input_data = ctx.read_sandbox_memory(input_data_ptr, input_data_len)?;

		if value > 0u32.into() {
			ctx.charge_gas(RuntimeToken::CallSurchargeTransfer)?;
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
			ctx.write_sandbox_output(output_ptr, output_len_ptr, &output.data, true, |len| {
				Some(RuntimeToken::CallCopyOut(len))
			})?;
		}
		Ok(Runtime::<E>::exec_into_return_code(call_outcome)?)
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
	// - salt_ptr: Pointer to raw bytes used for address deriviation. See `fn contract_address`.
	// - salt_len: length in bytes of the supplied salt.
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
		output_len_ptr: u32,
		salt_ptr: u32,
		salt_len: u32
	) -> ReturnCode => {
		ctx.charge_gas(RuntimeToken::InstantiateBase {input_data_len, salt_len})?;
		let code_hash: CodeHash<<E as Ext>::T> =
			ctx.read_sandbox_memory_as(code_hash_ptr, code_hash_len)?;
		let value: BalanceOf<<E as Ext>::T> = ctx.read_sandbox_memory_as(value_ptr, value_len)?;
		let input_data = ctx.read_sandbox_memory(input_data_ptr, input_data_len)?;
		let salt = ctx.read_sandbox_memory(salt_ptr, salt_len)?;

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
						input_data,
						&salt,
					)
				}
				// there is not enough gas to allocate for the nested call.
				None => Err(Error::<<E as Ext>::T>::OutOfGas.into()),
			}
		});
		if let Ok((address, output)) = &instantiate_outcome {
			if !output.flags.contains(ReturnFlags::REVERT) {
				ctx.write_sandbox_output(
					address_ptr, address_len_ptr, &address.encode(), true, already_charged,
				)?;
			}
			ctx.write_sandbox_output(output_ptr, output_len_ptr, &output.data, true, |len| {
				Some(RuntimeToken::InstantiateCopyOut(len))
			})?;
		}
		Ok(Runtime::<E>::exec_into_return_code(instantiate_outcome.map(|(_id, retval)| retval))?)
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
	// - Failed to send the balance to the beneficiary.
	// - The deletion queue is full.
	seal_terminate(
		ctx,
		beneficiary_ptr: u32,
		beneficiary_len: u32
	) => {
		ctx.charge_gas(RuntimeToken::Terminate)?;
		let beneficiary: <<E as Ext>::T as frame_system::Config>::AccountId =
			ctx.read_sandbox_memory_as(beneficiary_ptr, beneficiary_len)?;

		ctx.ext.terminate(&beneficiary)?;
		Err(TrapReason::Termination)
	},

	seal_input(ctx, buf_ptr: u32, buf_len_ptr: u32) => {
		ctx.charge_gas(RuntimeToken::InputBase)?;
		if let Some(input) = ctx.input_data.take() {
			ctx.write_sandbox_output(buf_ptr, buf_len_ptr, &input, false, |len| {
				Some(RuntimeToken::InputCopyOut(len))
			})?;
			Ok(())
		} else {
			Err(Error::<E::T>::InputAlreadyRead.into())
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
		ctx.charge_gas(RuntimeToken::Return(data_len))?;
		Err(TrapReason::Return(ReturnData {
			flags,
			data: ctx.read_sandbox_memory(data_ptr, data_len)?,
		}))
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
		ctx.charge_gas(RuntimeToken::Caller)?;
		Ok(ctx.write_sandbox_output(
			out_ptr, out_len_ptr, &ctx.ext.caller().encode(), false, already_charged
		)?)
	},

	// Stores the address of the current contract into the supplied buffer.
	//
	// The value is stored to linear memory at the address pointed to by `out_ptr`.
	// `out_len_ptr` must point to a u32 value that describes the available space at
	// `out_ptr`. This call overwrites it with the size of the value. If the available
	// space at `out_ptr` is less than the size of the value a trap is triggered.
	seal_address(ctx, out_ptr: u32, out_len_ptr: u32) => {
		ctx.charge_gas(RuntimeToken::Address)?;
		Ok(ctx.write_sandbox_output(
			out_ptr, out_len_ptr, &ctx.ext.address().encode(), false, already_charged
		)?)
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
		ctx.charge_gas(RuntimeToken::WeightToFee)?;
		Ok(ctx.write_sandbox_output(
			out_ptr, out_len_ptr, &ctx.ext.get_weight_price(gas).encode(), false, already_charged
		)?)
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
		ctx.charge_gas(RuntimeToken::GasLeft)?;
		Ok(ctx.write_sandbox_output(
			out_ptr, out_len_ptr, &ctx.gas_meter.gas_left().encode(), false, already_charged
		)?)
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
		ctx.charge_gas(RuntimeToken::Balance)?;
		Ok(ctx.write_sandbox_output(
			out_ptr, out_len_ptr, &ctx.ext.balance().encode(), false, already_charged
		)?)
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
		ctx.charge_gas(RuntimeToken::ValueTransferred)?;
		Ok(ctx.write_sandbox_output(
			out_ptr, out_len_ptr, &ctx.ext.value_transferred().encode(), false, already_charged
		)?)
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
		ctx.charge_gas(RuntimeToken::Random)?;
		if subject_len > ctx.schedule.limits.subject_len {
			Err(Error::<E::T>::RandomSubjectTooLong)?;
		}
		let subject_buf = ctx.read_sandbox_memory(subject_ptr, subject_len)?;
		Ok(ctx.write_sandbox_output(
			out_ptr, out_len_ptr, &ctx.ext.random(&subject_buf).encode(), false, already_charged
		)?)
	},

	// Load the latest block timestamp into the supplied buffer
	//
	// The value is stored to linear memory at the address pointed to by `out_ptr`.
	// `out_len_ptr` must point to a u32 value that describes the available space at
	// `out_ptr`. This call overwrites it with the size of the value. If the available
	// space at `out_ptr` is less than the size of the value a trap is triggered.
	seal_now(ctx, out_ptr: u32, out_len_ptr: u32) => {
		ctx.charge_gas(RuntimeToken::Now)?;
		Ok(ctx.write_sandbox_output(
			out_ptr, out_len_ptr, &ctx.ext.now().encode(), false, already_charged
		)?)
	},

	// Stores the minimum balance (a.k.a. existential deposit) into the supplied buffer.
	//
	// The data is encoded as T::Balance.
	seal_minimum_balance(ctx, out_ptr: u32, out_len_ptr: u32) => {
		ctx.charge_gas(RuntimeToken::MinimumBalance)?;
		Ok(ctx.write_sandbox_output(
			out_ptr, out_len_ptr, &ctx.ext.minimum_balance().encode(), false, already_charged
		)?)
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
		ctx.charge_gas(RuntimeToken::TombstoneDeposit)?;
		Ok(ctx.write_sandbox_output(
			out_ptr, out_len_ptr, &ctx.ext.tombstone_deposit().encode(), false, already_charged
		)?)
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
		ctx.charge_gas(RuntimeToken::RestoreTo(delta_count))?;
		let dest: <<E as Ext>::T as frame_system::Config>::AccountId =
			ctx.read_sandbox_memory_as(dest_ptr, dest_len)?;
		let code_hash: CodeHash<<E as Ext>::T> =
			ctx.read_sandbox_memory_as(code_hash_ptr, code_hash_len)?;
		let rent_allowance: BalanceOf<<E as Ext>::T> =
			ctx.read_sandbox_memory_as(rent_allowance_ptr, rent_allowance_len)?;
		let delta = {
			const KEY_SIZE: usize = 32;

			// We can eagerly allocate because we charged for the complete delta count already
			// We still need to make sure that the allocation isn't larger than the memory
			// allocator can handle.
			ensure!(
				delta_count
					.saturating_mul(KEY_SIZE as u32) <= ctx.schedule.limits.max_memory_size(),
				Error::<E::T>::OutOfBounds,
			);
			let mut delta = vec![[0; KEY_SIZE]; delta_count as usize];
			let mut key_ptr = delta_ptr;

			for i in 0..delta_count {
				// Read the delta into the provided buffer
				// This cannot panic because of the loop condition
				ctx.read_sandbox_memory_into_buf(key_ptr, &mut delta[i as usize])?;

				// Offset key_ptr to the next element.
				key_ptr = key_ptr.checked_add(KEY_SIZE as u32).ok_or(Error::<E::T>::OutOfBounds)?;
			}

			delta
		};

		ctx.ext.restore_to(dest, code_hash, rent_allowance, delta)?;
		Err(TrapReason::Restoration)
	},

	// Deposit a contract event with the data buffer and optional list of topics. There is a limit
	// on the maximum number of topics specified by `event_topics`.
	//
	// - topics_ptr - a pointer to the buffer of topics encoded as `Vec<T::Hash>`. The value of this
	//   is ignored if `topics_len` is set to 0. The topics list can't contain duplicates.
	// - topics_len - the length of the topics buffer. Pass 0 if you want to pass an empty vector.
	// - data_ptr - a pointer to a raw data buffer which will saved along the event.
	// - data_len - the length of the data buffer.
	seal_deposit_event(ctx, topics_ptr: u32, topics_len: u32, data_ptr: u32, data_len: u32) => {
		let num_topic = topics_len
			.checked_div(sp_std::mem::size_of::<TopicOf<E::T>>() as u32)
			.ok_or_else(|| "Zero sized topics are not allowed")?;
		ctx.charge_gas(RuntimeToken::DepositEvent {
			num_topic,
			len: data_len,
		})?;
		if data_len > ctx.ext.max_value_size() {
			Err(Error::<E::T>::ValueTooLarge)?;
		}

		let mut topics: Vec::<TopicOf<<E as Ext>::T>> = match topics_len {
			0 => Vec::new(),
			_ => ctx.read_sandbox_memory_as(topics_ptr, topics_len)?,
		};

		// If there are more than `event_topics`, then trap.
		if topics.len() > ctx.schedule.limits.event_topics as usize {
			Err(Error::<E::T>::TooManyTopics)?;
		}

		// Check for duplicate topics. If there are any, then trap.
		if has_duplicates(&mut topics) {
			Err(Error::<E::T>::DuplicateTopics)?;
		}

		let event_data = ctx.read_sandbox_memory(data_ptr, data_len)?;

		ctx.ext.deposit_event(topics, event_data);

		Ok(())
	},

	// Set rent allowance of the contract
	//
	// - value_ptr: a pointer to the buffer with value, how much to allow for rent
	//   Should be decodable as a `T::Balance`. Traps otherwise.
	// - value_len: length of the value buffer.
	seal_set_rent_allowance(ctx, value_ptr: u32, value_len: u32) => {
		ctx.charge_gas(RuntimeToken::SetRentAllowance)?;
		let value: BalanceOf<<E as Ext>::T> =
			ctx.read_sandbox_memory_as(value_ptr, value_len)?;
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
		ctx.charge_gas(RuntimeToken::RentAllowance)?;
		Ok(ctx.write_sandbox_output(
			out_ptr, out_len_ptr, &ctx.ext.rent_allowance().encode(), false, already_charged
		)?)
	},

	// Prints utf8 encoded string from the data buffer.
	// Only available on `--dev` chains.
	// This function may be removed at any time, superseded by a more general contract debugging feature.
	seal_println(ctx, str_ptr: u32, str_len: u32) => {
		let data = ctx.read_sandbox_memory(str_ptr, str_len)?;
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
		ctx.charge_gas(RuntimeToken::BlockNumber)?;
		Ok(ctx.write_sandbox_output(
			out_ptr, out_len_ptr, &ctx.ext.block_number().encode(), false, already_charged
		)?)
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
		ctx.charge_gas(RuntimeToken::HashSha256(input_len))?;
		Ok(ctx.compute_hash_on_intermediate_buffer(sha2_256, input_ptr, input_len, output_ptr)?)
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
		ctx.charge_gas(RuntimeToken::HashKeccak256(input_len))?;
		Ok(ctx.compute_hash_on_intermediate_buffer(keccak_256, input_ptr, input_len, output_ptr)?)
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
		ctx.charge_gas(RuntimeToken::HashBlake256(input_len))?;
		Ok(ctx.compute_hash_on_intermediate_buffer(blake2_256, input_ptr, input_len, output_ptr)?)
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
		ctx.charge_gas(RuntimeToken::HashBlake128(input_len))?;
		Ok(ctx.compute_hash_on_intermediate_buffer(blake2_128, input_ptr, input_len, output_ptr)?)
	},

	// Call into the chain extension provided by the chain if any.
	//
	// Handling of the input values is up to the specific chain extension and so is the
	// return value. The extension can decide to use the inputs as primitive inputs or as
	// in/out arguments by interpreting them as pointers. Any caller of this function
	// must therefore coordinate with the chain that it targets.
	//
	// # Note
	//
	// If no chain extension exists the contract will trap with the `NoChainExtension`
	// module error.
	seal_call_chain_extension(
		ctx,
		func_id: u32,
		input_ptr: u32,
		input_len: u32,
		output_ptr: u32,
		output_len_ptr: u32
	) -> u32 => {
		use crate::chain_extension::{ChainExtension, Environment, RetVal};
		if <E::T as Config>::ChainExtension::enabled() == false {
			Err(Error::<E::T>::NoChainExtension)?;
		}
		let env = Environment::new(ctx, input_ptr, input_len, output_ptr, output_len_ptr);
		match <E::T as Config>::ChainExtension::call(func_id, env)? {
			RetVal::Converging(val) => Ok(val),
			RetVal::Diverging{flags, data} => Err(TrapReason::Return(ReturnData {
				flags: flags.bits(),
				data,
			})),
		}
	},
);
