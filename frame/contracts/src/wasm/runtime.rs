// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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
	exec::{ExecError, ExecResult, Ext, FixSizedKey, TopicOf, VarSizedKey},
	gas::{ChargedAmount, Token},
	schedule::HostFnWeights,
	wasm::env_def::ConvertibleToWasm,
	BalanceOf, CodeHash, Config, Error, SENTINEL,
};

use bitflags::bitflags;
use codec::{Decode, DecodeLimit, Encode, MaxEncodedLen};
use frame_support::{dispatch::DispatchError, ensure, traits::Get, weights::Weight};
use pallet_contracts_primitives::{ExecReturnValue, ReturnFlags};
use pallet_contracts_proc_macro::define_env;
use sp_core::crypto::UncheckedFrom;
use sp_io::hashing::{blake2_128, blake2_256, keccak_256, sha2_256};
use sp_runtime::traits::{Bounded, Zero};
use sp_sandbox::SandboxMemory;
use sp_std::prelude::*;
use wasm_instrument::parity_wasm::elements::ValueType;

/// The maximum nesting depth a contract can use when encoding types.
const MAX_DECODE_NESTING: u32 = 256;

/// Type of a storage key.
#[allow(dead_code)]
enum KeyType {
	/// Deprecated fix sized key [0;32].
	Fix,
	/// Variable sized key used in transparent hashing,
	/// cannot be larger than MaxStorageKeyLen.
	Variable(u32),
}

impl KeyType {
	fn len<T: Config>(&self) -> Result<u32, TrapReason> {
		match self {
			KeyType::Fix => Ok(32u32),
			KeyType::Variable(len) => {
				ensure!(len <= &<T>::MaxStorageKeyLen::get(), Error::<T>::DecodingFailed);
				Ok(*len)
			},
		}
	}
}

/// Every error that can be returned to a contract when it calls any of the host functions.
///
/// # Note
///
/// This enum can be extended in the future: New codes can be added but existing codes
/// will not be changed or removed. This means that any contract **must not** exhaustively
/// match return codes. Instead, contracts should prepare for unknown variants and deal with
/// those errors gracefully in order to be forward compatible.
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
	/// Deprecated and no longer returned: There is only the minimum balance.
	_BelowSubsistenceThreshold = 4,
	/// See [`Error::TransferFailed`].
	TransferFailed = 5,
	/// Deprecated and no longer returned: Endowment is no longer required.
	_EndowmentTooLow = 6,
	/// No code could be found at the supplied code hash.
	CodeNotFound = 7,
	/// The contract that was called is no contract (a plain account).
	NotCallable = 8,
	/// The call to `seal_debug_message` had no effect because debug message
	/// recording was disabled.
	LoggingDisabled = 9,
	/// The call dispatched by `seal_call_runtime` was executed but returned an error.
	#[cfg(feature = "unstable-interface")]
	CallRuntimeReturnedError = 10,
	/// ECDSA pubkey recovery failed (most probably wrong recovery id or signature), or
	/// ECDSA compressed pubkey conversion into Ethereum address failed (most probably
	/// wrong pubkey provided).
	EcdsaRecoverFailed = 11,
}

impl ConvertibleToWasm for ReturnCode {
	const VALUE_TYPE: ValueType = ValueType::I32;
	type NativeType = Self;

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
}

impl<T: Into<DispatchError>> From<T> for TrapReason {
	fn from(from: T) -> Self {
		Self::SupervisorError(from.into())
	}
}

#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
#[derive(Copy, Clone)]
pub enum RuntimeCosts {
	/// Charge the gas meter with the cost of a metering block. The charged costs are
	/// the supplied cost of the block plus the overhead of the metering itself.
	MeteringBlock(u64),
	/// Weight charged for copying data from the sandbox.
	CopyFromContract(u32),
	/// Weight charged for copying data to the sandbox.
	CopyToContract(u32),
	/// Weight of calling `seal_caller`.
	Caller,
	/// Weight of calling `seal_is_contract`.
	IsContract,
	/// Weight of calling `seal_code_hash`.
	CodeHash,
	/// Weight of calling `seal_own_code_hash`.
	OwnCodeHash,
	/// Weight of calling `seal_caller_is_origin`.
	CallerIsOrigin,
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
	/// Weight of calling `seal_block_number`.
	BlockNumber,
	/// Weight of calling `seal_now`.
	Now,
	/// Weight of calling `seal_weight_to_fee`.
	WeightToFee,
	/// Weight of calling `seal_input` without the weight of copying the input.
	InputBase,
	/// Weight of calling `seal_return` for the given output size.
	Return(u32),
	/// Weight of calling `seal_terminate`.
	Terminate,
	/// Weight of calling `seal_random`. It includes the weight for copying the subject.
	Random,
	/// Weight of calling `seal_deposit_event` with the given number of topics and event size.
	DepositEvent { num_topic: u32, len: u32 },
	/// Weight of calling `seal_debug_message`.
	DebugMessage,
	/// Weight of calling `seal_set_storage` for the given storage item sizes.
	SetStorage { old_bytes: u32, new_bytes: u32 },
	/// Weight of calling `seal_clear_storage` per cleared byte.
	ClearStorage(u32),
	/// Weight of calling `seal_contains_storage` per byte of the checked item.
	ContainsStorage(u32),
	/// Weight of calling `seal_get_storage` with the specified size in storage.
	GetStorage(u32),
	/// Weight of calling `seal_take_storage` for the given size.
	#[cfg(feature = "unstable-interface")]
	TakeStorage(u32),
	/// Weight of calling `seal_transfer`.
	Transfer,
	/// Base weight of calling `seal_call`.
	CallBase,
	/// Weight of calling `seal_delegate_call` for the given input size.
	DelegateCallBase,
	/// Weight of the transfer performed during a call.
	CallSurchargeTransfer,
	/// Weight per byte that is cloned by supplying the `CLONE_INPUT` flag.
	CallInputCloned(u32),
	/// Weight of calling `seal_instantiate` for the given input length and salt.
	InstantiateBase { input_data_len: u32, salt_len: u32 },
	/// Weight of the transfer performed during an instantiate.
	InstantiateSurchargeTransfer,
	/// Weight of calling `seal_hash_sha_256` for the given input size.
	HashSha256(u32),
	/// Weight of calling `seal_hash_keccak_256` for the given input size.
	HashKeccak256(u32),
	/// Weight of calling `seal_hash_blake2_256` for the given input size.
	HashBlake256(u32),
	/// Weight of calling `seal_hash_blake2_128` for the given input size.
	HashBlake128(u32),
	/// Weight of calling `seal_ecdsa_recover`.
	EcdsaRecovery,
	/// Weight charged by a chain extension through `seal_call_chain_extension`.
	ChainExtension(u64),
	/// Weight charged for calling into the runtime.
	#[cfg(feature = "unstable-interface")]
	CallRuntime(Weight),
	/// Weight of calling `seal_set_code_hash`
	SetCodeHash,
	/// Weight of calling `ecdsa_to_eth_address`
	EcdsaToEthAddress,
}

impl RuntimeCosts {
	fn token<T>(&self, s: &HostFnWeights<T>) -> RuntimeToken
	where
		T: Config,
		T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
	{
		use self::RuntimeCosts::*;
		let weight = match *self {
			MeteringBlock(amount) => s.gas.saturating_add(amount),
			CopyFromContract(len) => s.return_per_byte.saturating_mul(len.into()),
			CopyToContract(len) => s.input_per_byte.saturating_mul(len.into()),
			Caller => s.caller,
			IsContract => s.is_contract,
			CodeHash => s.code_hash,
			OwnCodeHash => s.own_code_hash,
			CallerIsOrigin => s.caller_is_origin,
			Address => s.address,
			GasLeft => s.gas_left,
			Balance => s.balance,
			ValueTransferred => s.value_transferred,
			MinimumBalance => s.minimum_balance,
			BlockNumber => s.block_number,
			Now => s.now,
			WeightToFee => s.weight_to_fee,
			InputBase => s.input,
			Return(len) => s.r#return.saturating_add(s.return_per_byte.saturating_mul(len.into())),
			Terminate => s.terminate,
			Random => s.random,
			DepositEvent { num_topic, len } => s
				.deposit_event
				.saturating_add(s.deposit_event_per_topic.saturating_mul(num_topic.into()))
				.saturating_add(s.deposit_event_per_byte.saturating_mul(len.into())),
			DebugMessage => s.debug_message,
			SetStorage { new_bytes, old_bytes } => s
				.set_storage
				.saturating_add(s.set_storage_per_new_byte.saturating_mul(new_bytes.into()))
				.saturating_add(s.set_storage_per_old_byte.saturating_mul(old_bytes.into())),
			ClearStorage(len) => s
				.clear_storage
				.saturating_add(s.clear_storage_per_byte.saturating_mul(len.into())),
			ContainsStorage(len) => s
				.contains_storage
				.saturating_add(s.contains_storage_per_byte.saturating_mul(len.into())),
			GetStorage(len) =>
				s.get_storage.saturating_add(s.get_storage_per_byte.saturating_mul(len.into())),
			#[cfg(feature = "unstable-interface")]
			TakeStorage(len) => s
				.take_storage
				.saturating_add(s.take_storage_per_byte.saturating_mul(len.into())),
			Transfer => s.transfer,
			CallBase => s.call,
			DelegateCallBase => s.delegate_call,
			CallSurchargeTransfer => s.call_transfer_surcharge,
			CallInputCloned(len) => s.call_per_cloned_byte.saturating_mul(len.into()),
			InstantiateBase { input_data_len, salt_len } => s
				.instantiate
				.saturating_add(s.return_per_byte.saturating_mul(input_data_len.into()))
				.saturating_add(s.instantiate_per_salt_byte.saturating_mul(salt_len.into())),
			InstantiateSurchargeTransfer => s.instantiate_transfer_surcharge,
			HashSha256(len) => s
				.hash_sha2_256
				.saturating_add(s.hash_sha2_256_per_byte.saturating_mul(len.into())),
			HashKeccak256(len) => s
				.hash_keccak_256
				.saturating_add(s.hash_keccak_256_per_byte.saturating_mul(len.into())),
			HashBlake256(len) => s
				.hash_blake2_256
				.saturating_add(s.hash_blake2_256_per_byte.saturating_mul(len.into())),
			HashBlake128(len) => s
				.hash_blake2_128
				.saturating_add(s.hash_blake2_128_per_byte.saturating_mul(len.into())),
			EcdsaRecovery => s.ecdsa_recover,
			ChainExtension(amount) => amount,
			#[cfg(feature = "unstable-interface")]
			CallRuntime(weight) => weight.ref_time(),
			SetCodeHash => s.set_code_hash,
			EcdsaToEthAddress => s.ecdsa_to_eth_address,
		};
		RuntimeToken {
			#[cfg(test)]
			_created_from: *self,
			weight: Weight::from_ref_time(weight),
		}
	}
}

/// Same as [`Runtime::charge_gas`].
///
/// We need this access as a macro because sometimes hiding the lifetimes behind
/// a function won't work out.
macro_rules! charge_gas {
	($runtime:expr, $costs:expr) => {{
		let token = $costs.token(&$runtime.ext.schedule().host_fn_weights);
		$runtime.ext.gas_meter().charge(token)
	}};
}

#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
#[derive(Copy, Clone)]
struct RuntimeToken {
	#[cfg(test)]
	_created_from: RuntimeCosts,
	weight: Weight,
}

impl<T> Token<T> for RuntimeToken
where
	T: Config,
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
{
	fn weight(&self) -> Weight {
		self.weight
	}
}

bitflags! {
	/// Flags used to change the behaviour of `seal_call` and `seal_delegate_call`.
	pub struct CallFlags: u32 {
		/// Forward the input of current function to the callee.
		///
		/// Supplied input pointers are ignored when set.
		///
		/// # Note
		///
		/// A forwarding call will consume the current contracts input. Any attempt to
		/// access the input after this call returns will lead to [`Error::InputForwarded`].
		/// It does not matter if this is due to calling `seal_input` or trying another
		/// forwarding call. Consider using [`Self::CLONE_INPUT`] in order to preserve
		/// the input.
		const FORWARD_INPUT = 0b0000_0001;
		/// Identical to [`Self::FORWARD_INPUT`] but without consuming the input.
		///
		/// This adds some additional weight costs to the call.
		///
		/// # Note
		///
		/// This implies [`Self::FORWARD_INPUT`] and takes precedence when both are set.
		const CLONE_INPUT = 0b0000_0010;
		/// Do not return from the call but rather return the result of the callee to the
		/// callers caller.
		///
		/// # Note
		///
		/// This makes the current contract completely transparent to its caller by replacing
		/// this contracts potential output by the callee ones. Any code after `seal_call`
		/// can be safely considered unreachable.
		const TAIL_CALL = 0b0000_0100;
		/// Allow the callee to reenter into the current contract.
		///
		/// Without this flag any reentrancy into the current contract that originates from
		/// the callee (or any of its callees) is denied. This includes the first callee:
		/// You cannot call into yourself with this flag set.
		///
		/// # Note
		///
		/// For `seal_delegate_call` should be always unset, otherwise
		/// [`Error::InvalidCallFlags`] is returned.
		const ALLOW_REENTRY = 0b0000_1000;
	}
}

/// The kind of call that should be performed.
enum CallType {
	/// Execute another instantiated contract
	Call { callee_ptr: u32, value_ptr: u32, gas: u64 },
	/// Execute deployed code in the context (storage, account ID, value) of the caller contract
	DelegateCall { code_hash_ptr: u32 },
}

impl CallType {
	fn cost(&self) -> RuntimeCosts {
		match self {
			CallType::Call { .. } => RuntimeCosts::CallBase,
			CallType::DelegateCall { .. } => RuntimeCosts::DelegateCallBase,
		}
	}
}

/// This is only appropriate when writing out data of constant size that does not depend on user
/// input. In this case the costs for this copy was already charged as part of the token at
/// the beginning of the API entry point.
fn already_charged(_: u32) -> Option<RuntimeCosts> {
	None
}

/// Can only be used for one call.
pub struct Runtime<'a, E: Ext + 'a> {
	ext: &'a mut E,
	input_data: Option<Vec<u8>>,
	memory: sp_sandbox::default_executor::Memory,
	trap_reason: Option<TrapReason>,
	chain_extension: Option<Box<<E::T as Config>::ChainExtension>>,
}

impl<'a, E> Runtime<'a, E>
where
	E: Ext + 'a,
	<E::T as frame_system::Config>::AccountId:
		UncheckedFrom<<E::T as frame_system::Config>::Hash> + AsRef<[u8]>,
{
	pub fn new(
		ext: &'a mut E,
		input_data: Vec<u8>,
		memory: sp_sandbox::default_executor::Memory,
	) -> Self {
		Runtime {
			ext,
			input_data: Some(input_data),
			memory,
			trap_reason: None,
			chain_extension: Some(Box::new(Default::default())),
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
				TrapReason::Return(ReturnData { flags, data }) => {
					let flags =
						ReturnFlags::from_bits(flags).ok_or(Error::<E::T>::InvalidCallFlags)?;
					Ok(ExecReturnValue { flags, data })
				},
				TrapReason::Termination =>
					Ok(ExecReturnValue { flags: ReturnFlags::empty(), data: Vec::new() }),
				TrapReason::SupervisorError(error) => return Err(error.into()),
			}
		}

		// Check the exact type of the error.
		match sandbox_result {
			// No traps were generated. Proceed normally.
			Ok(_) => Ok(ExecReturnValue { flags: ReturnFlags::empty(), data: Vec::new() }),
			// `Error::Module` is returned only if instantiation or linking failed (i.e.
			// wasm binary tried to import a function that is not provided by the host).
			// This shouldn't happen because validation process ought to reject such binaries.
			//
			// Because panics are really undesirable in the runtime code, we treat this as
			// a trap for now. Eventually, we might want to revisit this.
			Err(sp_sandbox::Error::Module) => return Err("validation error".into()),
			// Any other kind of a trap should result in a failure.
			Err(sp_sandbox::Error::Execution) | Err(sp_sandbox::Error::OutOfBounds) =>
				return Err(Error::<E::T>::ContractTrapped.into()),
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
	pub fn charge_gas(&mut self, costs: RuntimeCosts) -> Result<ChargedAmount, DispatchError> {
		charge_gas!(self, costs)
	}

	/// Adjust a previously charged amount down to its actual amount.
	///
	/// This is when a maximum a priori amount was charged and then should be partially
	/// refunded to match the actual amount.
	pub fn adjust_gas(&mut self, charged: ChargedAmount, actual_costs: RuntimeCosts) {
		let token = actual_costs.token(&self.ext.schedule().host_fn_weights);
		self.ext.gas_meter().adjust_gas(charged, token);
	}

	/// Read designated chunk from the sandbox memory.
	///
	/// Returns `Err` if one of the following conditions occurs:
	///
	/// - requested buffer is not within the bounds of the sandbox memory.
	pub fn read_sandbox_memory(&self, ptr: u32, len: u32) -> Result<Vec<u8>, DispatchError> {
		ensure!(len <= self.ext.schedule().limits.max_memory_size(), Error::<E::T>::OutOfBounds);
		let mut buf = vec![0u8; len as usize];
		self.memory
			.get(ptr, buf.as_mut_slice())
			.map_err(|_| Error::<E::T>::OutOfBounds)?;
		Ok(buf)
	}

	/// Read designated chunk from the sandbox memory into the supplied buffer.
	///
	/// Returns `Err` if one of the following conditions occurs:
	///
	/// - requested buffer is not within the bounds of the sandbox memory.
	pub fn read_sandbox_memory_into_buf(
		&self,
		ptr: u32,
		buf: &mut [u8],
	) -> Result<(), DispatchError> {
		self.memory.get(ptr, buf).map_err(|_| Error::<E::T>::OutOfBounds.into())
	}

	/// Reads and decodes a type with a size fixed at compile time from contract memory.
	///
	/// # Note
	///
	/// The weight of reading a fixed value is included in the overall weight of any
	/// contract callable function.
	pub fn read_sandbox_memory_as<D: Decode + MaxEncodedLen>(
		&self,
		ptr: u32,
	) -> Result<D, DispatchError> {
		let buf = self.read_sandbox_memory(ptr, D::max_encoded_len() as u32)?;
		let decoded = D::decode_all_with_depth_limit(MAX_DECODE_NESTING, &mut &buf[..])
			.map_err(|_| DispatchError::from(Error::<E::T>::DecodingFailed))?;
		Ok(decoded)
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
	/// There must be an extra benchmark for determining the influence of `len` with
	/// regard to the overall weight.
	pub fn read_sandbox_memory_as_unbounded<D: Decode>(
		&self,
		ptr: u32,
		len: u32,
	) -> Result<D, DispatchError> {
		let buf = self.read_sandbox_memory(ptr, len)?;
		let decoded = D::decode_all_with_depth_limit(MAX_DECODE_NESTING, &mut &buf[..])
			.map_err(|_| DispatchError::from(Error::<E::T>::DecodingFailed))?;
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
	/// If `out_ptr` is set to the sentinel value of `SENTINEL` and `allow_skip` is true the
	/// operation is skipped and `Ok` is returned. This is supposed to help callers to make copying
	/// output optional. For example to skip copying back the output buffer of an `seal_call`
	/// when the caller is not interested in the result.
	///
	/// `create_token` can optionally instruct this function to charge the gas meter with the token
	/// it returns. `create_token` receives the variable amount of bytes that are about to be copied
	/// by this function.
	///
	/// In addition to the error conditions of `write_sandbox_memory` this functions returns
	/// `Err` if the size of the buffer located at `out_ptr` is too small to fit `buf`.
	pub fn write_sandbox_output(
		&mut self,
		out_ptr: u32,
		out_len_ptr: u32,
		buf: &[u8],
		allow_skip: bool,
		create_token: impl FnOnce(u32) -> Option<RuntimeCosts>,
	) -> Result<(), DispatchError> {
		if allow_skip && out_ptr == SENTINEL {
			return Ok(())
		}

		let buf_len = buf.len() as u32;
		let len: u32 = self.read_sandbox_memory_as(out_len_ptr)?;

		if len < buf_len {
			return Err(Error::<E::T>::OutputBufferTooSmall.into())
		}

		if let Some(costs) = create_token(buf_len) {
			self.charge_gas(costs)?;
		}

		self.memory
			.set(out_ptr, buf)
			.and_then(|_| self.memory.set(out_len_ptr, &buf_len.encode()))
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

		let transfer_failed = Error::<E::T>::TransferFailed.into();
		let no_code = Error::<E::T>::CodeNotFound.into();
		let not_found = Error::<E::T>::ContractNotFound.into();

		match from {
			x if x == transfer_failed => Ok(TransferFailed),
			x if x == no_code => Ok(CodeNotFound),
			x if x == not_found => Ok(NotCallable),
			err => Err(err),
		}
	}

	/// Fallible conversion of a `ExecResult` to `ReturnCode`.
	fn exec_into_return_code(from: ExecResult) -> Result<ReturnCode, DispatchError> {
		use crate::exec::ErrorOrigin::Callee;

		let ExecError { error, origin } = match from {
			Ok(retval) => return Ok(retval.into()),
			Err(err) => err,
		};

		match (error, origin) {
			(_, Callee) => Ok(ReturnCode::CalleeTrapped),
			(err, _) => Self::err_into_return_code(err),
		}
	}

	fn set_storage(
		&mut self,
		key_type: KeyType,
		key_ptr: u32,
		value_ptr: u32,
		value_len: u32,
	) -> Result<u32, TrapReason> {
		let max_size = self.ext.max_value_size();
		let charged = self
			.charge_gas(RuntimeCosts::SetStorage { new_bytes: value_len, old_bytes: max_size })?;
		if value_len > max_size {
			return Err(Error::<E::T>::ValueTooLarge.into())
		}
		let key = self.read_sandbox_memory(key_ptr, key_type.len::<E::T>()?)?;
		let value = Some(self.read_sandbox_memory(value_ptr, value_len)?);
		let write_outcome = match key_type {
			KeyType::Fix => self.ext.set_storage(
				&FixSizedKey::try_from(key).map_err(|_| Error::<E::T>::DecodingFailed)?,
				value,
				false,
			)?,
			KeyType::Variable(_) => self.ext.set_storage_transparent(
				&VarSizedKey::<E::T>::try_from(key).map_err(|_| Error::<E::T>::DecodingFailed)?,
				value,
				false,
			)?,
		};

		self.adjust_gas(
			charged,
			RuntimeCosts::SetStorage { new_bytes: value_len, old_bytes: write_outcome.old_len() },
		);
		Ok(write_outcome.old_len_with_sentinel())
	}

	fn clear_storage(&mut self, key_type: KeyType, key_ptr: u32) -> Result<u32, TrapReason> {
		let charged = self.charge_gas(RuntimeCosts::ClearStorage(self.ext.max_value_size()))?;
		let key = self.read_sandbox_memory(key_ptr, key_type.len::<E::T>()?)?;
		let outcome = match key_type {
			KeyType::Fix => self.ext.set_storage(
				&FixSizedKey::try_from(key).map_err(|_| Error::<E::T>::DecodingFailed)?,
				None,
				false,
			)?,
			KeyType::Variable(_) => self.ext.set_storage_transparent(
				&VarSizedKey::<E::T>::try_from(key).map_err(|_| Error::<E::T>::DecodingFailed)?,
				None,
				false,
			)?,
		};

		self.adjust_gas(charged, RuntimeCosts::ClearStorage(outcome.old_len()));
		Ok(outcome.old_len_with_sentinel())
	}

	fn get_storage(
		&mut self,
		key_type: KeyType,
		key_ptr: u32,
		out_ptr: u32,
		out_len_ptr: u32,
	) -> Result<ReturnCode, TrapReason> {
		let charged = self.charge_gas(RuntimeCosts::GetStorage(self.ext.max_value_size()))?;
		let key = self.read_sandbox_memory(key_ptr, key_type.len::<E::T>()?)?;
		let outcome = match key_type {
			KeyType::Fix => self.ext.get_storage(
				&FixSizedKey::try_from(key).map_err(|_| Error::<E::T>::DecodingFailed)?,
			),
			KeyType::Variable(_) => self.ext.get_storage_transparent(
				&VarSizedKey::<E::T>::try_from(key).map_err(|_| Error::<E::T>::DecodingFailed)?,
			),
		};

		if let Some(value) = outcome {
			self.adjust_gas(charged, RuntimeCosts::GetStorage(value.len() as u32));
			self.write_sandbox_output(out_ptr, out_len_ptr, &value, false, already_charged)?;
			Ok(ReturnCode::Success)
		} else {
			self.adjust_gas(charged, RuntimeCosts::GetStorage(0));
			Ok(ReturnCode::KeyNotFound)
		}
	}

	fn contains_storage(&mut self, key_type: KeyType, key_ptr: u32) -> Result<u32, TrapReason> {
		let charged = self.charge_gas(RuntimeCosts::ContainsStorage(self.ext.max_value_size()))?;
		let key = self.read_sandbox_memory(key_ptr, key_type.len::<E::T>()?)?;
		let outcome = match key_type {
			KeyType::Fix => self.ext.get_storage_size(
				&FixSizedKey::try_from(key).map_err(|_| Error::<E::T>::DecodingFailed)?,
			),
			KeyType::Variable(_) => self.ext.get_storage_size_transparent(
				&VarSizedKey::<E::T>::try_from(key).map_err(|_| Error::<E::T>::DecodingFailed)?,
			),
		};

		self.adjust_gas(charged, RuntimeCosts::ClearStorage(outcome.unwrap_or(0)));
		Ok(outcome.unwrap_or(SENTINEL))
	}

	fn call(
		&mut self,
		flags: CallFlags,
		call_type: CallType,
		input_data_ptr: u32,
		input_data_len: u32,
		output_ptr: u32,
		output_len_ptr: u32,
	) -> Result<ReturnCode, TrapReason> {
		self.charge_gas(call_type.cost())?;
		let input_data = if flags.contains(CallFlags::CLONE_INPUT) {
			let input = self.input_data.as_ref().ok_or(Error::<E::T>::InputForwarded)?;
			charge_gas!(self, RuntimeCosts::CallInputCloned(input.len() as u32))?;
			input.clone()
		} else if flags.contains(CallFlags::FORWARD_INPUT) {
			self.input_data.take().ok_or(Error::<E::T>::InputForwarded)?
		} else {
			self.charge_gas(RuntimeCosts::CopyFromContract(input_data_len))?;
			self.read_sandbox_memory(input_data_ptr, input_data_len)?
		};

		let call_outcome = match call_type {
			CallType::Call { callee_ptr, value_ptr, gas } => {
				let callee: <<E as Ext>::T as frame_system::Config>::AccountId =
					self.read_sandbox_memory_as(callee_ptr)?;
				let value: BalanceOf<<E as Ext>::T> = self.read_sandbox_memory_as(value_ptr)?;
				if value > 0u32.into() {
					self.charge_gas(RuntimeCosts::CallSurchargeTransfer)?;
				}
				self.ext.call(
					Weight::from_ref_time(gas),
					callee,
					value,
					input_data,
					flags.contains(CallFlags::ALLOW_REENTRY),
				)
			},
			CallType::DelegateCall { code_hash_ptr } => {
				if flags.contains(CallFlags::ALLOW_REENTRY) {
					return Err(Error::<E::T>::InvalidCallFlags.into())
				}
				let code_hash = self.read_sandbox_memory_as(code_hash_ptr)?;
				self.ext.delegate_call(code_hash, input_data)
			},
		};

		// `TAIL_CALL` only matters on an `OK` result. Otherwise the call stack comes to
		// a halt anyways without anymore code being executed.
		if flags.contains(CallFlags::TAIL_CALL) {
			if let Ok(return_value) = call_outcome {
				return Err(TrapReason::Return(ReturnData {
					flags: return_value.flags.bits(),
					data: return_value.data,
				}))
			}
		}

		if let Ok(output) = &call_outcome {
			self.write_sandbox_output(output_ptr, output_len_ptr, &output.data, true, |len| {
				Some(RuntimeCosts::CopyToContract(len))
			})?;
		}
		Ok(Runtime::<E>::exec_into_return_code(call_outcome)?)
	}

	fn instantiate(
		&mut self,
		code_hash_ptr: u32,
		gas: u64,
		value_ptr: u32,
		input_data_ptr: u32,
		input_data_len: u32,
		address_ptr: u32,
		address_len_ptr: u32,
		output_ptr: u32,
		output_len_ptr: u32,
		salt_ptr: u32,
		salt_len: u32,
	) -> Result<ReturnCode, TrapReason> {
		let gas = Weight::from_ref_time(gas);
		self.charge_gas(RuntimeCosts::InstantiateBase { input_data_len, salt_len })?;
		let value: BalanceOf<<E as Ext>::T> = self.read_sandbox_memory_as(value_ptr)?;
		if value > 0u32.into() {
			self.charge_gas(RuntimeCosts::InstantiateSurchargeTransfer)?;
		}
		let code_hash: CodeHash<<E as Ext>::T> = self.read_sandbox_memory_as(code_hash_ptr)?;
		let input_data = self.read_sandbox_memory(input_data_ptr, input_data_len)?;
		let salt = self.read_sandbox_memory(salt_ptr, salt_len)?;
		let instantiate_outcome = self.ext.instantiate(gas, code_hash, value, input_data, &salt);
		if let Ok((address, output)) = &instantiate_outcome {
			if !output.flags.contains(ReturnFlags::REVERT) {
				self.write_sandbox_output(
					address_ptr,
					address_len_ptr,
					&address.encode(),
					true,
					already_charged,
				)?;
			}
			self.write_sandbox_output(output_ptr, output_len_ptr, &output.data, true, |len| {
				Some(RuntimeCosts::CopyToContract(len))
			})?;
		}
		Ok(Runtime::<E>::exec_into_return_code(instantiate_outcome.map(|(_, retval)| retval))?)
	}

	fn terminate(&mut self, beneficiary_ptr: u32) -> Result<(), TrapReason> {
		self.charge_gas(RuntimeCosts::Terminate)?;
		let beneficiary: <<E as Ext>::T as frame_system::Config>::AccountId =
			self.read_sandbox_memory_as(beneficiary_ptr)?;
		self.ext.terminate(&beneficiary)?;
		Err(TrapReason::Termination)
	}
}

// This is the API exposed to contracts.
//
// # Note
//
// Any input that leads to a out of bound error (reading or writing) or failing to decode
// data passed to the supervisor will lead to a trap. This is not documented explicitly
// for every function.
#[define_env]
pub mod env {
	/// Account for used gas. Traps if gas used is greater than gas limit.
	///
	/// NOTE: This is a implementation defined call and is NOT a part of the public API.
	/// This call is supposed to be called only by instrumentation injected code.
	///
	/// - amount: How much gas is used.
	fn gas(ctx: Runtime<E>, amount: u64) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::MeteringBlock(amount))?;
		Ok(())
	}

	/// Set the value at the given key in the contract storage.
	///
	/// Equivalent to the newer version of `seal_set_storage` with the exception of the return
	/// type. Still a valid thing to call when not interested in the return value.
	#[prefixed_alias]
	fn set_storage(
		ctx: Runtime<E>,
		key_ptr: u32,
		value_ptr: u32,
		value_len: u32,
	) -> Result<(), TrapReason> {
		ctx.set_storage(KeyType::Fix, key_ptr, value_ptr, value_len).map(|_| ())
	}

	/// Set the value at the given key in the contract storage.
	///
	/// This version is to be used with a fixed sized storage key. For runtimes supporting
	/// transparent hashing, please use the newer version of this function.
	///
	/// The value length must not exceed the maximum defined by the contracts module parameters.
	/// Specifying a `value_len` of zero will store an empty value.
	///
	/// # Parameters
	///
	/// - `key_ptr`: pointer into the linear memory where the location to store the value is placed.
	/// - `value_ptr`: pointer into the linear memory where the value to set is placed.
	/// - `value_len`: the length of the value in bytes.
	///
	/// # Return Value
	///
	/// Returns the size of the pre-existing value at the specified key if any. Otherwise
	/// `SENTINEL` is returned as a sentinel value.
	#[version(1)]
	#[prefixed_alias]
	fn set_storage(
		ctx: Runtime<E>,
		key_ptr: u32,
		value_ptr: u32,
		value_len: u32,
	) -> Result<u32, TrapReason> {
		ctx.set_storage(KeyType::Fix, key_ptr, value_ptr, value_len)
	}

	/// Set the value at the given key in the contract storage.
	///
	/// The key and value lengths must not exceed the maximums defined by the contracts module
	/// parameters. Specifying a `value_len` of zero will store an empty value.
	///
	/// # Parameters
	///
	/// - `key_ptr`: pointer into the linear memory where the location to store the value is placed.
	/// - `key_len`: the length of the key in bytes.
	/// - `value_ptr`: pointer into the linear memory where the value to set is placed.
	/// - `value_len`: the length of the value in bytes.
	///
	/// # Return Value
	///
	/// Returns the size of the pre-existing value at the specified key if any. Otherwise
	/// `SENTINEL` is returned as a sentinel value.
	#[unstable]
	#[prefixed_alias]
	fn set_storage(
		ctx: Runtime<E>,
		key_ptr: u32,
		key_len: u32,
		value_ptr: u32,
		value_len: u32,
	) -> Result<u32, TrapReason> {
		ctx.set_storage(KeyType::Variable(key_len), key_ptr, value_ptr, value_len)
	}

	/// Clear the value at the given key in the contract storage.
	///
	/// Equivalent to the newer version of `seal_clear_storage` with the exception of the return
	/// type. Still a valid thing to call when not interested in the return value.
	#[prefixed_alias]
	fn clear_storage(ctx: Runtime<E>, key_ptr: u32) -> Result<(), TrapReason> {
		ctx.clear_storage(KeyType::Fix, key_ptr).map(|_| ())
	}

	/// Clear the value at the given key in the contract storage.
	///
	/// # Parameters
	///
	/// - `key_ptr`: pointer into the linear memory where the key is placed.
	/// - `key_len`: the length of the key in bytes.
	///
	/// # Return Value
	///
	/// Returns the size of the pre-existing value at the specified key if any. Otherwise
	/// `SENTINEL` is returned as a sentinel value.
	#[unstable]
	#[prefixed_alias]
	fn clear_storage(ctx: Runtime<E>, key_ptr: u32, key_len: u32) -> Result<u32, TrapReason> {
		ctx.clear_storage(KeyType::Variable(key_len), key_ptr)
	}

	/// Retrieve the value under the given key from storage.
	///
	/// This version is to be used with a fixed sized storage key. For runtimes supporting
	/// transparent hashing, please use the newer version of this function.
	///
	/// # Parameters
	///
	/// - `key_ptr`: pointer into the linear memory where the key of the requested value is placed.
	/// - `out_ptr`: pointer to the linear memory where the value is written to.
	/// - `out_len_ptr`: in-out pointer into linear memory where the buffer length is read from and
	///   the value length is written to.
	///
	/// # Errors
	///
	/// `ReturnCode::KeyNotFound`
	#[prefixed_alias]
	fn get_storage(
		ctx: Runtime<E>,
		key_ptr: u32,
		out_ptr: u32,
		out_len_ptr: u32,
	) -> Result<ReturnCode, TrapReason> {
		ctx.get_storage(KeyType::Fix, key_ptr, out_ptr, out_len_ptr)
	}

	/// Retrieve the value under the given key from storage.
	///
	/// This version is to be used with a fixed sized storage key. For runtimes supporting
	/// transparent hashing, please use the newer version of this function.
	///
	/// The key length must not exceed the maximum defined by the contracts module parameter.
	///
	/// # Parameters
	///
	/// - `key_ptr`: pointer into the linear memory where the key of the requested value is placed.
	/// - `key_len`: the length of the key in bytes.
	/// - `out_ptr`: pointer to the linear memory where the value is written to.
	/// - `out_len_ptr`: in-out pointer into linear memory where the buffer length is read from and
	///   the value length is written to.
	///
	/// # Errors
	///
	/// `ReturnCode::KeyNotFound`
	#[unstable]
	#[prefixed_alias]
	fn get_storage(
		ctx: Runtime<E>,
		key_ptr: u32,
		key_len: u32,
		out_ptr: u32,
		out_len_ptr: u32,
	) -> Result<ReturnCode, TrapReason> {
		ctx.get_storage(KeyType::Variable(key_len), key_ptr, out_ptr, out_len_ptr)
	}

	/// Checks whether there is a value stored under the given key.
	///
	/// This version is to be used with a fixed sized storage key. For runtimes supporting
	/// transparent hashing, please use the newer version of this function.
	///
	/// # Parameters
	///
	/// - `key_ptr`: pointer into the linear memory where the key of the requested value is placed.
	///
	/// # Return Value
	///
	/// Returns the size of the pre-existing value at the specified key if any. Otherwise
	/// `SENTINEL` is returned as a sentinel value.
	#[prefixed_alias]
	fn contains_storage(ctx: Runtime<E>, key_ptr: u32) -> Result<u32, TrapReason> {
		ctx.contains_storage(KeyType::Fix, key_ptr)
	}

	/// Checks whether there is a value stored under the given key.
	///
	/// The key length must not exceed the maximum defined by the contracts module parameter.
	///
	/// # Parameters
	///
	/// - `key_ptr`: pointer into the linear memory where the key of the requested value is placed.
	/// - `key_len`: the length of the key in bytes.
	///
	/// # Return Value
	///
	/// Returns the size of the pre-existing value at the specified key if any. Otherwise
	/// `SENTINEL` is returned as a sentinel value.
	#[unstable]
	#[prefixed_alias]
	fn contains_storage(ctx: Runtime<E>, key_ptr: u32, key_len: u32) -> Result<u32, TrapReason> {
		ctx.contains_storage(KeyType::Variable(key_len), key_ptr)
	}

	/// Retrieve and remove the value under the given key from storage.
	///
	/// # Parameters
	///
	/// - `key_ptr`: pointer into the linear memory where the key of the requested value is placed.
	/// - `key_len`: the length of the key in bytes.
	/// - `out_ptr`: pointer to the linear memory where the value is written to.
	/// - `out_len_ptr`: in-out pointer into linear memory where the buffer length is read from and
	///   the value length is written to.
	///
	/// # Errors
	///
	/// `ReturnCode::KeyNotFound`
	#[unstable]
	#[prefixed_alias]
	fn take_storage(
		ctx: Runtime<E>,
		key_ptr: u32,
		key_len: u32,
		out_ptr: u32,
		out_len_ptr: u32,
	) -> Result<ReturnCode, TrapReason> {
		let charged = ctx.charge_gas(RuntimeCosts::TakeStorage(ctx.ext.max_value_size()))?;
		let key = ctx.read_sandbox_memory(key_ptr, key_len)?;
		if let crate::storage::WriteOutcome::Taken(value) = ctx.ext.set_storage_transparent(
			&VarSizedKey::<E::T>::try_from(key).map_err(|_| Error::<E::T>::DecodingFailed)?,
			None,
			true,
		)? {
			ctx.adjust_gas(charged, RuntimeCosts::TakeStorage(value.len() as u32));
			ctx.write_sandbox_output(out_ptr, out_len_ptr, &value, false, already_charged)?;
			Ok(ReturnCode::Success)
		} else {
			ctx.adjust_gas(charged, RuntimeCosts::TakeStorage(0));
			Ok(ReturnCode::KeyNotFound)
		}
	}
	/// Transfer some value to another account.
	///
	/// # Parameters
	///
	/// - account_ptr: a pointer to the address of the beneficiary account Should be decodable as an
	///   `T::AccountId`. Traps otherwise.
	/// - account_len: length of the address buffer.
	/// - value_ptr: a pointer to the buffer with value, how much value to send. Should be decodable
	///   as a `T::Balance`. Traps otherwise.
	/// - value_len: length of the value buffer.
	///
	/// # Errors
	///
	/// `ReturnCode::TransferFailed`
	#[prefixed_alias]
	fn transfer(
		ctx: Runtime<E>,
		account_ptr: u32,
		_account_len: u32,
		value_ptr: u32,
		_value_len: u32,
	) -> Result<ReturnCode, TrapReason> {
		ctx.charge_gas(RuntimeCosts::Transfer)?;
		let callee: <<E as Ext>::T as frame_system::Config>::AccountId =
			ctx.read_sandbox_memory_as(account_ptr)?;
		let value: BalanceOf<<E as Ext>::T> = ctx.read_sandbox_memory_as(value_ptr)?;
		let result = ctx.ext.transfer(&callee, value);
		match result {
			Ok(()) => Ok(ReturnCode::Success),
			Err(err) => {
				let code = Runtime::<E>::err_into_return_code(err)?;
				Ok(code)
			},
		}
	}

	/// Make a call to another contract.
	///
	/// # Deprecation
	///
	/// This is equivalent to calling the newer version of this function with
	/// `flags` set to `ALLOW_REENTRY`. See the newer version for documentation.
	///
	/// # Note
	///
	/// The values `_callee_len` and `_value_len` are ignored because the encoded sizes
	/// of those types are fixed through `[`MaxEncodedLen`]. The fields exist for backwards
	/// compatibility. Consider switching to the newest version of this function.
	#[prefixed_alias]
	fn call(
		ctx: Runtime<E>,
		callee_ptr: u32,
		_callee_len: u32,
		gas: u64,
		value_ptr: u32,
		_value_len: u32,
		input_data_ptr: u32,
		input_data_len: u32,
		output_ptr: u32,
		output_len_ptr: u32,
	) -> Result<ReturnCode, TrapReason> {
		ctx.call(
			CallFlags::ALLOW_REENTRY,
			CallType::Call { callee_ptr, value_ptr, gas },
			input_data_ptr,
			input_data_len,
			output_ptr,
			output_len_ptr,
		)
	}

	/// Make a call to another contract.
	///
	/// The callees output buffer is copied to `output_ptr` and its length to `output_len_ptr`.
	/// The copy of the output buffer can be skipped by supplying the sentinel value
	/// of `SENTINEL` to `output_ptr`.
	///
	/// # Parameters
	///
	/// - flags: See [`CallFlags`] for a documenation of the supported flags.
	/// - callee_ptr: a pointer to the address of the callee contract. Should be decodable as an
	///   `T::AccountId`. Traps otherwise.
	/// - gas: how much gas to devote to the execution.
	/// - value_ptr: a pointer to the buffer with value, how much value to send. Should be decodable
	///   as a `T::Balance`. Traps otherwise.
	/// - input_data_ptr: a pointer to a buffer to be used as input data to the callee.
	/// - input_data_len: length of the input data buffer.
	/// - output_ptr: a pointer where the output buffer is copied to.
	/// - output_len_ptr: in-out pointer to where the length of the buffer is read from and the
	///   actual length is written to.
	///
	/// # Errors
	///
	/// An error means that the call wasn't successful output buffer is returned unless
	/// stated otherwise.
	///
	/// `ReturnCode::CalleeReverted`: Output buffer is returned.
	/// `ReturnCode::CalleeTrapped`
	/// `ReturnCode::TransferFailed`
	/// `ReturnCode::NotCallable`
	#[version(1)]
	#[prefixed_alias]
	fn call(
		ctx: Runtime<E>,
		flags: u32,
		callee_ptr: u32,
		gas: u64,
		value_ptr: u32,
		input_data_ptr: u32,
		input_data_len: u32,
		output_ptr: u32,
		output_len_ptr: u32,
	) -> Result<ReturnCode, TrapReason> {
		ctx.call(
			CallFlags::from_bits(flags).ok_or(Error::<E::T>::InvalidCallFlags)?,
			CallType::Call { callee_ptr, value_ptr, gas },
			input_data_ptr,
			input_data_len,
			output_ptr,
			output_len_ptr,
		)
	}

	/// Execute code in the context (storage, caller, value) of the current contract.
	///
	/// Reentrancy protection is always disabled since the callee is allowed
	/// to modify the callers storage. This makes going through a reentrancy attack
	/// unnecessary for the callee when it wants to exploit the caller.
	///
	/// # Parameters
	///
	/// - flags: See [`CallFlags`] for a documentation of the supported flags.
	/// - code_hash: a pointer to the hash of the code to be called.
	/// - input_data_ptr: a pointer to a buffer to be used as input data to the callee.
	/// - input_data_len: length of the input data buffer.
	/// - output_ptr: a pointer where the output buffer is copied to.
	/// - output_len_ptr: in-out pointer to where the length of the buffer is read from and the
	///   actual length is written to.
	///
	/// # Errors
	///
	/// An error means that the call wasn't successful and no output buffer is returned unless
	/// stated otherwise.
	///
	/// `ReturnCode::CalleeReverted`: Output buffer is returned.
	/// `ReturnCode::CalleeTrapped`
	/// `ReturnCode::CodeNotFound`
	#[prefixed_alias]
	fn delegate_call(
		ctx: Runtime<E>,
		flags: u32,
		code_hash_ptr: u32,
		input_data_ptr: u32,
		input_data_len: u32,
		output_ptr: u32,
		output_len_ptr: u32,
	) -> Result<ReturnCode, TrapReason> {
		ctx.call(
			CallFlags::from_bits(flags).ok_or(Error::<E::T>::InvalidCallFlags)?,
			CallType::DelegateCall { code_hash_ptr },
			input_data_ptr,
			input_data_len,
			output_ptr,
			output_len_ptr,
		)
	}
	/// Instantiate a contract with the specified code hash.
	///
	/// # Deprecation
	///
	/// This is equivalent to calling the newer version of this function. The newer version
	/// drops the now unnecessary length fields.
	///
	/// # Note
	///
	/// The values `_code_hash_len` and `_value_len` are ignored because the encoded sizes
	/// of those types are fixed through `[`MaxEncodedLen`]. The fields exist for backwards
	/// compatibility. Consider switching to the newest version of this function.
	#[prefixed_alias]
	fn instantiate(
		ctx: Runtime<E>,
		code_hash_ptr: u32,
		_code_hash_len: u32,
		gas: u64,
		value_ptr: u32,
		_value_len: u32,
		input_data_ptr: u32,
		input_data_len: u32,
		address_ptr: u32,
		address_len_ptr: u32,
		output_ptr: u32,
		output_len_ptr: u32,
		salt_ptr: u32,
		salt_len: u32,
	) -> Result<ReturnCode, TrapReason> {
		ctx.instantiate(
			code_hash_ptr,
			gas,
			value_ptr,
			input_data_ptr,
			input_data_len,
			address_ptr,
			address_len_ptr,
			output_ptr,
			output_len_ptr,
			salt_ptr,
			salt_len,
		)
	}

	/// Instantiate a contract with the specified code hash.
	///
	/// This function creates an account and executes the constructor defined in the code specified
	/// by the code hash. The address of this new account is copied to `address_ptr` and its length
	/// to `address_len_ptr`. The constructors output buffer is copied to `output_ptr` and its
	/// length to `output_len_ptr`. The copy of the output buffer and address can be skipped by
	/// supplying the sentinel value of `SENTINEL` to `output_ptr` or `address_ptr`.
	///
	/// `value` must be at least the minimum balance. Otherwise the instantiation fails and the
	/// contract is not created.
	///
	/// # Parameters
	///
	/// - code_hash_ptr: a pointer to the buffer that contains the initializer code.
	/// - gas: how much gas to devote to the execution of the initializer code.
	/// - value_ptr: a pointer to the buffer with value, how much value to send. Should be decodable
	///   as a `T::Balance`. Traps otherwise.
	/// - input_data_ptr: a pointer to a buffer to be used as input data to the initializer code.
	/// - input_data_len: length of the input data buffer.
	/// - address_ptr: a pointer where the new account's address is copied to.
	/// - address_len_ptr: in-out pointer to where the length of the buffer is read from and the
	///   actual length is written to.
	/// - output_ptr: a pointer where the output buffer is copied to.
	/// - output_len_ptr: in-out pointer to where the length of the buffer is read from and the
	///   actual length is written to.
	/// - salt_ptr: Pointer to raw bytes used for address derivation. See `fn contract_address`.
	/// - salt_len: length in bytes of the supplied salt.
	///
	/// # Errors
	///
	/// Please consult the `ReturnCode` enum declaration for more information on those
	/// errors. Here we only note things specific to this function.
	///
	/// An error means that the account wasn't created and no address or output buffer
	/// is returned unless stated otherwise.
	///
	/// `ReturnCode::CalleeReverted`: Output buffer is returned.
	/// `ReturnCode::CalleeTrapped`
	/// `ReturnCode::TransferFailed`
	/// `ReturnCode::CodeNotFound`
	#[version(1)]
	#[prefixed_alias]
	fn instantiate(
		ctx: Runtime<E>,
		code_hash_ptr: u32,
		gas: u64,
		value_ptr: u32,
		input_data_ptr: u32,
		input_data_len: u32,
		address_ptr: u32,
		address_len_ptr: u32,
		output_ptr: u32,
		output_len_ptr: u32,
		salt_ptr: u32,
		salt_len: u32,
	) -> Result<ReturnCode, TrapReason> {
		ctx.instantiate(
			code_hash_ptr,
			gas,
			value_ptr,
			input_data_ptr,
			input_data_len,
			address_ptr,
			address_len_ptr,
			output_ptr,
			output_len_ptr,
			salt_ptr,
			salt_len,
		)
	}

	/// Remove the calling account and transfer remaining balance.
	///
	/// # Deprecation
	///
	/// This is equivalent to calling the newer version of this function. The newer version
	/// drops the now unnecessary length fields.
	///
	/// # Note
	///
	/// The value `_beneficiary_len` is ignored because the encoded sizes
	/// this type is fixed through `[`MaxEncodedLen`]. The field exist for backwards
	/// compatibility. Consider switching to the newest version of this function.
	#[prefixed_alias]
	fn terminate(
		ctx: Runtime<E>,
		beneficiary_ptr: u32,
		_beneficiary_len: u32,
	) -> Result<(), TrapReason> {
		ctx.terminate(beneficiary_ptr)
	}

	/// Remove the calling account and transfer remaining **free** balance.
	///
	/// This function never returns. Either the termination was successful and the
	/// execution of the destroyed contract is halted. Or it failed during the termination
	/// which is considered fatal and results in a trap + rollback.
	///
	/// - beneficiary_ptr: a pointer to the address of the beneficiary account where all where all
	///   remaining funds of the caller are transferred. Should be decodable as an `T::AccountId`.
	///   Traps otherwise.
	///
	/// # Traps
	///
	/// - The contract is live i.e is already on the call stack.
	/// - Failed to send the balance to the beneficiary.
	/// - The deletion queue is full.
	#[version(1)]
	#[prefixed_alias]
	fn terminate(ctx: Runtime<E>, beneficiary_ptr: u32) -> Result<(), TrapReason> {
		ctx.terminate(beneficiary_ptr)
	}

	/// Stores the input passed by the caller into the supplied buffer.
	///
	/// The value is stored to linear memory at the address pointed to by `out_ptr`.
	/// `out_len_ptr` must point to a u32 value that describes the available space at
	/// `out_ptr`. This call overwrites it with the size of the value. If the available
	/// space at `out_ptr` is less than the size of the value a trap is triggered.
	///
	/// # Note
	///
	/// This function traps if the input was previously forwarded by a `seal_call`.
	#[prefixed_alias]
	fn input(ctx: Runtime<E>, out_ptr: u32, out_len_ptr: u32) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::InputBase)?;
		if let Some(input) = ctx.input_data.take() {
			ctx.write_sandbox_output(out_ptr, out_len_ptr, &input, false, |len| {
				Some(RuntimeCosts::CopyToContract(len))
			})?;
			ctx.input_data = Some(input);
			Ok(())
		} else {
			Err(Error::<E::T>::InputForwarded.into())
		}
	}

	/// Cease contract execution and save a data buffer as a result of the execution.
	///
	/// This function never returns as it stops execution of the caller.
	/// This is the only way to return a data buffer to the caller. Returning from
	/// execution without calling this function is equivalent to calling:
	/// ```
	/// seal_return(0, 0, 0);
	/// ```
	///
	/// The flags argument is a bitfield that can be used to signal special return
	/// conditions to the supervisor:
	/// --- lsb ---
	/// bit 0      : REVERT - Revert all storage changes made by the caller.
	/// bit [1, 31]: Reserved for future use.
	/// --- msb ---
	///
	/// Using a reserved bit triggers a trap.
	fn seal_return(
		ctx: Runtime<E>,
		flags: u32,
		data_ptr: u32,
		data_len: u32,
	) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::Return(data_len))?;
		Err(TrapReason::Return(ReturnData {
			flags,
			data: ctx.read_sandbox_memory(data_ptr, data_len)?,
		}))
	}

	/// Stores the address of the caller into the supplied buffer.
	///
	/// The value is stored to linear memory at the address pointed to by `out_ptr`.
	/// `out_len_ptr` must point to a u32 value that describes the available space at
	/// `out_ptr`. This call overwrites it with the size of the value. If the available
	/// space at `out_ptr` is less than the size of the value a trap is triggered.
	///
	/// If this is a top-level call (i.e. initiated by an extrinsic) the origin address of the
	/// extrinsic will be returned. Otherwise, if this call is initiated by another contract then
	/// the address of the contract will be returned. The value is encoded as T::AccountId.
	#[prefixed_alias]
	fn caller(ctx: Runtime<E>, out_ptr: u32, out_len_ptr: u32) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::Caller)?;
		Ok(ctx.write_sandbox_output(
			out_ptr,
			out_len_ptr,
			&ctx.ext.caller().encode(),
			false,
			already_charged,
		)?)
	}

	/// Checks whether a specified address belongs to a contract.
	///
	/// # Parameters
	///
	/// - account_ptr: a pointer to the address of the beneficiary account Should be decodable as an
	///   `T::AccountId`. Traps otherwise.
	///
	/// Returned value is a u32-encoded boolean: (0 = false, 1 = true).
	#[prefixed_alias]
	fn is_contract(ctx: Runtime<E>, account_ptr: u32) -> Result<u32, TrapReason> {
		ctx.charge_gas(RuntimeCosts::IsContract)?;
		let address: <<E as Ext>::T as frame_system::Config>::AccountId =
			ctx.read_sandbox_memory_as(account_ptr)?;

		Ok(ctx.ext.is_contract(&address) as u32)
	}

	/// Retrieve the code hash for a specified contract address.
	///
	/// # Parameters
	///
	/// - `account_ptr`: a pointer to the address in question. Should be decodable as an
	///   `T::AccountId`. Traps otherwise.
	/// - `out_ptr`: pointer to the linear memory where the returning value is written to.
	/// - `out_len_ptr`: in-out pointer into linear memory where the buffer length is read from and
	///   the value length is written to.
	///
	/// # Errors
	///
	/// `ReturnCode::KeyNotFound`
	#[prefixed_alias]
	fn code_hash(
		ctx: Runtime<E>,
		account_ptr: u32,
		out_ptr: u32,
		out_len_ptr: u32,
	) -> Result<ReturnCode, TrapReason> {
		ctx.charge_gas(RuntimeCosts::CodeHash)?;
		let address: <<E as Ext>::T as frame_system::Config>::AccountId =
			ctx.read_sandbox_memory_as(account_ptr)?;
		if let Some(value) = ctx.ext.code_hash(&address) {
			ctx.write_sandbox_output(
				out_ptr,
				out_len_ptr,
				&value.encode(),
				false,
				already_charged,
			)?;
			Ok(ReturnCode::Success)
		} else {
			Ok(ReturnCode::KeyNotFound)
		}
	}

	/// Retrieve the code hash of the currently executing contract.
	///
	/// # Parameters
	///
	/// - `out_ptr`: pointer to the linear memory where the returning value is written to.
	/// - `out_len_ptr`: in-out pointer into linear memory where the buffer length is read from and
	///   the value length is written to.
	#[prefixed_alias]
	fn own_code_hash(ctx: Runtime<E>, out_ptr: u32, out_len_ptr: u32) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::OwnCodeHash)?;
		let code_hash_encoded = &ctx.ext.own_code_hash().encode();
		Ok(ctx.write_sandbox_output(
			out_ptr,
			out_len_ptr,
			code_hash_encoded,
			false,
			already_charged,
		)?)
	}

	/// Checks whether the caller of the current contract is the origin of the whole call stack.
	///
	/// Prefer this over `seal_is_contract` when checking whether your contract is being called by a
	/// contract or a plain account. The reason is that it performs better since it does not need to
	/// do any storage lookups.
	///
	/// A return value of`true` indicates that this contract is being called by a plain account
	/// and `false` indicates that the caller is another contract.
	///
	/// Returned value is a u32-encoded boolean: (0 = false, 1 = true).
	#[prefixed_alias]
	fn caller_is_origin(ctx: Runtime<E>) -> Result<u32, TrapReason> {
		ctx.charge_gas(RuntimeCosts::CallerIsOrigin)?;
		Ok(ctx.ext.caller_is_origin() as u32)
	}

	/// Stores the address of the current contract into the supplied buffer.
	///
	/// The value is stored to linear memory at the address pointed to by `out_ptr`.
	/// `out_len_ptr` must point to a u32 value that describes the available space at
	/// `out_ptr`. This call overwrites it with the size of the value. If the available
	/// space at `out_ptr` is less than the size of the value a trap is triggered.
	#[prefixed_alias]
	fn address(ctx: Runtime<E>, out_ptr: u32, out_len_ptr: u32) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::Address)?;
		Ok(ctx.write_sandbox_output(
			out_ptr,
			out_len_ptr,
			&ctx.ext.address().encode(),
			false,
			already_charged,
		)?)
	}

	/// Stores the price for the specified amount of gas into the supplied buffer.
	///
	/// The value is stored to linear memory at the address pointed to by `out_ptr`.
	/// `out_len_ptr` must point to a u32 value that describes the available space at
	/// `out_ptr`. This call overwrites it with the size of the value. If the available
	/// space at `out_ptr` is less than the size of the value a trap is triggered.
	///
	/// The data is encoded as T::Balance.
	///
	/// # Note
	///
	/// It is recommended to avoid specifying very small values for `gas` as the prices for a single
	/// gas can be smaller than one.
	#[prefixed_alias]
	fn weight_to_fee(
		ctx: Runtime<E>,
		gas: u64,
		out_ptr: u32,
		out_len_ptr: u32,
	) -> Result<(), TrapReason> {
		let gas = Weight::from_ref_time(gas);
		ctx.charge_gas(RuntimeCosts::WeightToFee)?;
		Ok(ctx.write_sandbox_output(
			out_ptr,
			out_len_ptr,
			&ctx.ext.get_weight_price(gas).encode(),
			false,
			already_charged,
		)?)
	}

	/// Stores the amount of gas left into the supplied buffer.
	///
	/// The value is stored to linear memory at the address pointed to by `out_ptr`.
	/// `out_len_ptr` must point to a u32 value that describes the available space at
	/// `out_ptr`. This call overwrites it with the size of the value. If the available
	/// space at `out_ptr` is less than the size of the value a trap is triggered.
	///
	/// The data is encoded as Gas.
	#[prefixed_alias]
	fn gas_left(ctx: Runtime<E>, out_ptr: u32, out_len_ptr: u32) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::GasLeft)?;
		let gas_left = &ctx.ext.gas_meter().gas_left().ref_time().encode();
		Ok(ctx.write_sandbox_output(out_ptr, out_len_ptr, gas_left, false, already_charged)?)
	}

	/// Stores the **free* balance of the current account into the supplied buffer.
	///
	/// The value is stored to linear memory at the address pointed to by `out_ptr`.
	/// `out_len_ptr` must point to a u32 value that describes the available space at
	/// `out_ptr`. This call overwrites it with the size of the value. If the available
	/// space at `out_ptr` is less than the size of the value a trap is triggered.
	///
	/// The data is encoded as T::Balance.
	#[prefixed_alias]
	fn balance(ctx: Runtime<E>, out_ptr: u32, out_len_ptr: u32) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::Balance)?;
		Ok(ctx.write_sandbox_output(
			out_ptr,
			out_len_ptr,
			&ctx.ext.balance().encode(),
			false,
			already_charged,
		)?)
	}

	/// Stores the value transferred along with this call/instantiate into the supplied buffer.
	///
	/// The value is stored to linear memory at the address pointed to by `out_ptr`.
	/// `out_len_ptr` must point to a u32 value that describes the available space at
	/// `out_ptr`. This call overwrites it with the size of the value. If the available
	/// space at `out_ptr` is less than the size of the value a trap is triggered.
	///
	/// The data is encoded as T::Balance.
	#[prefixed_alias]
	fn value_transferred(
		ctx: Runtime<E>,
		out_ptr: u32,
		out_len_ptr: u32,
	) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::ValueTransferred)?;
		Ok(ctx.write_sandbox_output(
			out_ptr,
			out_len_ptr,
			&ctx.ext.value_transferred().encode(),
			false,
			already_charged,
		)?)
	}

	/// Stores a random number for the current block and the given subject into the supplied buffer.
	///
	/// The value is stored to linear memory at the address pointed to by `out_ptr`.
	/// `out_len_ptr` must point to a u32 value that describes the available space at
	/// `out_ptr`. This call overwrites it with the size of the value. If the available
	/// space at `out_ptr` is less than the size of the value a trap is triggered.
	///
	/// The data is encoded as T::Hash.
	///
	/// # Deprecation
	///
	/// This function is deprecated. Users should migrate to the version in the "seal1" module.
	#[prefixed_alias]
	fn random(
		ctx: Runtime<E>,
		subject_ptr: u32,
		subject_len: u32,
		out_ptr: u32,
		out_len_ptr: u32,
	) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::Random)?;
		if subject_len > ctx.ext.schedule().limits.subject_len {
			return Err(Error::<E::T>::RandomSubjectTooLong.into())
		}
		let subject_buf = ctx.read_sandbox_memory(subject_ptr, subject_len)?;
		Ok(ctx.write_sandbox_output(
			out_ptr,
			out_len_ptr,
			&ctx.ext.random(&subject_buf).0.encode(),
			false,
			already_charged,
		)?)
	}

	/// Stores a random number for the current block and the given subject into the supplied buffer.
	///
	/// The value is stored to linear memory at the address pointed to by `out_ptr`.
	/// `out_len_ptr` must point to a u32 value that describes the available space at
	/// `out_ptr`. This call overwrites it with the size of the value. If the available
	/// space at `out_ptr` is less than the size of the value a trap is triggered.
	///
	/// The data is encoded as (T::Hash, T::BlockNumber).
	///
	/// # Changes from v0
	///
	/// In addition to the seed it returns the block number since which it was determinable
	/// by chain observers.
	///
	/// # Note
	///
	/// The returned seed should only be used to distinguish commitments made before
	/// the returned block number. If the block number is too early (i.e. commitments were
	/// made afterwards), then ensure no further commitments may be made and repeatedly
	/// call this on later blocks until the block number returned is later than the latest
	/// commitment.
	#[version(1)]
	#[prefixed_alias]
	fn random(
		ctx: Runtime<E>,
		subject_ptr: u32,
		subject_len: u32,
		out_ptr: u32,
		out_len_ptr: u32,
	) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::Random)?;
		if subject_len > ctx.ext.schedule().limits.subject_len {
			return Err(Error::<E::T>::RandomSubjectTooLong.into())
		}
		let subject_buf = ctx.read_sandbox_memory(subject_ptr, subject_len)?;
		Ok(ctx.write_sandbox_output(
			out_ptr,
			out_len_ptr,
			&ctx.ext.random(&subject_buf).encode(),
			false,
			already_charged,
		)?)
	}

	/// Load the latest block timestamp into the supplied buffer
	///
	/// The value is stored to linear memory at the address pointed to by `out_ptr`.
	/// `out_len_ptr` must point to a u32 value that describes the available space at
	/// `out_ptr`. This call overwrites it with the size of the value. If the available
	/// space at `out_ptr` is less than the size of the value a trap is triggered.
	#[prefixed_alias]
	fn now(ctx: Runtime<E>, out_ptr: u32, out_len_ptr: u32) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::Now)?;
		Ok(ctx.write_sandbox_output(
			out_ptr,
			out_len_ptr,
			&ctx.ext.now().encode(),
			false,
			already_charged,
		)?)
	}

	/// Stores the minimum balance (a.k.a. existential deposit) into the supplied buffer.
	///
	/// The data is encoded as T::Balance.
	#[prefixed_alias]
	fn minimum_balance(ctx: Runtime<E>, out_ptr: u32, out_len_ptr: u32) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::MinimumBalance)?;
		Ok(ctx.write_sandbox_output(
			out_ptr,
			out_len_ptr,
			&ctx.ext.minimum_balance().encode(),
			false,
			already_charged,
		)?)
	}

	/// Stores the tombstone deposit into the supplied buffer.
	///
	/// The value is stored to linear memory at the address pointed to by `out_ptr`.
	/// `out_len_ptr` must point to a u32 value that describes the available space at
	/// `out_ptr`. This call overwrites it with the size of the value. If the available
	/// space at `out_ptr` is less than the size of the value a trap is triggered.
	///
	/// # Deprecation
	///
	/// There is no longer a tombstone deposit. This function always returns 0.
	#[prefixed_alias]
	fn tombstone_deposit(
		ctx: Runtime<E>,
		out_ptr: u32,
		out_len_ptr: u32,
	) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::Balance)?;
		let deposit = <BalanceOf<E::T>>::zero().encode();
		Ok(ctx.write_sandbox_output(out_ptr, out_len_ptr, &deposit, false, already_charged)?)
	}

	/// Was used to restore the given destination contract sacrificing the caller.
	///
	/// # Note
	///
	/// The state rent functionality was removed. This is stub only exists for
	/// backwards compatiblity
	#[prefixed_alias]
	fn restore_to(
		ctx: Runtime<E>,
		_dest_ptr: u32,
		_dest_len: u32,
		_code_hash_ptr: u32,
		_code_hash_len: u32,
		_rent_allowance_ptr: u32,
		_rent_allowance_len: u32,
		_delta_ptr: u32,
		_delta_count: u32,
	) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::DebugMessage)?;
		Ok(())
	}

	/// Was used to restore the given destination contract sacrificing the caller.
	///
	/// # Note
	///
	/// The state rent functionality was removed. This is stub only exists for
	/// backwards compatiblity
	#[version(1)]
	#[prefixed_alias]
	fn restore_to(
		ctx: Runtime<E>,
		_dest_ptr: u32,
		_code_hash_ptr: u32,
		_rent_allowance_ptr: u32,
		_delta_ptr: u32,
		_delta_count: u32,
	) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::DebugMessage)?;
		Ok(())
	}

	/// Deposit a contract event with the data buffer and optional list of topics. There is a limit
	/// on the maximum number of topics specified by `event_topics`.
	///
	/// - topics_ptr - a pointer to the buffer of topics encoded as `Vec<T::Hash>`. The value of
	///   this is ignored if `topics_len` is set to 0. The topics list can't contain duplicates.
	/// - topics_len - the length of the topics buffer. Pass 0 if you want to pass an empty vector.
	/// - data_ptr - a pointer to a raw data buffer which will saved along the event.
	/// - data_len - the length of the data buffer.
	#[prefixed_alias]
	fn deposit_event(
		ctx: Runtime<E>,
		topics_ptr: u32,
		topics_len: u32,
		data_ptr: u32,
		data_len: u32,
	) -> Result<(), TrapReason> {
		fn has_duplicates<T: Ord>(items: &mut Vec<T>) -> bool {
			// # Warning
			//
			// Unstable sorts are non-deterministic across architectures. The usage here is OK
			// because we are rejecting duplicates which removes the non determinism.
			items.sort_unstable();
			// Find any two consecutive equal elements.
			items.windows(2).any(|w| match &w {
				&[a, b] => a == b,
				_ => false,
			})
		}

		let num_topic = topics_len
			.checked_div(sp_std::mem::size_of::<TopicOf<E::T>>() as u32)
			.ok_or("Zero sized topics are not allowed")?;
		ctx.charge_gas(RuntimeCosts::DepositEvent { num_topic, len: data_len })?;
		if data_len > ctx.ext.max_value_size() {
			return Err(Error::<E::T>::ValueTooLarge.into())
		}

		let mut topics: Vec<TopicOf<<E as Ext>::T>> = match topics_len {
			0 => Vec::new(),
			_ => ctx.read_sandbox_memory_as_unbounded(topics_ptr, topics_len)?,
		};

		// If there are more than `event_topics`, then trap.
		if topics.len() > ctx.ext.schedule().limits.event_topics as usize {
			return Err(Error::<E::T>::TooManyTopics.into())
		}

		// Check for duplicate topics. If there are any, then trap.
		// Complexity O(n * log(n)) and no additional allocations.
		// This also sorts the topics.
		if has_duplicates(&mut topics) {
			return Err(Error::<E::T>::DuplicateTopics.into())
		}

		let event_data = ctx.read_sandbox_memory(data_ptr, data_len)?;

		ctx.ext.deposit_event(topics, event_data);

		Ok(())
	}

	/// Was used to set rent allowance of the contract.
	///
	/// # Note
	///
	/// The state rent functionality was removed. This is stub only exists for
	/// backwards compatiblity.
	#[prefixed_alias]
	fn set_rent_allowance(
		ctx: Runtime<E>,
		_value_ptr: u32,
		_value_len: u32,
	) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::DebugMessage)?;
		Ok(())
	}

	/// Was used to set rent allowance of the contract.
	///
	/// # Note
	///
	/// The state rent functionality was removed. This is stub only exists for
	/// backwards compatiblity.
	#[version(1)]
	#[prefixed_alias]
	fn set_rent_allowance(ctx: Runtime<E>, _value_ptr: u32) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::DebugMessage)?;
		Ok(())
	}

	/// Was used to store the rent allowance into the supplied buffer.
	///
	/// # Note
	///
	/// The state rent functionality was removed. This is stub only exists for
	/// backwards compatiblity.
	#[prefixed_alias]
	fn rent_allowance(ctx: Runtime<E>, out_ptr: u32, out_len_ptr: u32) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::Balance)?;
		let rent_allowance = <BalanceOf<E::T>>::max_value().encode();
		Ok(ctx.write_sandbox_output(
			out_ptr,
			out_len_ptr,
			&rent_allowance,
			false,
			already_charged,
		)?)
	}

	/// Stores the current block number of the current contract into the supplied buffer.
	///
	/// The value is stored to linear memory at the address pointed to by `out_ptr`.
	/// `out_len_ptr` must point to a u32 value that describes the available space at
	/// `out_ptr`. This call overwrites it with the size of the value. If the available
	/// space at `out_ptr` is less than the size of the value a trap is triggered.
	#[prefixed_alias]
	fn block_number(ctx: Runtime<E>, out_ptr: u32, out_len_ptr: u32) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::BlockNumber)?;
		Ok(ctx.write_sandbox_output(
			out_ptr,
			out_len_ptr,
			&ctx.ext.block_number().encode(),
			false,
			already_charged,
		)?)
	}

	/// Computes the SHA2 256-bit hash on the given input buffer.
	///
	/// Returns the result directly into the given output buffer.
	///
	/// # Note
	///
	/// - The `input` and `output` buffer may overlap.
	/// - The output buffer is expected to hold at least 32 bytes (256 bits).
	/// - It is the callers responsibility to provide an output buffer that is large enough to hold
	///   the expected amount of bytes returned by the chosen hash function.
	///
	/// # Parameters
	///
	/// - `input_ptr`: the pointer into the linear memory where the input data is placed.
	/// - `input_len`: the length of the input data in bytes.
	/// - `output_ptr`: the pointer into the linear memory where the output data is placed. The
	///   function will write the result directly into this buffer.
	#[prefixed_alias]
	fn hash_sha2_256(
		ctx: Runtime<E>,
		input_ptr: u32,
		input_len: u32,
		output_ptr: u32,
	) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::HashSha256(input_len))?;
		Ok(ctx.compute_hash_on_intermediate_buffer(sha2_256, input_ptr, input_len, output_ptr)?)
	}

	/// Computes the KECCAK 256-bit hash on the given input buffer.
	///
	/// Returns the result directly into the given output buffer.
	///
	/// # Note
	///
	/// - The `input` and `output` buffer may overlap.
	/// - The output buffer is expected to hold at least 32 bytes (256 bits).
	/// - It is the callers responsibility to provide an output buffer that is large enough to hold
	///   the expected amount of bytes returned by the chosen hash function.
	///
	/// # Parameters
	///
	/// - `input_ptr`: the pointer into the linear memory where the input data is placed.
	/// - `input_len`: the length of the input data in bytes.
	/// - `output_ptr`: the pointer into the linear memory where the output data is placed. The
	///   function will write the result directly into this buffer.
	#[prefixed_alias]
	fn hash_keccak_256(
		ctx: Runtime<E>,
		input_ptr: u32,
		input_len: u32,
		output_ptr: u32,
	) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::HashKeccak256(input_len))?;
		Ok(ctx.compute_hash_on_intermediate_buffer(keccak_256, input_ptr, input_len, output_ptr)?)
	}

	/// Computes the BLAKE2 256-bit hash on the given input buffer.
	///
	/// Returns the result directly into the given output buffer.
	///
	/// # Note
	///
	/// - The `input` and `output` buffer may overlap.
	/// - The output buffer is expected to hold at least 32 bytes (256 bits).
	/// - It is the callers responsibility to provide an output buffer that is large enough to hold
	///   the expected amount of bytes returned by the chosen hash function.
	///
	/// # Parameters
	///
	/// - `input_ptr`: the pointer into the linear memory where the input data is placed.
	/// - `input_len`: the length of the input data in bytes.
	/// - `output_ptr`: the pointer into the linear memory where the output data is placed. The
	///   function will write the result directly into this buffer.
	#[prefixed_alias]
	fn hash_blake2_256(
		ctx: Runtime<E>,
		input_ptr: u32,
		input_len: u32,
		output_ptr: u32,
	) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::HashBlake256(input_len))?;
		Ok(ctx.compute_hash_on_intermediate_buffer(blake2_256, input_ptr, input_len, output_ptr)?)
	}

	/// Computes the BLAKE2 128-bit hash on the given input buffer.
	///
	/// Returns the result directly into the given output buffer.
	///
	/// # Note
	///
	/// - The `input` and `output` buffer may overlap.
	/// - The output buffer is expected to hold at least 16 bytes (128 bits).
	/// - It is the callers responsibility to provide an output buffer that is large enough to hold
	///   the expected amount of bytes returned by the chosen hash function.
	///
	/// # Parameters
	///
	/// - `input_ptr`: the pointer into the linear memory where the input data is placed.
	/// - `input_len`: the length of the input data in bytes.
	/// - `output_ptr`: the pointer into the linear memory where the output data is placed. The
	///   function will write the result directly into this buffer.
	#[prefixed_alias]
	fn hash_blake2_128(
		ctx: Runtime<E>,
		input_ptr: u32,
		input_len: u32,
		output_ptr: u32,
	) -> Result<(), TrapReason> {
		ctx.charge_gas(RuntimeCosts::HashBlake128(input_len))?;
		Ok(ctx.compute_hash_on_intermediate_buffer(blake2_128, input_ptr, input_len, output_ptr)?)
	}

	/// Call into the chain extension provided by the chain if any.
	///
	/// Handling of the input values is up to the specific chain extension and so is the
	/// return value. The extension can decide to use the inputs as primitive inputs or as
	/// in/out arguments by interpreting them as pointers. Any caller of this function
	/// must therefore coordinate with the chain that it targets.
	///
	/// # Note
	///
	/// If no chain extension exists the contract will trap with the `NoChainExtension`
	/// module error.
	#[prefixed_alias]
	fn call_chain_extension(
		ctx: Runtime<E>,
		id: u32,
		input_ptr: u32,
		input_len: u32,
		output_ptr: u32,
		output_len_ptr: u32,
	) -> Result<u32, TrapReason> {
		use crate::chain_extension::{ChainExtension, Environment, RetVal};
		if !<E::T as Config>::ChainExtension::enabled() {
			return Err(Error::<E::T>::NoChainExtension.into())
		}
		let mut chain_extension = ctx.chain_extension.take().expect(
			"Constructor initializes with `Some`. This is the only place where it is set to `None`.\
			It is always reset to `Some` afterwards. qed"
		);
		let env = Environment::new(ctx, id, input_ptr, input_len, output_ptr, output_len_ptr);
		let ret = match chain_extension.call(env)? {
			RetVal::Converging(val) => Ok(val),
			RetVal::Diverging { flags, data } =>
				Err(TrapReason::Return(ReturnData { flags: flags.bits(), data })),
		};
		ctx.chain_extension = Some(chain_extension);
		ret
	}

	/// Emit a custom debug message.
	///
	/// No newlines are added to the supplied message.
	/// Specifying invalid UTF-8 triggers a trap.
	///
	/// This is a no-op if debug message recording is disabled which is always the case
	/// when the code is executing on-chain. The message is interpreted as UTF-8 and
	/// appended to the debug buffer which is then supplied to the calling RPC client.
	///
	/// # Note
	///
	/// Even though no action is taken when debug message recording is disabled there is still
	/// a non trivial overhead (and weight cost) associated with calling this function. Contract
	/// languages should remove calls to this function (either at runtime or compile time) when
	/// not being executed as an RPC. For example, they could allow users to disable logging
	/// through compile time flags (cargo features) for on-chain deployment. Additionally, the
	/// return value of this function can be cached in order to prevent further calls at runtime.
	#[prefixed_alias]
	fn debug_message(
		ctx: Runtime<E>,
		str_ptr: u32,
		str_len: u32,
	) -> Result<ReturnCode, TrapReason> {
		ctx.charge_gas(RuntimeCosts::DebugMessage)?;
		if ctx.ext.append_debug_buffer("") {
			let data = ctx.read_sandbox_memory(str_ptr, str_len)?;
			let msg =
				core::str::from_utf8(&data).map_err(|_| <Error<E::T>>::DebugMessageInvalidUTF8)?;
			ctx.ext.append_debug_buffer(msg);
			return Ok(ReturnCode::Success)
		}
		Ok(ReturnCode::LoggingDisabled)
	}

	/// Call some dispatchable of the runtime.
	///
	/// This function decodes the passed in data as the overarching `Call` type of the
	/// runtime and dispatches it. The weight as specified in the runtime is charged
	/// from the gas meter. Any weight refunds made by the dispatchable are considered.
	///
	/// The filter specified by `Config::CallFilter` is attached to the origin of
	/// the dispatched call.
	///
	/// # Parameters
	///
	/// - `input_ptr`: the pointer into the linear memory where the input data is placed.
	/// - `input_len`: the length of the input data in bytes.
	///
	/// # Return Value
	///
	/// Returns `ReturnCode::Success` when the dispatchable was succesfully executed and
	/// returned `Ok`. When the dispatchable was exeuted but returned an error
	/// `ReturnCode::CallRuntimeReturnedError` is returned. The full error is not
	/// provided because it is not guaranteed to be stable.
	///
	/// # Comparison with `ChainExtension`
	///
	/// Just as a chain extension this API allows the runtime to extend the functionality
	/// of contracts. While making use of this function is generelly easier it cannot be
	/// used in call cases. Consider writing a chain extension if you need to do perform
	/// one of the following tasks:
	///
	/// - Return data.
	/// - Provide functionality **exclusively** to contracts.
	/// - Provide custom weights.
	/// - Avoid the need to keep the `Call` data structure stable.
	///
	/// # Unstable
	///
	/// This function is unstable and subject to change (or removal) in the future. Do not
	/// deploy a contract using it to a production chain.
	#[unstable]
	#[prefixed_alias]
	fn call_runtime(
		ctx: Runtime<E>,
		call_ptr: u32,
		call_len: u32,
	) -> Result<ReturnCode, TrapReason> {
		use frame_support::dispatch::{extract_actual_weight, GetDispatchInfo};
		ctx.charge_gas(RuntimeCosts::CopyFromContract(call_len))?;
		let call: <E::T as Config>::RuntimeCall =
			ctx.read_sandbox_memory_as_unbounded(call_ptr, call_len)?;
		let dispatch_info = call.get_dispatch_info();
		let charged = ctx.charge_gas(RuntimeCosts::CallRuntime(dispatch_info.weight))?;
		let result = ctx.ext.call_runtime(call);
		let actual_weight = extract_actual_weight(&result, &dispatch_info);
		ctx.adjust_gas(charged, RuntimeCosts::CallRuntime(actual_weight));
		match result {
			Ok(_) => Ok(ReturnCode::Success),
			Err(_) => Ok(ReturnCode::CallRuntimeReturnedError),
		}
	}

	/// Recovers the ECDSA public key from the given message hash and signature.
	///
	/// Writes the public key into the given output buffer.
	/// Assumes the secp256k1 curve.
	///
	/// # Parameters
	///
	/// - `signature_ptr`: the pointer into the linear memory where the signature is placed. Should
	///   be decodable as a 65 bytes. Traps otherwise.
	/// - `message_hash_ptr`: the pointer into the linear memory where the message hash is placed.
	///   Should be decodable as a 32 bytes. Traps otherwise.
	/// - `output_ptr`: the pointer into the linear memory where the output data is placed. The
	///   buffer should be 33 bytes. The function will write the result directly into this buffer.
	///
	/// # Errors
	///
	/// `ReturnCode::EcdsaRecoverFailed`
	#[prefixed_alias]
	fn ecdsa_recover(
		ctx: Runtime<E>,
		signature_ptr: u32,
		message_hash_ptr: u32,
		output_ptr: u32,
	) -> Result<ReturnCode, TrapReason> {
		ctx.charge_gas(RuntimeCosts::EcdsaRecovery)?;

		let mut signature: [u8; 65] = [0; 65];
		ctx.read_sandbox_memory_into_buf(signature_ptr, &mut signature)?;
		let mut message_hash: [u8; 32] = [0; 32];
		ctx.read_sandbox_memory_into_buf(message_hash_ptr, &mut message_hash)?;

		let result = ctx.ext.ecdsa_recover(&signature, &message_hash);

		match result {
			Ok(pub_key) => {
				// Write the recovered compressed ecdsa public key back into the sandboxed output
				// buffer.
				ctx.write_sandbox_memory(output_ptr, pub_key.as_ref())?;

				Ok(ReturnCode::Success)
			},
			Err(_) => Ok(ReturnCode::EcdsaRecoverFailed),
		}
	}

	/// Replace the contract code at the specified address with new code.
	///
	/// # Note
	///
	/// There are a couple of important considerations which must be taken into account when
	/// using this API:
	///
	/// 1. The storage at the code address will remain untouched. This means that contract
	/// developers must ensure that the storage layout of the new code is compatible with that of
	/// the old code.
	///
	/// 2. Contracts using this API can't be assumed as having deterministic addresses. Said another
	/// way, when using this API you lose the guarantee that an address always identifies a specific
	/// code hash.
	/// 3. If a contract calls into itself after changing its code the new call would use
	/// the new code. However, if the original caller panics after returning from the sub call it
	/// would revert the changes made by `seal_set_code_hash` and the next caller would use
	/// the old code.
	///
	/// # Parameters
	///
	/// - `code_hash_ptr`: A pointer to the buffer that contains the new code hash.
	///
	/// # Errors
	///
	/// `ReturnCode::CodeNotFound`
	#[prefixed_alias]
	fn set_code_hash(ctx: Runtime<E>, code_hash_ptr: u32) -> Result<ReturnCode, TrapReason> {
		ctx.charge_gas(RuntimeCosts::SetCodeHash)?;
		let code_hash: CodeHash<<E as Ext>::T> = ctx.read_sandbox_memory_as(code_hash_ptr)?;
		match ctx.ext.set_code_hash(code_hash) {
			Err(err) => {
				let code = Runtime::<E>::err_into_return_code(err)?;
				Ok(code)
			},
			Ok(()) => Ok(ReturnCode::Success),
		}
	}

	/// Calculates Ethereum address from the ECDSA compressed public key and stores
	/// it into the supplied buffer.
	///
	/// # Parameters
	///
	/// - `key_ptr`: a pointer to the ECDSA compressed public key. Should be decodable as a 33 bytes
	///   value. Traps otherwise.
	/// - `out_ptr`: the pointer into the linear memory where the output data is placed. The
	///   function will write the result directly into this buffer.
	///
	/// The value is stored to linear memory at the address pointed to by `out_ptr`.
	/// If the available space at `out_ptr` is less than the size of the value a trap is triggered.
	///
	/// # Errors
	///
	/// `ReturnCode::EcdsaRecoverFailed`
	#[prefixed_alias]
	fn ecdsa_to_eth_address(
		ctx: Runtime<E>,
		key_ptr: u32,
		out_ptr: u32,
	) -> Result<ReturnCode, TrapReason> {
		ctx.charge_gas(RuntimeCosts::EcdsaToEthAddress)?;
		let mut compressed_key: [u8; 33] = [0; 33];
		ctx.read_sandbox_memory_into_buf(key_ptr, &mut compressed_key)?;
		let result = ctx.ext.ecdsa_to_eth_address(&compressed_key);
		match result {
			Ok(eth_address) => {
				ctx.write_sandbox_memory(out_ptr, eth_address.as_ref())?;
				Ok(ReturnCode::Success)
			},
			Err(_) => Ok(ReturnCode::EcdsaRecoverFailed),
		}
	}
}
