// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! This module provides a means for executing contracts
//! represented in wasm.

mod prepare;
mod runtime;

#[cfg(doc)]
pub use crate::wasm::runtime::api_doc;

#[cfg(test)]
pub use tests::MockExt;

pub use crate::wasm::runtime::{
	AllowDeprecatedInterface, AllowUnstableInterface, CallFlags, Environment, ReturnCode, Runtime,
	RuntimeCosts,
};

use crate::{
	exec::{ExecResult, Executable, ExportedFunction, Ext},
	gas::{GasMeter, Token},
	wasm::prepare::LoadedModule,
	weights::WeightInfo,
	AccountIdOf, BadOrigin, BalanceOf, CodeHash, CodeInfoOf, CodeVec, Config, Error, Event,
	HoldReason, Pallet, PristineCode, Schedule, Weight, LOG_TARGET,
};
use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	dispatch::DispatchResult,
	ensure,
	traits::{fungible::MutateHold, tokens::Precision::BestEffort},
};
use sp_core::Get;
use sp_runtime::{DispatchError, RuntimeDebug};
use sp_std::prelude::*;
use wasmi::{Instance, Linker, Memory, MemoryType, StackLimits, Store};

const BYTES_PER_PAGE: usize = 64 * 1024;

/// Validated Wasm module ready for execution.
/// This data structure is immutable once created and stored.
#[derive(Encode, Decode, scale_info::TypeInfo)]
#[codec(mel_bound())]
#[scale_info(skip_type_params(T))]
pub struct WasmBlob<T: Config> {
	code: CodeVec<T>,
	// This isn't needed for contract execution and is not stored alongside it.
	#[codec(skip)]
	code_info: CodeInfo<T>,
	// This is for not calculating the hash every time we need it.
	#[codec(skip)]
	code_hash: CodeHash<T>,
}

/// Contract code related data, such as:
///
/// - owner of the contract, i.e. account uploaded its code,
/// - storage deposit amount,
/// - reference count,
/// - determinism marker.
///
/// It is stored in a separate storage entry to avoid loading the code when not necessary.
#[derive(Clone, Encode, Decode, scale_info::TypeInfo, MaxEncodedLen)]
#[codec(mel_bound())]
#[scale_info(skip_type_params(T))]
pub struct CodeInfo<T: Config> {
	/// The account that has uploaded the contract code and hence is allowed to remove it.
	owner: AccountIdOf<T>,
	/// The amount of balance that was deposited by the owner in order to store it on-chain.
	#[codec(compact)]
	deposit: BalanceOf<T>,
	/// The number of instantiated contracts that use this as their code.
	#[codec(compact)]
	refcount: u64,
	/// Marks if the code might contain non-deterministic features and is therefore never allowed
	/// to be run on-chain. Specifically, such a code can never be instantiated into a contract
	/// and can just be used through a delegate call.
	determinism: Determinism,
	/// length of the code in bytes.
	code_len: u32,
}

/// Defines the required determinism level of a wasm blob when either running or uploading code.
#[derive(
	Clone, Copy, Encode, Decode, scale_info::TypeInfo, MaxEncodedLen, RuntimeDebug, PartialEq, Eq,
)]
pub enum Determinism {
	/// The execution should be deterministic and hence no indeterministic instructions are
	/// allowed.
	///
	/// Dispatchables always use this mode in order to make on-chain execution deterministic.
	Enforced,
	/// Allow calling or uploading an indeterministic code.
	///
	/// This is only possible when calling into `pallet-contracts` directly via
	/// [`crate::Pallet::bare_call`].
	///
	/// # Note
	///
	/// **Never** use this mode for on-chain execution.
	Relaxed,
}

impl ExportedFunction {
	/// The wasm export name for the function.
	fn identifier(&self) -> &str {
		match self {
			Self::Constructor => "deploy",
			Self::Call => "call",
		}
	}
}

/// Cost of code loading from storage.
#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
struct CodeLoadToken(u32);

impl<T: Config> Token<T> for CodeLoadToken {
	fn weight(&self) -> Weight {
		// When loading the contract, we already covered the general costs of
		// calling the storage but still need to account for the actual size of the
		// contract code. This is why we subtract `T::*::(0)`. We need to do this at this
		// point because when charging the general weight for calling the contract we don't know the
		// size of the contract.
		T::WeightInfo::call_with_code_per_byte(self.0)
			.saturating_sub(T::WeightInfo::call_with_code_per_byte(0))
	}
}

impl<T: Config> WasmBlob<T> {
	/// Create the module by checking the `code`.
	pub fn from_code(
		code: Vec<u8>,
		schedule: &Schedule<T>,
		owner: AccountIdOf<T>,
		determinism: Determinism,
	) -> Result<Self, (DispatchError, &'static str)> {
		prepare::prepare::<runtime::Env, T>(
			code.try_into().map_err(|_| (<Error<T>>::CodeTooLarge.into(), ""))?,
			schedule,
			owner,
			determinism,
		)
	}

	/// Remove the code from storage and refund the deposit to its owner.
	///
	/// Applies all necessary checks before removing the code.
	pub fn remove(origin: &T::AccountId, code_hash: CodeHash<T>) -> DispatchResult {
		Self::try_remove_code(origin, code_hash)
	}

	/// Creates and returns an instance of the supplied code.
	///
	/// This is either used for later executing a contract or for validation of a contract.
	/// When validating we pass `()` as `host_state`. Please note that such a dummy instance must
	/// **never** be called/executed, since it will panic the executor.
	pub fn instantiate<E, H>(
		code: &[u8],
		host_state: H,
		schedule: &Schedule<T>,
		determinism: Determinism,
		stack_limits: StackLimits,
		allow_deprecated: AllowDeprecatedInterface,
	) -> Result<(Store<H>, Memory, Instance), &'static str>
	where
		E: Environment<H>,
	{
		let contract = LoadedModule::new::<T>(&code, determinism, Some(stack_limits))?;
		let mut store = Store::new(&contract.engine, host_state);
		let mut linker = Linker::new(&contract.engine);
		E::define(
			&mut store,
			&mut linker,
			if T::UnsafeUnstableInterface::get() {
				AllowUnstableInterface::Yes
			} else {
				AllowUnstableInterface::No
			},
			allow_deprecated,
		)
		.map_err(|_| "can't define host functions to Linker")?;

		// Query wasmi for memory limits specified in the module's import entry.
		let memory_limits = contract.scan_imports::<T>(schedule)?;
		// Here we allocate this memory in the _store_. It allocates _inital_ value, but allows it
		// to grow up to maximum number of memory pages, if necessary.
		let qed = "We checked the limits versus our Schedule,
					 which specifies the max amount of memory pages
					 well below u16::MAX; qed";
		let memory = Memory::new(
			&mut store,
			MemoryType::new(memory_limits.0, Some(memory_limits.1)).expect(qed),
		)
		.expect(qed);

		linker
			.define("env", "memory", memory)
			.expect("We just created the Linker. It has no definitions with this name; qed");

		let instance = linker
			.instantiate(&mut store, &contract.module)
			.map_err(|_| "can't instantiate module with provided definitions")?
			.ensure_no_start(&mut store)
			.map_err(|_| "start function is forbidden but found in the module")?;

		Ok((store, memory, instance))
	}

	/// Puts the module blob into storage, and returns the deposit collected for the storage.
	pub fn store_code(&mut self) -> Result<BalanceOf<T>, Error<T>> {
		let code_hash = *self.code_hash();
		<CodeInfoOf<T>>::mutate(code_hash, |stored_code_info| {
			match stored_code_info {
				// Contract code is already stored in storage. Nothing to be done here.
				Some(_) => Ok(Default::default()),
				// Upload a new contract code.
				// We need to store the code and its code_info, and collect the deposit.
				// This `None` case happens only with freshly uploaded modules. This means that
				// the `owner` is always the origin of the current transaction.
				None => {
					let deposit = self.code_info.deposit;
					T::Currency::hold(
						&HoldReason::CodeUploadDepositReserve.into(),
						&self.code_info.owner,
						deposit,
					)
					.map_err(|_| <Error<T>>::StorageDepositNotEnoughFunds)?;

					self.code_info.refcount = 0;
					<PristineCode<T>>::insert(code_hash, &self.code);
					*stored_code_info = Some(self.code_info.clone());
					<Pallet<T>>::deposit_event(
						vec![code_hash],
						Event::CodeStored {
							code_hash,
							deposit_held: deposit,
							uploader: self.code_info.owner.clone(),
						},
					);
					Ok(deposit)
				},
			}
		})
	}

	/// Try to remove code together with all associated information.
	fn try_remove_code(origin: &T::AccountId, code_hash: CodeHash<T>) -> DispatchResult {
		<CodeInfoOf<T>>::try_mutate_exists(&code_hash, |existing| {
			if let Some(code_info) = existing {
				ensure!(code_info.refcount == 0, <Error<T>>::CodeInUse);
				ensure!(&code_info.owner == origin, BadOrigin);
				let _ = T::Currency::release(
					&HoldReason::CodeUploadDepositReserve.into(),
					&code_info.owner,
					code_info.deposit,
					BestEffort,
				);
				let deposit_released = code_info.deposit;
				let remover = code_info.owner.clone();

				*existing = None;
				<PristineCode<T>>::remove(&code_hash);
				<Pallet<T>>::deposit_event(
					vec![code_hash],
					Event::CodeRemoved { code_hash, deposit_released, remover },
				);
				Ok(())
			} else {
				Err(<Error<T>>::CodeNotFound.into())
			}
		})
	}

	/// Load code with the given code hash.
	fn load_code(
		code_hash: CodeHash<T>,
		gas_meter: &mut GasMeter<T>,
	) -> Result<(CodeVec<T>, CodeInfo<T>), DispatchError> {
		let code_info = <CodeInfoOf<T>>::get(code_hash).ok_or(Error::<T>::CodeNotFound)?;
		gas_meter.charge(CodeLoadToken(code_info.code_len))?;
		let code = <PristineCode<T>>::get(code_hash).ok_or(Error::<T>::CodeNotFound)?;
		Ok((code, code_info))
	}

	/// Create the module without checking the passed code.
	///
	/// # Note
	///
	/// This is useful for benchmarking where we don't want validation of the module to skew
	/// our results. This also does not collect any deposit from the `owner`. Also useful
	/// during testing when we want to deploy codes that do not pass the instantiation checks.
	#[cfg(any(test, feature = "runtime-benchmarks"))]
	pub fn from_code_unchecked(
		code: Vec<u8>,
		schedule: &Schedule<T>,
		owner: T::AccountId,
	) -> Result<Self, DispatchError> {
		prepare::benchmarking::prepare(code, schedule, owner)
	}
}

impl<T: Config> CodeInfo<T> {
	/// Return the refcount of the module.
	#[cfg(test)]
	pub fn refcount(&self) -> u64 {
		self.refcount
	}

	#[cfg(test)]
	pub fn new(owner: T::AccountId) -> Self {
		CodeInfo {
			owner,
			deposit: Default::default(),
			refcount: 0,
			code_len: 0,
			determinism: Determinism::Enforced,
		}
	}

	/// Returns the deposit of the module.
	pub fn deposit(&self) -> BalanceOf<T> {
		self.deposit
	}
}

impl<T: Config> Executable<T> for WasmBlob<T> {
	fn from_storage(
		code_hash: CodeHash<T>,
		gas_meter: &mut GasMeter<T>,
	) -> Result<Self, DispatchError> {
		let (code, code_info) = Self::load_code(code_hash, gas_meter)?;
		Ok(Self { code, code_info, code_hash })
	}

	fn increment_refcount(code_hash: CodeHash<T>) -> Result<(), DispatchError> {
		<CodeInfoOf<T>>::mutate(code_hash, |existing| -> Result<(), DispatchError> {
			if let Some(info) = existing {
				info.refcount = info.refcount.saturating_add(1);
				Ok(())
			} else {
				Err(Error::<T>::CodeNotFound.into())
			}
		})
	}

	fn decrement_refcount(code_hash: CodeHash<T>) {
		<CodeInfoOf<T>>::mutate(code_hash, |existing| {
			if let Some(info) = existing {
				info.refcount = info.refcount.saturating_sub(1);
			}
		});
	}

	fn execute<E: Ext<T = T>>(
		self,
		ext: &mut E,
		function: &ExportedFunction,
		input_data: Vec<u8>,
	) -> ExecResult {
		let code = self.code.as_slice();
		// Instantiate the Wasm module to the engine.
		let runtime = Runtime::new(ext, input_data);
		let schedule = <T>::Schedule::get();
		let (mut store, memory, instance) = Self::instantiate::<crate::wasm::runtime::Env, _>(
			code,
			runtime,
			&schedule,
			self.code_info.determinism,
			StackLimits::default(),
			match function {
				ExportedFunction::Call => AllowDeprecatedInterface::Yes,
				ExportedFunction::Constructor => AllowDeprecatedInterface::No,
			},
		)
		.map_err(|msg| {
			log::debug!(target: LOG_TARGET, "failed to instantiate code to wasmi: {}", msg);
			Error::<T>::CodeRejected
		})?;
		store.data_mut().set_memory(memory);

		// Set fuel limit for the wasmi execution.
		// We normalize it by the base instruction weight, as its cost in wasmi engine is `1`.
		let fuel_limit = store
			.data_mut()
			.ext()
			.gas_meter_mut()
			.gas_left()
			.ref_time()
			.checked_div(T::Schedule::get().instruction_weights.base as u64)
			.ok_or(Error::<T>::InvalidSchedule)?;
		store
			.add_fuel(fuel_limit)
			.expect("We've set up engine to fuel consuming mode; qed");

		let exported_func = instance
			.get_export(&store, function.identifier())
			.and_then(|export| export.into_func())
			.ok_or_else(|| {
				log::error!(target: LOG_TARGET, "failed to find entry point");
				Error::<T>::CodeRejected
			})?;

		if let &ExportedFunction::Constructor = function {
			WasmBlob::<T>::increment_refcount(self.code_hash)?;
		}

		let result = exported_func.call(&mut store, &[], &mut []);
		let engine_consumed_total = store.fuel_consumed().expect("Fuel metering is enabled; qed");
		// Sync this frame's gas meter with the engine's one.
		let gas_meter = store.data_mut().ext().gas_meter_mut();
		gas_meter.charge_fuel(engine_consumed_total)?;

		store.into_data().to_execution_result(result)
	}

	fn code_hash(&self) -> &CodeHash<T> {
		&self.code_hash
	}

	fn code_info(&self) -> &CodeInfo<T> {
		&self.code_info
	}

	fn code_len(&self) -> u32 {
		self.code.len() as u32
	}

	fn is_deterministic(&self) -> bool {
		matches!(self.code_info.determinism, Determinism::Enforced)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		exec::{AccountIdOf, ErrorOrigin, ExecError, Executable, Ext, Key, SeedOf},
		gas::GasMeter,
		storage::WriteOutcome,
		tests::{RuntimeCall, Test, ALICE, BOB},
		BalanceOf, CodeHash, Error, Origin, Pallet as Contracts,
	};
	use assert_matches::assert_matches;
	use frame_support::{
		assert_err, assert_ok, dispatch::DispatchResultWithPostInfo, weights::Weight,
	};
	use frame_system::pallet_prelude::BlockNumberFor;
	use pallet_contracts_primitives::{ExecReturnValue, ReturnFlags};
	use pretty_assertions::assert_eq;
	use sp_core::H256;
	use sp_runtime::DispatchError;
	use std::{
		borrow::BorrowMut,
		cell::RefCell,
		collections::{
			hash_map::{Entry, HashMap},
			HashSet,
		},
	};

	#[derive(Debug, PartialEq, Eq)]
	struct InstantiateEntry {
		code_hash: H256,
		value: u64,
		data: Vec<u8>,
		gas_left: u64,
		salt: Vec<u8>,
	}

	#[derive(Debug, PartialEq, Eq)]
	struct TerminationEntry {
		beneficiary: AccountIdOf<Test>,
	}

	#[derive(Debug, PartialEq, Eq)]
	struct TransferEntry {
		to: AccountIdOf<Test>,
		value: u64,
	}

	#[derive(Debug, PartialEq, Eq)]
	struct CallEntry {
		to: AccountIdOf<Test>,
		value: u64,
		data: Vec<u8>,
		allows_reentry: bool,
	}

	#[derive(Debug, PartialEq, Eq)]
	struct CallCodeEntry {
		code_hash: H256,
		data: Vec<u8>,
	}

	pub struct MockExt {
		storage: HashMap<Vec<u8>, Vec<u8>>,
		instantiates: Vec<InstantiateEntry>,
		terminations: Vec<TerminationEntry>,
		calls: Vec<CallEntry>,
		code_calls: Vec<CallCodeEntry>,
		transfers: Vec<TransferEntry>,
		// (topics, data)
		events: Vec<(Vec<H256>, Vec<u8>)>,
		runtime_calls: RefCell<Vec<RuntimeCall>>,
		schedule: Schedule<Test>,
		gas_meter: GasMeter<Test>,
		debug_buffer: Vec<u8>,
		ecdsa_recover: RefCell<Vec<([u8; 65], [u8; 32])>>,
		sr25519_verify: RefCell<Vec<([u8; 64], Vec<u8>, [u8; 32])>>,
		code_hashes: Vec<CodeHash<Test>>,
		caller: Origin<Test>,
		delegate_dependencies: RefCell<HashSet<CodeHash<Test>>>,
	}

	/// The call is mocked and just returns this hardcoded value.
	fn call_return_data() -> Vec<u8> {
		vec![0xDE, 0xAD, 0xBE, 0xEF]
	}

	impl Default for MockExt {
		fn default() -> Self {
			Self {
				code_hashes: Default::default(),
				storage: Default::default(),
				instantiates: Default::default(),
				terminations: Default::default(),
				calls: Default::default(),
				code_calls: Default::default(),
				transfers: Default::default(),
				events: Default::default(),
				runtime_calls: Default::default(),
				schedule: Default::default(),
				gas_meter: GasMeter::new(Weight::from_parts(10_000_000_000, 10 * 1024 * 1024)),
				debug_buffer: Default::default(),
				ecdsa_recover: Default::default(),
				caller: Default::default(),
				sr25519_verify: Default::default(),
				delegate_dependencies: Default::default(),
			}
		}
	}

	impl Ext for MockExt {
		type T = Test;

		fn call(
			&mut self,
			_gas_limit: Weight,
			_deposit_limit: BalanceOf<Self::T>,
			to: AccountIdOf<Self::T>,
			value: u64,
			data: Vec<u8>,
			allows_reentry: bool,
		) -> Result<ExecReturnValue, ExecError> {
			self.calls.push(CallEntry { to, value, data, allows_reentry });
			Ok(ExecReturnValue { flags: ReturnFlags::empty(), data: call_return_data() })
		}
		fn delegate_call(
			&mut self,
			code_hash: CodeHash<Self::T>,
			data: Vec<u8>,
		) -> Result<ExecReturnValue, ExecError> {
			self.code_calls.push(CallCodeEntry { code_hash, data });
			Ok(ExecReturnValue { flags: ReturnFlags::empty(), data: call_return_data() })
		}
		fn instantiate(
			&mut self,
			gas_limit: Weight,
			_deposit_limit: BalanceOf<Self::T>,
			code_hash: CodeHash<Test>,
			value: u64,
			data: Vec<u8>,
			salt: &[u8],
		) -> Result<(AccountIdOf<Self::T>, ExecReturnValue), ExecError> {
			self.instantiates.push(InstantiateEntry {
				code_hash,
				value,
				data: data.to_vec(),
				gas_left: gas_limit.ref_time(),
				salt: salt.to_vec(),
			});
			Ok((
				Contracts::<Test>::contract_address(&ALICE, &code_hash, &data, salt),
				ExecReturnValue { flags: ReturnFlags::empty(), data: Vec::new() },
			))
		}
		fn set_code_hash(&mut self, hash: CodeHash<Self::T>) -> Result<(), DispatchError> {
			self.code_hashes.push(hash);
			Ok(())
		}
		fn transfer(&mut self, to: &AccountIdOf<Self::T>, value: u64) -> Result<(), DispatchError> {
			self.transfers.push(TransferEntry { to: to.clone(), value });
			Ok(())
		}
		fn terminate(&mut self, beneficiary: &AccountIdOf<Self::T>) -> Result<(), DispatchError> {
			self.terminations.push(TerminationEntry { beneficiary: beneficiary.clone() });
			Ok(())
		}
		fn get_storage(&mut self, key: &Key<Self::T>) -> Option<Vec<u8>> {
			self.storage.get(&key.to_vec()).cloned()
		}
		fn get_storage_size(&mut self, key: &Key<Self::T>) -> Option<u32> {
			self.storage.get(&key.to_vec()).map(|val| val.len() as u32)
		}
		fn set_storage(
			&mut self,
			key: &Key<Self::T>,
			value: Option<Vec<u8>>,
			take_old: bool,
		) -> Result<WriteOutcome, DispatchError> {
			let key = key.to_vec();
			let entry = self.storage.entry(key.clone());
			let result = match (entry, take_old) {
				(Entry::Vacant(_), _) => WriteOutcome::New,
				(Entry::Occupied(entry), false) =>
					WriteOutcome::Overwritten(entry.remove().len() as u32),
				(Entry::Occupied(entry), true) => WriteOutcome::Taken(entry.remove()),
			};
			if let Some(value) = value {
				self.storage.insert(key, value);
			}
			Ok(result)
		}
		fn caller(&self) -> Origin<Self::T> {
			self.caller.clone()
		}
		fn is_contract(&self, _address: &AccountIdOf<Self::T>) -> bool {
			true
		}
		fn code_hash(&self, _address: &AccountIdOf<Self::T>) -> Option<CodeHash<Self::T>> {
			Some(H256::from_slice(&[0x11; 32]))
		}
		fn own_code_hash(&mut self) -> &CodeHash<Self::T> {
			const HASH: H256 = H256::repeat_byte(0x10);
			&HASH
		}
		fn caller_is_origin(&self) -> bool {
			false
		}
		fn caller_is_root(&self) -> bool {
			&self.caller == &Origin::Root
		}
		fn address(&self) -> &AccountIdOf<Self::T> {
			&BOB
		}
		fn balance(&self) -> u64 {
			228
		}
		fn value_transferred(&self) -> u64 {
			1337
		}
		fn now(&self) -> &u64 {
			&1111
		}
		fn minimum_balance(&self) -> u64 {
			666
		}
		fn random(&self, subject: &[u8]) -> (SeedOf<Self::T>, BlockNumberFor<Self::T>) {
			(H256::from_slice(subject), 42)
		}
		fn deposit_event(&mut self, topics: Vec<H256>, data: Vec<u8>) {
			self.events.push((topics, data))
		}
		fn block_number(&self) -> u64 {
			121
		}
		fn max_value_size(&self) -> u32 {
			16_384
		}
		fn get_weight_price(&self, weight: Weight) -> BalanceOf<Self::T> {
			BalanceOf::<Self::T>::from(1312_u32)
				.saturating_mul(weight.ref_time().into())
				.saturating_add(
					BalanceOf::<Self::T>::from(103_u32).saturating_mul(weight.proof_size()),
				)
		}
		fn schedule(&self) -> &Schedule<Self::T> {
			&self.schedule
		}
		fn gas_meter(&self) -> &GasMeter<Self::T> {
			&self.gas_meter
		}
		fn gas_meter_mut(&mut self) -> &mut GasMeter<Self::T> {
			&mut self.gas_meter
		}
		fn charge_storage(&mut self, _diff: &crate::storage::meter::Diff) {}
		fn append_debug_buffer(&mut self, msg: &str) -> bool {
			self.debug_buffer.extend(msg.as_bytes());
			true
		}
		fn call_runtime(
			&self,
			call: <Self::T as Config>::RuntimeCall,
		) -> DispatchResultWithPostInfo {
			self.runtime_calls.borrow_mut().push(call);
			Ok(Default::default())
		}
		fn ecdsa_recover(
			&self,
			signature: &[u8; 65],
			message_hash: &[u8; 32],
		) -> Result<[u8; 33], ()> {
			self.ecdsa_recover.borrow_mut().push((*signature, *message_hash));
			Ok([3; 33])
		}
		fn sr25519_verify(&self, signature: &[u8; 64], message: &[u8], pub_key: &[u8; 32]) -> bool {
			self.sr25519_verify.borrow_mut().push((*signature, message.to_vec(), *pub_key));
			true
		}
		fn contract_info(&mut self) -> &mut crate::ContractInfo<Self::T> {
			unimplemented!()
		}
		fn ecdsa_to_eth_address(&self, _pk: &[u8; 33]) -> Result<[u8; 20], ()> {
			Ok([2u8; 20])
		}
		fn reentrance_count(&self) -> u32 {
			12
		}
		fn account_reentrance_count(&self, _account_id: &AccountIdOf<Self::T>) -> u32 {
			12
		}
		fn nonce(&mut self) -> u64 {
			995
		}

		fn add_delegate_dependency(
			&mut self,
			code: CodeHash<Self::T>,
		) -> Result<(), DispatchError> {
			self.delegate_dependencies.borrow_mut().insert(code);
			Ok(())
		}

		fn remove_delegate_dependency(
			&mut self,
			code: &CodeHash<Self::T>,
		) -> Result<(), DispatchError> {
			self.delegate_dependencies.borrow_mut().remove(code);
			Ok(())
		}
	}

	/// Execute the supplied code.
	///
	/// Not used directly but through the wrapper functions defined below.
	fn execute_internal<E: BorrowMut<MockExt>>(
		wat: &str,
		input_data: Vec<u8>,
		mut ext: E,
		entry_point: &ExportedFunction,
		unstable_interface: bool,
		skip_checks: bool,
	) -> ExecResult {
		type RuntimeConfig = <MockExt as Ext>::T;
		RuntimeConfig::set_unstable_interface(unstable_interface);
		let wasm = wat::parse_str(wat).unwrap();
		let executable = if skip_checks {
			WasmBlob::<RuntimeConfig>::from_code_unchecked(
				wasm,
				ext.borrow_mut().schedule(),
				ALICE,
			)?
		} else {
			WasmBlob::<RuntimeConfig>::from_code(
				wasm,
				ext.borrow_mut().schedule(),
				ALICE,
				Determinism::Enforced,
			)
			.map_err(|err| err.0)?
		};
		executable.execute(ext.borrow_mut(), entry_point, input_data)
	}

	/// Execute the supplied code.
	fn execute<E: BorrowMut<MockExt>>(wat: &str, input_data: Vec<u8>, ext: E) -> ExecResult {
		execute_internal(wat, input_data, ext, &ExportedFunction::Call, true, false)
	}

	/// Execute the supplied code with disabled unstable functions.
	///
	/// In our test config unstable functions are disabled so that we can test them.
	/// In order to test that code using them is properly rejected we temporarily disable
	/// them when this test is run.
	#[cfg(not(feature = "runtime-benchmarks"))]
	fn execute_no_unstable<E: BorrowMut<MockExt>>(
		wat: &str,
		input_data: Vec<u8>,
		ext: E,
	) -> ExecResult {
		execute_internal(wat, input_data, ext, &ExportedFunction::Call, false, false)
	}

	/// Execute code without validating it first.
	///
	/// This is mainly useful in order to test code which uses deprecated functions. Those
	/// would fail when validating the code.
	fn execute_unvalidated<E: BorrowMut<MockExt>>(
		wat: &str,
		input_data: Vec<u8>,
		ext: E,
	) -> ExecResult {
		execute_internal(wat, input_data, ext, &ExportedFunction::Call, false, true)
	}

	/// Execute instantiation entry point of code without validating it first.
	///
	/// Same as `execute_unvalidated` except that the `deploy` entry point is ran.
	#[cfg(not(feature = "runtime-benchmarks"))]
	fn execute_instantiate_unvalidated<E: BorrowMut<MockExt>>(
		wat: &str,
		input_data: Vec<u8>,
		ext: E,
	) -> ExecResult {
		execute_internal(wat, input_data, ext, &ExportedFunction::Constructor, false, true)
	}

	const CODE_TRANSFER: &str = r#"
(module
	;; seal_transfer(
	;;    account_ptr: u32,
	;;    account_len: u32,
	;;    value_ptr: u32,
	;;    value_len: u32,
	;;) -> u32
	(import "seal0" "seal_transfer" (func $seal_transfer (param i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $seal_transfer
				(i32.const 4)  ;; Pointer to "account" address.
				(i32.const 32)  ;; Length of "account" address.
				(i32.const 36) ;; Pointer to the buffer with value to transfer
				(i32.const 8)  ;; Length of the buffer with value to transfer.
			)
		)
	)
	(func (export "deploy"))

	;; Destination AccountId (ALICE)
	(data (i32.const 4)
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
	)

	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 36) "\99\00\00\00\00\00\00\00")
)
"#;

	#[test]
	fn contract_transfer() {
		let mut mock_ext = MockExt::default();
		assert_ok!(execute(CODE_TRANSFER, vec![], &mut mock_ext));

		assert_eq!(&mock_ext.transfers, &[TransferEntry { to: ALICE, value: 153 }]);
	}

	const CODE_CALL: &str = r#"
(module
	;; seal_call(
	;;    callee_ptr: u32,
	;;    callee_len: u32,
	;;    gas: u64,
	;;    value_ptr: u32,
	;;    value_len: u32,
	;;    input_data_ptr: u32,
	;;    input_data_len: u32,
	;;    output_ptr: u32,
	;;    output_len_ptr: u32
	;;) -> u32
	(import "seal0" "seal_call" (func $seal_call (param i32 i32 i64 i32 i32 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $seal_call
				(i32.const 4)  ;; Pointer to "callee" address.
				(i32.const 32)  ;; Length of "callee" address.
				(i64.const 0)  ;; How much gas to devote for the execution. 0 = all.
				(i32.const 36) ;; Pointer to the buffer with value to transfer
				(i32.const 8)  ;; Length of the buffer with value to transfer.
				(i32.const 44) ;; Pointer to input data buffer address
				(i32.const 4)  ;; Length of input data buffer
				(i32.const 4294967295) ;; u32 max value is the sentinel value: do not copy output
				(i32.const 0) ;; Length is ignored in this case
			)
		)
	)
	(func (export "deploy"))

	;; Destination AccountId (ALICE)
	(data (i32.const 4)
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
	)

	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 36) "\06\00\00\00\00\00\00\00")

	(data (i32.const 44) "\01\02\03\04")
)
"#;

	#[test]
	fn contract_call() {
		let mut mock_ext = MockExt::default();
		assert_ok!(execute(CODE_CALL, vec![], &mut mock_ext));

		assert_eq!(
			&mock_ext.calls,
			&[CallEntry { to: ALICE, value: 6, data: vec![1, 2, 3, 4], allows_reentry: true }]
		);
	}

	#[test]
	fn contract_delegate_call() {
		const CODE: &str = r#"
(module
	;; seal_delegate_call(
	;;    flags: u32,
	;;    code_hash_ptr: u32,
	;;    input_data_ptr: u32,
	;;    input_data_len: u32,
	;;    output_ptr: u32,
	;;    output_len_ptr: u32
	;;) -> u32
	(import "seal0" "seal_delegate_call" (func $seal_delegate_call (param i32 i32 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $seal_delegate_call
				(i32.const 0) ;; No flags are set
				(i32.const 4)  ;; Pointer to "callee" code_hash.
				(i32.const 36) ;; Pointer to input data buffer address
				(i32.const 4)  ;; Length of input data buffer
				(i32.const 4294967295) ;; u32 max value is the sentinel value: do not copy output
				(i32.const 0) ;; Length is ignored in this case
			)
		)
	)
	(func (export "deploy"))

	;; Callee code_hash
	(data (i32.const 4)
		"\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11"
		"\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11"
	)

	(data (i32.const 36) "\01\02\03\04")
)
"#;
		let mut mock_ext = MockExt::default();
		assert_ok!(execute(CODE, vec![], &mut mock_ext));

		assert_eq!(
			&mock_ext.code_calls,
			&[CallCodeEntry { code_hash: [0x11; 32].into(), data: vec![1, 2, 3, 4] }]
		);
	}

	#[test]
	fn contract_call_forward_input() {
		const CODE: &str = r#"
(module
	(import "seal1" "seal_call" (func $seal_call (param i32 i32 i64 i32 i32 i32 i32 i32) (result i32)))
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $seal_call
				(i32.const 1) ;; Set FORWARD_INPUT bit
				(i32.const 4)  ;; Pointer to "callee" address.
				(i64.const 0)  ;; How much gas to devote for the execution. 0 = all.
				(i32.const 36) ;; Pointer to the buffer with value to transfer
				(i32.const 44) ;; Pointer to input data buffer address
				(i32.const 4)  ;; Length of input data buffer
				(i32.const 4294967295) ;; u32 max value is the sentinel value: do not copy output
				(i32.const 0) ;; Length is ignored in this case
			)
		)

		;; triggers a trap because we already forwarded the input
		(call $seal_input (i32.const 1) (i32.const 44))
	)

	(func (export "deploy"))

	;; Destination AccountId (ALICE)
	(data (i32.const 4)
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
	)

	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 36) "\2A\00\00\00\00\00\00\00")

	;; The input is ignored because we forward our own input
	(data (i32.const 44) "\01\02\03\04")
)
"#;
		let mut mock_ext = MockExt::default();
		let input = vec![0xff, 0x2a, 0x99, 0x88];
		assert_err!(execute(CODE, input.clone(), &mut mock_ext), <Error<Test>>::InputForwarded,);

		assert_eq!(
			&mock_ext.calls,
			&[CallEntry { to: ALICE, value: 0x2a, data: input, allows_reentry: false }]
		);
	}

	#[test]
	fn contract_call_clone_input() {
		const CODE: &str = r#"
(module
	(import "seal1" "seal_call" (func $seal_call (param i32 i32 i64 i32 i32 i32 i32 i32) (result i32)))
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $seal_call
				(i32.const 11) ;; Set FORWARD_INPUT | CLONE_INPUT | ALLOW_REENTRY bits
				(i32.const 4)  ;; Pointer to "callee" address.
				(i64.const 0)  ;; How much gas to devote for the execution. 0 = all.
				(i32.const 36) ;; Pointer to the buffer with value to transfer
				(i32.const 44) ;; Pointer to input data buffer address
				(i32.const 4)  ;; Length of input data buffer
				(i32.const 4294967295) ;; u32 max value is the sentinel value: do not copy output
				(i32.const 0) ;; Length is ignored in this case
			)
		)

		;; works because the input was cloned
		(call $seal_input (i32.const 0) (i32.const 44))

		;; return the input to caller for inspection
		(call $seal_return (i32.const 0) (i32.const 0) (i32.load (i32.const 44)))
	)

	(func (export "deploy"))

	;; Destination AccountId (ALICE)
	(data (i32.const 4)
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
	)

	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 36) "\2A\00\00\00\00\00\00\00")

	;; The input is ignored because we forward our own input
	(data (i32.const 44) "\01\02\03\04")
)
"#;
		let mut mock_ext = MockExt::default();
		let input = vec![0xff, 0x2a, 0x99, 0x88];
		let result = execute(CODE, input.clone(), &mut mock_ext).unwrap();
		assert_eq!(result.data, input);
		assert_eq!(
			&mock_ext.calls,
			&[CallEntry { to: ALICE, value: 0x2a, data: input, allows_reentry: true }]
		);
	}

	#[test]
	fn contract_call_tail_call() {
		const CODE: &str = r#"
(module
	(import "seal1" "seal_call" (func $seal_call (param i32 i32 i64 i32 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $seal_call
				(i32.const 5) ;; Set FORWARD_INPUT | TAIL_CALL bit
				(i32.const 4)  ;; Pointer to "callee" address.
				(i64.const 0)  ;; How much gas to devote for the execution. 0 = all.
				(i32.const 36) ;; Pointer to the buffer with value to transfer
				(i32.const 0) ;; Pointer to input data buffer address
				(i32.const 0)  ;; Length of input data buffer
				(i32.const 4294967295) ;; u32 max value is the sentinel value: do not copy output
				(i32.const 0) ;; Length is ignored in this case
			)
		)

		;; a tail call never returns
		(unreachable)
	)

	(func (export "deploy"))

	;; Destination AccountId (ALICE)
	(data (i32.const 4)
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
	)

	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 36) "\2A\00\00\00\00\00\00\00")
)
"#;
		let mut mock_ext = MockExt::default();
		let input = vec![0xff, 0x2a, 0x99, 0x88];
		let result = execute(CODE, input.clone(), &mut mock_ext).unwrap();
		assert_eq!(result.data, call_return_data());
		assert_eq!(
			&mock_ext.calls,
			&[CallEntry { to: ALICE, value: 0x2a, data: input, allows_reentry: false }]
		);
	}

	#[test]
	fn contains_storage_works() {
		const CODE: &str = r#"
(module
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal1" "contains_storage" (func $contains_storage (param i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))


	;; size of input buffer
	;; [0, 4) size of input buffer (128+32 = 160 bytes = 0xA0)
	(data (i32.const 0) "\A0")

	;; [4, 164) input buffer

	(func (export "call")
		;; Receive key
		(call $seal_input
			(i32.const 4)	;; Where we take input and store it
			(i32.const 0)	;; Where we take and store the length of the data
		)
		;; Call seal_clear_storage and save what it returns at 0
		(i32.store (i32.const 0)
			(call $contains_storage
				(i32.const 8)			;; key_ptr
				(i32.load (i32.const 4))	;; key_len
			)
		)
		(call $seal_return
			(i32.const 0)	;; flags
			(i32.const 0)	;; returned value
			(i32.const 4)	;; length of returned value
		)
	)

	(func (export "deploy"))
)
"#;

		let mut ext = MockExt::default();
		ext.set_storage(
			&Key::<Test>::try_from_var([1u8; 64].to_vec()).unwrap(),
			Some(vec![42u8]),
			false,
		)
		.unwrap();
		ext.set_storage(
			&Key::<Test>::try_from_var([2u8; 19].to_vec()).unwrap(),
			Some(vec![]),
			false,
		)
		.unwrap();

		//value does not exist (wrong key length)
		let input = (63, [1u8; 64]).encode();
		let result = execute(CODE, input, &mut ext).unwrap();
		// sentinel returned
		assert_eq!(u32::from_le_bytes(result.data.try_into().unwrap()), crate::SENTINEL);

		// value exists
		let input = (64, [1u8; 64]).encode();
		let result = execute(CODE, input, &mut ext).unwrap();
		// true as u32 returned
		assert_eq!(u32::from_le_bytes(result.data.try_into().unwrap()), 1);
		// getter does not remove the value from storage
		assert_eq!(ext.storage.get(&[1u8; 64].to_vec()).unwrap(), &[42u8]);

		// value exists (test for 0 sized)
		let input = (19, [2u8; 19]).encode();
		let result = execute(CODE, input, &mut ext).unwrap();
		// true as u32 returned
		assert_eq!(u32::from_le_bytes(result.data.try_into().unwrap()), 0);
		// getter does not remove the value from storage
		assert_eq!(ext.storage.get(&[2u8; 19].to_vec()).unwrap(), &([] as [u8; 0]));
	}

	const CODE_INSTANTIATE: &str = r#"
(module
	;; seal_instantiate(
	;;     code_ptr: u32,
	;;     code_len: u32,
	;;     gas: u64,
	;;     value_ptr: u32,
	;;     value_len: u32,
	;;     input_data_ptr: u32,
	;;     input_data_len: u32,
	;;     input_data_len: u32,
	;;     address_ptr: u32,
	;;     address_len_ptr: u32,
	;;     output_ptr: u32,
	;;     output_len_ptr: u32
	;; ) -> u32
	(import "seal0" "seal_instantiate" (func $seal_instantiate
		(param i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32) (result i32)
	))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $seal_instantiate
				(i32.const 16)   ;; Pointer to `code_hash`
				(i32.const 32)   ;; Length of `code_hash`
				(i64.const 0)    ;; How much gas to devote for the execution. 0 = all.
				(i32.const 4)    ;; Pointer to the buffer with value to transfer
				(i32.const 8)    ;; Length of the buffer with value to transfer
				(i32.const 12)   ;; Pointer to input data buffer address
				(i32.const 4)    ;; Length of input data buffer
				(i32.const 4294967295) ;; u32 max value is the sentinel value: do not copy address
				(i32.const 0) ;; Length is ignored in this case
				(i32.const 4294967295) ;; u32 max value is the sentinel value: do not copy output
				(i32.const 0) ;; Length is ignored in this case
				(i32.const 0) ;; salt_ptr
				(i32.const 4) ;; salt_len
			)
		)
	)
	(func (export "deploy"))

	;; Salt
	(data (i32.const 0) "\42\43\44\45")
	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 4) "\03\00\00\00\00\00\00\00")
	;; Input data to pass to the contract being instantiated.
	(data (i32.const 12) "\01\02\03\04")
	;; Hash of code.
	(data (i32.const 16)
		"\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11"
		"\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11"
	)
)
"#;

	#[test]
	fn contract_instantiate() {
		let mut mock_ext = MockExt::default();
		assert_ok!(execute(CODE_INSTANTIATE, vec![], &mut mock_ext));

		assert_matches!(
			&mock_ext.instantiates[..],
			[InstantiateEntry {
				code_hash,
				value: 3,
				data,
				gas_left: _,
				salt,
			}] if
				code_hash == &[0x11; 32].into() &&
				data == &vec![1, 2, 3, 4] &&
				salt == &vec![0x42, 0x43, 0x44, 0x45]
		);
	}

	const CODE_TERMINATE: &str = r#"
(module
	;; seal_terminate(
	;;     beneficiary_ptr: u32,
	;;     beneficiary_len: u32,
	;; )
	(import "seal0" "seal_terminate" (func $seal_terminate (param i32 i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(call $seal_terminate
			(i32.const 4)  ;; Pointer to "beneficiary" address.
			(i32.const 32)  ;; Length of "beneficiary" address.
		)
	)
	(func (export "deploy"))

	;; Beneficiary AccountId to transfer the funds.
	(data (i32.const 4)
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
	)
)
"#;

	#[test]
	fn contract_terminate() {
		let mut mock_ext = MockExt::default();
		execute(CODE_TERMINATE, vec![], &mut mock_ext).unwrap();

		assert_eq!(&mock_ext.terminations, &[TerminationEntry { beneficiary: ALICE }]);
	}

	const CODE_TRANSFER_LIMITED_GAS: &str = r#"
(module
	;; seal_call(
	;;    callee_ptr: u32,
	;;    callee_len: u32,
	;;    gas: u64,
	;;    value_ptr: u32,
	;;    value_len: u32,
	;;    input_data_ptr: u32,
	;;    input_data_len: u32,
	;;    output_ptr: u32,
	;;    output_len_ptr: u32
	;;) -> u32
	(import "seal0" "seal_call" (func $seal_call (param i32 i32 i64 i32 i32 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $seal_call
				(i32.const 4)  ;; Pointer to "callee" address.
				(i32.const 32)  ;; Length of "callee" address.
				(i64.const 228)  ;; How much gas to devote for the execution.
				(i32.const 36)  ;; Pointer to the buffer with value to transfer
				(i32.const 8)   ;; Length of the buffer with value to transfer.
				(i32.const 44)   ;; Pointer to input data buffer address
				(i32.const 4)   ;; Length of input data buffer
				(i32.const 4294967295) ;; u32 max value is the sentinel value: do not copy output
				(i32.const 0) ;; Length is ignored in this cas
			)
		)
	)
	(func (export "deploy"))

	;; Destination AccountId to transfer the funds.
	(data (i32.const 4)
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
	)
	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 36) "\06\00\00\00\00\00\00\00")

	(data (i32.const 44) "\01\02\03\04")
)
"#;

	#[test]
	fn contract_call_limited_gas() {
		let mut mock_ext = MockExt::default();
		assert_ok!(execute(&CODE_TRANSFER_LIMITED_GAS, vec![], &mut mock_ext));

		assert_eq!(
			&mock_ext.calls,
			&[CallEntry { to: ALICE, value: 6, data: vec![1, 2, 3, 4], allows_reentry: true }]
		);
	}

	const CODE_ECDSA_RECOVER: &str = r#"
(module
	;; seal_ecdsa_recover(
	;;    signature_ptr: u32,
	;;    message_hash_ptr: u32,
	;;    output_ptr: u32
	;; ) -> u32
	(import "seal0" "seal_ecdsa_recover" (func $seal_ecdsa_recover (param i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $seal_ecdsa_recover
				(i32.const 36) ;; Pointer to signature.
				(i32.const 4)  ;; Pointer to message hash.
				(i32.const 36) ;; Pointer for output - public key.
			)
		)
	)
	(func (export "deploy"))

	;; Hash of message.
	(data (i32.const 4)
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
	)
	;; Signature
	(data (i32.const 36)
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01"
	)
)
"#;

	#[test]
	fn contract_ecdsa_recover() {
		let mut mock_ext = MockExt::default();
		assert_ok!(execute(&CODE_ECDSA_RECOVER, vec![], &mut mock_ext));
		assert_eq!(mock_ext.ecdsa_recover.into_inner(), [([1; 65], [1; 32])]);
	}

	#[test]
	fn contract_ecdsa_to_eth_address() {
		/// calls `seal_ecdsa_to_eth_address` for the contstant and ensures the result equals the
		/// expected one.
		const CODE_ECDSA_TO_ETH_ADDRESS: &str = r#"
(module
	(import "seal0" "seal_ecdsa_to_eth_address" (func $seal_ecdsa_to_eth_address (param i32 i32) (result i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "call")
		;; fill the buffer with the eth address.
		(call $seal_ecdsa_to_eth_address (i32.const 0) (i32.const 0))

		;; Return the contents of the buffer
		(call $seal_return
			(i32.const 0)
			(i32.const 0)
			(i32.const 20)
		)

		;; seal_return doesn't return, so this is effectively unreachable.
		(unreachable)
	)
	(func (export "deploy"))
)
"#;

		let output = execute(CODE_ECDSA_TO_ETH_ADDRESS, vec![], MockExt::default()).unwrap();
		assert_eq!(
			output,
			ExecReturnValue { flags: ReturnFlags::empty(), data: [0x02; 20].to_vec() }
		);
	}

	#[test]
	fn contract_sr25519() {
		const CODE_SR25519: &str = r#"
(module
	(import "seal0" "sr25519_verify" (func $sr25519_verify (param i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $sr25519_verify
				(i32.const 0) ;; Pointer to signature.
				(i32.const 64) ;; Pointer to public key.
				(i32.const 16) ;; message length.
				(i32.const 96) ;; Pointer to message.
			)
		)
	)
	(func (export "deploy"))

	;; Signature (64 bytes)
	(data (i32.const 0)
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
	)

	;;  public key (32 bytes)
	(data (i32.const 64)
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
	)

	;;  message. (16 bytes)
	(data (i32.const 96)
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
	)
)
"#;
		let mut mock_ext = MockExt::default();
		assert_ok!(execute(&CODE_SR25519, vec![], &mut mock_ext));
		assert_eq!(mock_ext.sr25519_verify.into_inner(), [([1; 64], [1; 16].to_vec(), [1; 32])]);
	}

	const CODE_GET_STORAGE: &str = r#"
(module
	(import "seal0" "seal_get_storage" (func $seal_get_storage (param i32 i32 i32) (result i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 32) key for get storage
	(data (i32.const 0)
		"\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11"
		"\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11"
	)

	;; [32, 36) buffer size = 4k in little endian
	(data (i32.const 32) "\00\10")

	;; [36; inf) buffer where the result is copied

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		(local $buf_size i32)

		;; Load a storage value into contract memory.
		(call $assert
			(i32.eq
				(call $seal_get_storage
					(i32.const 0)		;; The pointer to the storage key to fetch
					(i32.const 36)		;; Pointer to the output buffer
					(i32.const 32)		;; Pointer to the size of the buffer
				)

				;; Return value 0 means that the value is found and there were
				;; no errors.
				(i32.const 0)
			)
		)

		;; Find out the size of the buffer
		(set_local $buf_size
			(i32.load (i32.const 32))
		)

		;; Return the contents of the buffer
		(call $seal_return
			(i32.const 0)
			(i32.const 36)
			(get_local $buf_size)
		)

		;; env:seal_return doesn't return, so this is effectively unreachable.
		(unreachable)
	)

	(func (export "deploy"))
)
"#;

	#[test]
	fn get_storage_puts_data_into_buf() {
		let mut mock_ext = MockExt::default();
		mock_ext.storage.insert([0x11; 32].to_vec(), [0x22; 32].to_vec());

		let output = execute(CODE_GET_STORAGE, vec![], mock_ext).unwrap();

		assert_eq!(
			output,
			ExecReturnValue { flags: ReturnFlags::empty(), data: [0x22; 32].to_vec() }
		);
	}

	/// calls `seal_caller` and compares the result with the constant (ALICE's address part).
	const CODE_CALLER: &str = r#"
(module
	(import "seal0" "seal_caller" (func $seal_caller (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; fill the buffer with the caller.
		(call $seal_caller (i32.const 0) (i32.const 32))

		;; assert len == 32
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 32)
			)
		)

		;; assert that the first 8 bytes are the beginning of "ALICE"
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 0x0101010101010101)
			)
		)
	)

	(func (export "deploy"))
)
"#;

	#[test]
	fn caller() {
		assert_ok!(execute(CODE_CALLER, vec![], MockExt::default()));
	}

	#[test]
	fn caller_traps_when_no_account_id() {
		let mut ext = MockExt::default();
		ext.caller = Origin::Root;
		assert_eq!(
			execute(CODE_CALLER, vec![], ext),
			Err(ExecError { error: DispatchError::RootNotAllowed, origin: ErrorOrigin::Caller })
		);
	}

	/// calls `seal_address` and compares the result with the constant (BOB's address part).
	const CODE_ADDRESS: &str = r#"
(module
	(import "seal0" "seal_address" (func $seal_address (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; fill the buffer with the self address.
		(call $seal_address (i32.const 0) (i32.const 32))

		;; assert size == 32
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 32)
			)
		)

		;; assert that the first 8 bytes are the beginning of "BOB"
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 0x0202020202020202)
			)
		)
	)

	(func (export "deploy"))
)
"#;

	#[test]
	fn address() {
		assert_ok!(execute(CODE_ADDRESS, vec![], MockExt::default()));
	}

	const CODE_BALANCE: &str = r#"
(module
	(import "seal0" "seal_balance" (func $seal_balance (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the balance in the buffer
		(call $seal_balance (i32.const 0) (i32.const 32))

		;; assert len == 8
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 8)
			)
		)

		;; assert that contents of the buffer is equal to the i64 value of 228.
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 228)
			)
		)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn balance() {
		assert_ok!(execute(CODE_BALANCE, vec![], MockExt::default()));
	}

	const CODE_GAS_PRICE: &str = r#"
(module
	(import "seal1" "weight_to_fee" (func $seal_weight_to_fee (param i64 i64 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the gas price in the buffer
		(call $seal_weight_to_fee (i64.const 2) (i64.const 1) (i32.const 0) (i32.const 32))

		;; assert len == 8
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 8)
			)
		)

		;; assert that contents of the buffer is equal to the i64 value of 2 * 1312 + 103 = 2727.
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 2727)
			)
		)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn gas_price() {
		assert_ok!(execute(CODE_GAS_PRICE, vec![], MockExt::default()));
	}

	const CODE_GAS_LEFT: &str = r#"
(module
	(import "seal1" "gas_left" (func $seal_gas_left (param i32 i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; Make output buffer size 20 bytes
	(data (i32.const 20) "\14")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the weight left to the buffer
		(call $seal_gas_left (i32.const 0) (i32.const 20))

		;; Assert len <= 16 (max encoded Weight len)
		(call $assert
			(i32.le_u
				(i32.load (i32.const 20))
				(i32.const 16)
			)
		)

		;; Return weight left and its encoded value len
		(call $seal_return (i32.const 0) (i32.const 0) (i32.load (i32.const 20)))

		(unreachable)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn gas_left() {
		let mut ext = MockExt::default();
		let gas_limit = ext.gas_meter.gas_left();

		let output = execute(CODE_GAS_LEFT, vec![], &mut ext).unwrap();

		let weight_left = Weight::decode(&mut &*output.data).unwrap();
		let actual_left = ext.gas_meter.gas_left();

		assert!(weight_left.all_lt(gas_limit), "gas_left must be less than initial");
		assert!(weight_left.all_gt(actual_left), "gas_left must be greater than final");
	}

	/// Test that [`frame_support::weights::OldWeight`] en/decodes the same as our
	/// [`crate::OldWeight`].
	#[test]
	fn old_weight_decode() {
		#![allow(deprecated)]
		let sp = frame_support::weights::OldWeight(42).encode();
		let our = crate::OldWeight::decode(&mut &*sp).unwrap();

		assert_eq!(our, 42);
	}

	const CODE_VALUE_TRANSFERRED: &str = r#"
(module
	(import "seal0" "seal_value_transferred" (func $seal_value_transferred (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the value transferred in the buffer
		(call $seal_value_transferred (i32.const 0) (i32.const 32))

		;; assert len == 8
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 8)
			)
		)

		;; assert that contents of the buffer is equal to the i64 value of 1337.
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 1337)
			)
		)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn value_transferred() {
		assert_ok!(execute(CODE_VALUE_TRANSFERRED, vec![], MockExt::default()));
	}

	const START_FN_ILLEGAL: &str = r#"
(module
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(start $start)
	(func $start
		(unreachable)
	)

	(func (export "call")
		(unreachable)
	)

	(func (export "deploy")
		(unreachable)
	)

	(data (i32.const 8) "\01\02\03\04")
)
"#;

	#[test]
	fn start_fn_illegal() {
		let output = execute(START_FN_ILLEGAL, vec![], MockExt::default());
		assert_err!(output, <Error<Test>>::CodeRejected,);
	}

	const CODE_TIMESTAMP_NOW: &str = r#"
(module
	(import "seal0" "seal_now" (func $seal_now (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the block timestamp in the buffer
		(call $seal_now (i32.const 0) (i32.const 32))

		;; assert len == 8
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 8)
			)
		)

		;; assert that contents of the buffer is equal to the i64 value of 1111.
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 1111)
			)
		)
	)
	(func (export "deploy"))
)
"#;

	const CODE_TIMESTAMP_NOW_UNPREFIXED: &str = r#"
(module
	(import "seal0" "now" (func $now (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the block timestamp in the buffer
		(call $now (i32.const 0) (i32.const 32))

		;; assert len == 8
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 8)
			)
		)

		;; assert that contents of the buffer is equal to the i64 value of 1111.
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 1111)
			)
		)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn now() {
		assert_ok!(execute(CODE_TIMESTAMP_NOW, vec![], MockExt::default()));
		assert_ok!(execute(CODE_TIMESTAMP_NOW_UNPREFIXED, vec![], MockExt::default()));
	}

	const CODE_MINIMUM_BALANCE: &str = r#"
(module
	(import "seal0" "seal_minimum_balance" (func $seal_minimum_balance (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		(call $seal_minimum_balance (i32.const 0) (i32.const 32))

		;; assert len == 8
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 8)
			)
		)

		;; assert that contents of the buffer is equal to the i64 value of 666.
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 666)
			)
		)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn minimum_balance() {
		assert_ok!(execute(CODE_MINIMUM_BALANCE, vec![], MockExt::default()));
	}

	const CODE_RANDOM: &str = r#"
(module
	(import "seal0" "seal_random" (func $seal_random (param i32 i32 i32 i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; [0,128) is reserved for the result of PRNG.

	;; the subject used for the PRNG. [128,160)
	(data (i32.const 128)
		"\00\01\02\03\04\05\06\07\08\09\0A\0B\0C\0D\0E\0F"
		"\00\01\02\03\04\05\06\07\08\09\0A\0B\0C\0D\0E\0F"
	)

	;; size of our buffer is 128 bytes
	(data (i32.const 160) "\80")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the block random seed in the buffer
		(call $seal_random
			(i32.const 128) ;; Pointer in memory to the start of the subject buffer
			(i32.const 32) ;; The subject buffer's length
			(i32.const 0) ;; Pointer to the output buffer
			(i32.const 160) ;; Pointer to the output buffer length
		)

		;; assert len == 32
		(call $assert
			(i32.eq
				(i32.load (i32.const 160))
				(i32.const 32)
			)
		)

		;; return the random data
		(call $seal_return
			(i32.const 0)
			(i32.const 0)
			(i32.const 32)
		)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn random() {
		let output = execute_unvalidated(CODE_RANDOM, vec![], MockExt::default()).unwrap();

		// The mock ext just returns the same data that was passed as the subject.
		assert_eq!(
			output,
			ExecReturnValue {
				flags: ReturnFlags::empty(),
				data: array_bytes::hex_into_unchecked(
					"000102030405060708090A0B0C0D0E0F000102030405060708090A0B0C0D0E0F"
				)
			},
		);
	}

	const CODE_RANDOM_V1: &str = r#"
(module
	(import "seal1" "seal_random" (func $seal_random (param i32 i32 i32 i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; [0,128) is reserved for the result of PRNG.

	;; the subject used for the PRNG. [128,160)
	(data (i32.const 128)
		"\00\01\02\03\04\05\06\07\08\09\0A\0B\0C\0D\0E\0F"
		"\00\01\02\03\04\05\06\07\08\09\0A\0B\0C\0D\0E\0F"
	)

	;; size of our buffer is 128 bytes
	(data (i32.const 160) "\80")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the block random seed in the buffer
		(call $seal_random
			(i32.const 128) ;; Pointer in memory to the start of the subject buffer
			(i32.const 32) ;; The subject buffer's length
			(i32.const 0) ;; Pointer to the output buffer
			(i32.const 160) ;; Pointer to the output buffer length
		)

		;; assert len == 32
		(call $assert
			(i32.eq
				(i32.load (i32.const 160))
				(i32.const 40)
			)
		)

		;; return the random data
		(call $seal_return
			(i32.const 0)
			(i32.const 0)
			(i32.const 40)
		)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn random_v1() {
		let output = execute_unvalidated(CODE_RANDOM_V1, vec![], MockExt::default()).unwrap();

		// The mock ext just returns the same data that was passed as the subject.
		assert_eq!(
			output,
			ExecReturnValue {
				flags: ReturnFlags::empty(),
				data: (
					array_bytes::hex2array_unchecked::<_, 32>(
						"000102030405060708090A0B0C0D0E0F000102030405060708090A0B0C0D0E0F"
					),
					42u64,
				)
					.encode()
			},
		);
	}

	const CODE_DEPOSIT_EVENT: &str = r#"
(module
	(import "seal0" "seal_deposit_event" (func $seal_deposit_event (param i32 i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "call")
		(call $seal_deposit_event
			(i32.const 32) ;; Pointer to the start of topics buffer
			(i32.const 33) ;; The length of the topics buffer.
			(i32.const 8) ;; Pointer to the start of the data buffer
			(i32.const 13) ;; Length of the buffer
		)
	)
	(func (export "deploy"))

	(data (i32.const 8) "\00\01\2A\00\00\00\00\00\00\00\E5\14\00")

	;; Encoded Vec<TopicOf<T>>, the buffer has length of 33 bytes.
	(data (i32.const 32) "\04\33\33\33\33\33\33\33\33\33\33\33\33\33\33\33\33\33\33\33\33\33\33\33"
	"\33\33\33\33\33\33\33\33\33")
)
"#;

	#[test]
	fn deposit_event() {
		let mut mock_ext = MockExt::default();
		assert_ok!(execute(CODE_DEPOSIT_EVENT, vec![], &mut mock_ext));

		assert_eq!(
			mock_ext.events,
			vec![(
				vec![H256::repeat_byte(0x33)],
				vec![0x00, 0x01, 0x2a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe5, 0x14, 0x00]
			)]
		);

		assert!(mock_ext.gas_meter.gas_left().ref_time() > 0);
	}

	const CODE_DEPOSIT_EVENT_DUPLICATES: &str = r#"
(module
	(import "seal0" "seal_deposit_event" (func $seal_deposit_event (param i32 i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "call")
		(call $seal_deposit_event
			(i32.const 32) ;; Pointer to the start of topics buffer
			(i32.const 129) ;; The length of the topics buffer.
			(i32.const 8) ;; Pointer to the start of the data buffer
			(i32.const 13) ;; Length of the buffer
		)
	)
	(func (export "deploy"))

	(data (i32.const 8) "\00\01\2A\00\00\00\00\00\00\00\E5\14\00")

	;; Encoded Vec<TopicOf<T>>, the buffer has length of 129 bytes.
	(data (i32.const 32) "\10"
"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
"\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02"
"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
"\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04")
)
"#;

	/// Checks that the runtime allows duplicate topics.
	#[test]
	fn deposit_event_duplicates_allowed() {
		let mut mock_ext = MockExt::default();
		assert_ok!(execute(CODE_DEPOSIT_EVENT_DUPLICATES, vec![], &mut mock_ext,));

		assert_eq!(
			mock_ext.events,
			vec![(
				vec![
					H256::repeat_byte(0x01),
					H256::repeat_byte(0x02),
					H256::repeat_byte(0x01),
					H256::repeat_byte(0x04)
				],
				vec![0x00, 0x01, 0x2a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe5, 0x14, 0x00]
			)]
		);
	}

	const CODE_DEPOSIT_EVENT_MAX_TOPICS: &str = r#"
(module
	(import "seal0" "seal_deposit_event" (func $seal_deposit_event (param i32 i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "call")
		(call $seal_deposit_event
			(i32.const 32) ;; Pointer to the start of topics buffer
			(i32.const 161) ;; The length of the topics buffer.
			(i32.const 8) ;; Pointer to the start of the data buffer
			(i32.const 13) ;; Length of the buffer
		)
	)
	(func (export "deploy"))

	(data (i32.const 8) "\00\01\2A\00\00\00\00\00\00\00\E5\14\00")

	;; Encoded Vec<TopicOf<T>>, the buffer has length of 161 bytes.
	(data (i32.const 32) "\14"
"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
"\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02"
"\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03"
"\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04"
"\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05")
)
"#;

	/// Checks that the runtime traps if there are more than `max_topic_events` topics.
	#[test]
	fn deposit_event_max_topics() {
		assert_eq!(
			execute(CODE_DEPOSIT_EVENT_MAX_TOPICS, vec![], MockExt::default(),),
			Err(ExecError {
				error: Error::<Test>::TooManyTopics.into(),
				origin: ErrorOrigin::Caller,
			})
		);
	}

	/// calls `seal_block_number` compares the result with the constant 121.
	const CODE_BLOCK_NUMBER: &str = r#"
(module
	(import "seal0" "seal_block_number" (func $seal_block_number (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the block height in the buffer
		(call $seal_block_number (i32.const 0) (i32.const 32))

		;; assert len == 8
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 8)
			)
		)

		;; assert that contents of the buffer is equal to the i64 value of 121.
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 121)
			)
		)
	)

	(func (export "deploy"))
)
"#;

	#[test]
	fn block_number() {
		let _ = execute(CODE_BLOCK_NUMBER, vec![], MockExt::default()).unwrap();
	}

	const CODE_RETURN_WITH_DATA: &str = r#"
(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(data (i32.const 32) "\20")

	;; Deploy routine is the same as call.
	(func (export "deploy")
		(call $call)
	)

	;; Call reads the first 4 bytes (LE) as the exit status and returns the rest as output data.
	(func $call (export "call")
		;; Copy input data this contract memory.
		(call $seal_input
			(i32.const 0)	;; Pointer where to store input
			(i32.const 32)	;; Pointer to the length of the buffer
		)

		;; Copy all but the first 4 bytes of the input data as the output data.
		(call $seal_return
			(i32.load (i32.const 0))
			(i32.const 4)
			(i32.sub (i32.load (i32.const 32)) (i32.const 4))
		)
		(unreachable)
	)
)
"#;

	#[test]
	fn seal_return_with_success_status() {
		let output = execute(
			CODE_RETURN_WITH_DATA,
			array_bytes::hex2bytes_unchecked("00000000445566778899"),
			MockExt::default(),
		)
		.unwrap();

		assert_eq!(
			output,
			ExecReturnValue {
				flags: ReturnFlags::empty(),
				data: array_bytes::hex2bytes_unchecked("445566778899"),
			}
		);
		assert!(!output.did_revert());
	}

	#[test]
	fn return_with_revert_status() {
		let output = execute(
			CODE_RETURN_WITH_DATA,
			array_bytes::hex2bytes_unchecked("010000005566778899"),
			MockExt::default(),
		)
		.unwrap();

		assert_eq!(
			output,
			ExecReturnValue {
				flags: ReturnFlags::REVERT,
				data: array_bytes::hex2bytes_unchecked("5566778899"),
			}
		);
		assert!(output.did_revert());
	}

	const CODE_OUT_OF_BOUNDS_ACCESS: &str = r#"
(module
	(import "seal0" "seal_terminate" (func $seal_terminate (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "deploy"))

	(func (export "call")
		(call $seal_terminate
			(i32.const 65536)  ;; Pointer to "account" address (out of bound).
			(i32.const 8)  ;; Length of "account" address.
		)
	)
)
"#;

	#[test]
	fn contract_out_of_bounds_access() {
		let mut mock_ext = MockExt::default();
		let result = execute(CODE_OUT_OF_BOUNDS_ACCESS, vec![], &mut mock_ext);

		assert_eq!(
			result,
			Err(ExecError {
				error: Error::<Test>::OutOfBounds.into(),
				origin: ErrorOrigin::Caller,
			})
		);
	}

	const CODE_DECODE_FAILURE: &str = r#"
(module
	(import "seal0" "seal_terminate" (func $seal_terminate (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "deploy"))

	(func (export "call")
		(call $seal_terminate
			(i32.const 0)  ;; Pointer to "account" address.
			(i32.const 4)  ;; Length of "account" address (too small -> decode fail).
		)
	)
)
"#;

	#[test]
	fn contract_decode_length_ignored() {
		let mut mock_ext = MockExt::default();
		let result = execute(CODE_DECODE_FAILURE, vec![], &mut mock_ext);
		// AccountID implements `MaxEncodeLen` and therefore the supplied length is
		// no longer needed nor used to determine how much is read from contract memory.
		assert_ok!(result);
	}

	#[test]
	fn debug_message_works() {
		const CODE_DEBUG_MESSAGE: &str = r#"
(module
	(import "seal0" "seal_debug_message" (func $seal_debug_message (param i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))

	(data (i32.const 0) "Hello World!")

	(func (export "call")
		(call $seal_debug_message
			(i32.const 0)	;; Pointer to the text buffer
			(i32.const 12)	;; The size of the buffer
		)
		drop
	)

	(func (export "deploy"))
)
"#;
		let mut ext = MockExt::default();
		execute(CODE_DEBUG_MESSAGE, vec![], &mut ext).unwrap();

		assert_eq!(std::str::from_utf8(&ext.debug_buffer).unwrap(), "Hello World!");
	}

	#[test]
	fn debug_message_invalid_utf8_fails() {
		const CODE_DEBUG_MESSAGE_FAIL: &str = r#"
(module
	(import "seal0" "seal_debug_message" (func $seal_debug_message (param i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))

	(data (i32.const 0) "\fc")

	(func (export "call")
		(call $seal_debug_message
			(i32.const 0)	;; Pointer to the text buffer
			(i32.const 1)	;; The size of the buffer
		)
		drop
	)

	(func (export "deploy"))
)
"#;
		let mut ext = MockExt::default();
		let result = execute(CODE_DEBUG_MESSAGE_FAIL, vec![], &mut ext);
		assert_ok!(result);
		assert!(ext.debug_buffer.is_empty());
	}

	const CODE_CALL_RUNTIME: &str = r#"
(module
	(import "seal0" "call_runtime" (func $call_runtime (param i32 i32) (result i32)))
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; 0x1000 = 4k in little endian
	;; size of input buffer
	(data (i32.const 0) "\00\10")

	(func (export "call")
		;; Receive the encoded call
		(call $seal_input
			(i32.const 4)	;; Pointer to the input buffer
			(i32.const 0)	;; Size of the length buffer
		)
		;; Just use the call passed as input and store result to memory
		(i32.store (i32.const 0)
			(call $call_runtime
				(i32.const 4)				;; Pointer where the call is stored
				(i32.load (i32.const 0))	;; Size of the call
			)
		)
		(call $seal_return
			(i32.const 0)	;; flags
			(i32.const 0)	;; returned value
			(i32.const 4)	;; length of returned value
		)
	)

	(func (export "deploy"))
)
"#;

	#[test]
	fn call_runtime_works() {
		let call =
			RuntimeCall::System(frame_system::Call::remark { remark: b"Hello World".to_vec() });
		let mut ext = MockExt::default();
		let result = execute(CODE_CALL_RUNTIME, call.encode(), &mut ext).unwrap();
		assert_eq!(*ext.runtime_calls.borrow(), vec![call]);
		// 0 = ReturnCode::Success
		assert_eq!(u32::from_le_bytes(result.data.try_into().unwrap()), 0);
	}

	#[test]
	fn call_runtime_panics_on_invalid_call() {
		let mut ext = MockExt::default();
		let result = execute(CODE_CALL_RUNTIME, vec![0x42], &mut ext);
		assert_eq!(
			result,
			Err(ExecError {
				error: Error::<Test>::DecodingFailed.into(),
				origin: ErrorOrigin::Caller,
			})
		);
		assert_eq!(*ext.runtime_calls.borrow(), vec![]);
	}

	#[test]
	fn set_storage_works() {
		const CODE: &str = r#"
(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "seal2" "set_storage" (func $set_storage (param i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 4) size of input buffer
	;; 4k in little endian
	(data (i32.const 0) "\00\10")

	;; [4, 4100) input buffer

	(func (export "call")
		;; Receive (key ++ value_to_write)
		(call $seal_input
			(i32.const 4)	;; Pointer to the input buffer
			(i32.const 0)	;; Size of the input buffer
		)
		;; Store the passed value to the passed key and store result to memory
		(i32.store (i32.const 168)
			(call $set_storage
				(i32.const 8)				;; key_ptr
				(i32.load (i32.const 4))		;; key_len
				(i32.add				;; value_ptr = 8 + key_len
					(i32.const 8)
					(i32.load (i32.const 4)))
				(i32.sub				;; value_len (input_size - (key_len + key_len_len))
					(i32.load (i32.const 0))
					(i32.add
						(i32.load (i32.const 4))
						(i32.const 4)
					)
				)
			)
		)
		(call $seal_return
			(i32.const 0)	;; flags
			(i32.const 168)	;; ptr to returned value
			(i32.const 4)	;; length of returned value
		)
	)

	(func (export "deploy"))
)
"#;

		let mut ext = MockExt::default();

		// value did not exist before -> sentinel returned
		let input = (32, [1u8; 32], [42u8, 48]).encode();
		let result = execute(CODE, input, &mut ext).unwrap();
		assert_eq!(u32::from_le_bytes(result.data.try_into().unwrap()), crate::SENTINEL);
		assert_eq!(ext.storage.get(&[1u8; 32].to_vec()).unwrap(), &[42u8, 48]);

		// value do exist -> length of old value returned
		let input = (32, [1u8; 32], [0u8; 0]).encode();
		let result = execute(CODE, input, &mut ext).unwrap();
		assert_eq!(u32::from_le_bytes(result.data.try_into().unwrap()), 2);
		assert_eq!(ext.storage.get(&[1u8; 32].to_vec()).unwrap(), &[0u8; 0]);

		// value do exist -> length of old value returned (test for zero sized val)
		let input = (32, [1u8; 32], [99u8]).encode();
		let result = execute(CODE, input, &mut ext).unwrap();
		assert_eq!(u32::from_le_bytes(result.data.try_into().unwrap()), 0);
		assert_eq!(ext.storage.get(&[1u8; 32].to_vec()).unwrap(), &[99u8]);
	}

	#[test]
	fn get_storage_works() {
		const CODE: &str = r#"
(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "seal1" "get_storage" (func $get_storage (param i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 4) size of input buffer (160 bytes as we copy the key+len here)
	(data (i32.const 0) "\A0")

	;; [4, 8) size of output buffer
	;; 4k in little endian
	(data (i32.const 4) "\00\10")

	;; [8, 168) input buffer
	;; [168, 4264) output buffer

	(func (export "call")
		;; Receive (key ++ value_to_write)
		(call $seal_input
			(i32.const 8)	;; Pointer to the input buffer
			(i32.const 0)	;; Size of the input buffer
		)
		;; Load a storage value and result of this call into the output buffer
		(i32.store (i32.const 168)
			(call $get_storage
				(i32.const 12)			;; key_ptr
				(i32.load (i32.const 8))	;; key_len
				(i32.const 172)			;; Pointer to the output buffer
				(i32.const 4)			;; Pointer to the size of the buffer
			)
		)
		(call $seal_return
			(i32.const 0)				;; flags
			(i32.const 168)				;; output buffer ptr
			(i32.add				;; length: output size + 4 (retval)
				(i32.load (i32.const 4))
				(i32.const 4)
			)
		)
	)

	(func (export "deploy"))
)
"#;

		let mut ext = MockExt::default();

		ext.set_storage(
			&Key::<Test>::try_from_var([1u8; 64].to_vec()).unwrap(),
			Some(vec![42u8]),
			false,
		)
		.unwrap();

		ext.set_storage(
			&Key::<Test>::try_from_var([2u8; 19].to_vec()).unwrap(),
			Some(vec![]),
			false,
		)
		.unwrap();

		// value does not exist
		let input = (63, [1u8; 64]).encode();
		let result = execute(CODE, input, &mut ext).unwrap();
		assert_eq!(
			u32::from_le_bytes(result.data[0..4].try_into().unwrap()),
			ReturnCode::KeyNotFound as u32
		);

		// value exists
		let input = (64, [1u8; 64]).encode();
		let result = execute(CODE, input, &mut ext).unwrap();
		assert_eq!(
			u32::from_le_bytes(result.data[0..4].try_into().unwrap()),
			ReturnCode::Success as u32
		);
		assert_eq!(ext.storage.get(&[1u8; 64].to_vec()).unwrap(), &[42u8]);
		assert_eq!(&result.data[4..], &[42u8]);

		// value exists (test for 0 sized)
		let input = (19, [2u8; 19]).encode();
		let result = execute(CODE, input, &mut ext).unwrap();
		assert_eq!(
			u32::from_le_bytes(result.data[0..4].try_into().unwrap()),
			ReturnCode::Success as u32
		);
		assert_eq!(ext.storage.get(&[2u8; 19].to_vec()), Some(&vec![]));
		assert_eq!(&result.data[4..], &([] as [u8; 0]));
	}

	#[test]
	fn clear_storage_works() {
		const CODE: &str = r#"
(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "seal1" "clear_storage" (func $clear_storage (param i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))

	;; size of input buffer
	;; [0, 4) size of input buffer (128+32 = 160 bytes = 0xA0)
	(data (i32.const 0) "\A0")

	;; [4, 164) input buffer

	(func (export "call")
		;; Receive key
		(call $seal_input
			(i32.const 4)	;; Where we take input and store it
			(i32.const 0)	;; Where we take and store the length of thedata
		)
		;; Call seal_clear_storage and save what it returns at 0
		(i32.store (i32.const 0)
			(call $clear_storage
				(i32.const 8)			;; key_ptr
				(i32.load (i32.const 4))	;; key_len
			)
		)
		(call $seal_return
			(i32.const 0)	;; flags
			(i32.const 0)	;; returned value
			(i32.const 4)	;; length of returned value
		)
	)

	(func (export "deploy"))
)
"#;

		let mut ext = MockExt::default();

		ext.set_storage(
			&Key::<Test>::try_from_var([1u8; 64].to_vec()).unwrap(),
			Some(vec![42u8]),
			false,
		)
		.unwrap();
		ext.set_storage(
			&Key::<Test>::try_from_var([2u8; 19].to_vec()).unwrap(),
			Some(vec![]),
			false,
		)
		.unwrap();

		// value did not exist
		let input = (32, [3u8; 32]).encode();
		let result = execute(CODE, input, &mut ext).unwrap();
		// sentinel returned
		assert_eq!(u32::from_le_bytes(result.data.try_into().unwrap()), crate::SENTINEL);
		assert_eq!(ext.storage.get(&[3u8; 32].to_vec()), None);

		// value did exist
		let input = (64, [1u8; 64]).encode();
		let result = execute(CODE, input, &mut ext).unwrap();
		// length returned
		assert_eq!(u32::from_le_bytes(result.data.try_into().unwrap()), 1);
		// value cleared
		assert_eq!(ext.storage.get(&[1u8; 64].to_vec()), None);

		//value did not exist (wrong key length)
		let input = (63, [1u8; 64]).encode();
		let result = execute(CODE, input, &mut ext).unwrap();
		// sentinel returned
		assert_eq!(u32::from_le_bytes(result.data.try_into().unwrap()), crate::SENTINEL);
		assert_eq!(ext.storage.get(&[1u8; 64].to_vec()), None);

		// value exists
		let input = (19, [2u8; 19]).encode();
		let result = execute(CODE, input, &mut ext).unwrap();
		// length returned (test for 0 sized)
		assert_eq!(u32::from_le_bytes(result.data.try_into().unwrap()), 0);
		// value cleared
		assert_eq!(ext.storage.get(&[2u8; 19].to_vec()), None);
	}

	#[test]
	fn take_storage_works() {
		const CODE: &str = r#"
(module
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "take_storage" (func $take_storage (param i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 4) size of input buffer (160 bytes as we copy the key+len here)
	(data (i32.const 0) "\A0")

	;; [4, 8) size of output buffer
	;; 4k in little endian
	(data (i32.const 4) "\00\10")

	;; [8, 168) input buffer
	;; [168, 4264) output buffer

	(func (export "call")
		;; Receive key
		(call $seal_input
			(i32.const 8)	;; Pointer to the input buffer
			(i32.const 0)	;; Size of the length buffer
		)

		;; Load a storage value and result of this call into the output buffer
		(i32.store (i32.const 168)
			(call $take_storage
				(i32.const 12)			;; key_ptr
				(i32.load (i32.const 8))	;; key_len
				(i32.const 172)			;; Pointer to the output buffer
				(i32.const 4)			;; Pointer to the size of the buffer
			)
		)

		;; Return the contents of the buffer
		(call $seal_return
			(i32.const 0)				;; flags
			(i32.const 168)				;; output buffer ptr
			(i32.add				;; length: storage size + 4 (retval)
				(i32.load (i32.const 4))
				(i32.const 4)
			)
		)
	)

	(func (export "deploy"))
)
"#;

		let mut ext = MockExt::default();

		ext.set_storage(
			&Key::<Test>::try_from_var([1u8; 64].to_vec()).unwrap(),
			Some(vec![42u8]),
			false,
		)
		.unwrap();

		ext.set_storage(
			&Key::<Test>::try_from_var([2u8; 19].to_vec()).unwrap(),
			Some(vec![]),
			false,
		)
		.unwrap();

		// value does not exist -> error returned
		let input = (63, [1u8; 64]).encode();
		let result = execute(CODE, input, &mut ext).unwrap();
		assert_eq!(
			u32::from_le_bytes(result.data[0..4].try_into().unwrap()),
			ReturnCode::KeyNotFound as u32
		);

		// value did exist -> value returned
		let input = (64, [1u8; 64]).encode();
		let result = execute(CODE, input, &mut ext).unwrap();
		assert_eq!(
			u32::from_le_bytes(result.data[0..4].try_into().unwrap()),
			ReturnCode::Success as u32
		);
		assert_eq!(ext.storage.get(&[1u8; 64].to_vec()), None);
		assert_eq!(&result.data[4..], &[42u8]);

		// value did exist -> length returned (test for 0 sized)
		let input = (19, [2u8; 19]).encode();
		let result = execute(CODE, input, &mut ext).unwrap();
		assert_eq!(
			u32::from_le_bytes(result.data[0..4].try_into().unwrap()),
			ReturnCode::Success as u32
		);
		assert_eq!(ext.storage.get(&[2u8; 19].to_vec()), None);
		assert_eq!(&result.data[4..], &[0u8; 0]);
	}

	#[test]
	fn is_contract_works() {
		const CODE_IS_CONTRACT: &str = r#"
;; This runs `is_contract` check on zero account address
(module
	(import "seal0" "seal_is_contract" (func $seal_is_contract (param i32) (result i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 32) zero-adress
	(data (i32.const 0)
		"\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
		"\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00"
	)

	;; [32, 36) here we store the return code of the `seal_is_contract`

	(func (export "deploy"))

	(func (export "call")
		(i32.store
			(i32.const 32)
			(call $seal_is_contract
				(i32.const 0) ;; ptr to destination address
			)
		)
		;; exit with success and take `seal_is_contract` return code to the output buffer
		(call $seal_return (i32.const 0) (i32.const 32) (i32.const 4))
	)
)
"#;
		let output = execute(CODE_IS_CONTRACT, vec![], MockExt::default()).unwrap();

		// The mock ext just always returns 1u32 (`true`).
		assert_eq!(output, ExecReturnValue { flags: ReturnFlags::empty(), data: 1u32.encode() },);
	}

	#[test]
	fn code_hash_works() {
		/// calls `seal_code_hash` and compares the result with the constant.
		const CODE_CODE_HASH: &str = r#"
(module
	(import "seal0" "seal_code_hash" (func $seal_code_hash (param i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; fill the buffer with the code hash.
		(call $seal_code_hash
			(i32.const 0) ;; input: address_ptr (before call)
			(i32.const 0) ;; output: code_hash_ptr (after call)
			(i32.const 32) ;; same 32 bytes length for input and output
		)

		;; assert size == 32
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 32)
			)
		)

		;; assert that the first 8 bytes are "1111111111111111"
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 0x1111111111111111)
			)
		)
		drop
	)

	(func (export "deploy"))
)
"#;
		assert_ok!(execute(CODE_CODE_HASH, vec![], MockExt::default()));
	}

	#[test]
	fn own_code_hash_works() {
		/// calls `seal_own_code_hash` and compares the result with the constant.
		const CODE_OWN_CODE_HASH: &str = r#"
(module
	(import "seal0" "seal_own_code_hash" (func $seal_own_code_hash (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; fill the buffer with the code hash
		(call $seal_own_code_hash
			(i32.const 0)  ;; output: code_hash_ptr
			(i32.const 32) ;; 32 bytes length of code_hash output
		)

		;; assert size == 32
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 32)
			)
		)

		;; assert that the first 8 bytes are "1010101010101010"
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 0x1010101010101010)
			)
		)
	)

	(func (export "deploy"))
)
"#;
		assert_ok!(execute(CODE_OWN_CODE_HASH, vec![], MockExt::default()));
	}

	#[test]
	fn caller_is_origin_works() {
		const CODE_CALLER_IS_ORIGIN: &str = r#"
;; This runs `caller_is_origin` check on zero account address
(module
	(import "seal0" "seal_caller_is_origin" (func $seal_caller_is_origin (result i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 4) here the return code of the `seal_caller_is_origin` will be stored
	;; we initialize it with non-zero value to be sure that it's being overwritten below
	(data (i32.const 0) "\10\10\10\10")

	(func (export "deploy"))

	(func (export "call")
		(i32.store
			(i32.const 0)
			(call $seal_caller_is_origin)
		)
		;; exit with success and take `seal_caller_is_origin` return code to the output buffer
		(call $seal_return (i32.const 0) (i32.const 0) (i32.const 4))
	)
)
"#;
		let output = execute(CODE_CALLER_IS_ORIGIN, vec![], MockExt::default()).unwrap();

		// The mock ext just always returns 0u32 (`false`)
		assert_eq!(output, ExecReturnValue { flags: ReturnFlags::empty(), data: 0u32.encode() },);
	}

	#[test]
	fn caller_is_root_works() {
		const CODE_CALLER_IS_ROOT: &str = r#"
;; This runs `caller_is_root` check on zero account address
(module
	(import "seal0" "caller_is_root" (func $caller_is_root (result i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 4) here the return code of the `caller_is_root` will be stored
	;; we initialize it with non-zero value to be sure that it's being overwritten below
	(data (i32.const 0) "\10\10\10\10")

	(func (export "deploy"))

	(func (export "call")
		(i32.store
			(i32.const 0)
			(call $caller_is_root)
		)
		;; exit with success and take `caller_is_root` return code to the output buffer
		(call $seal_return (i32.const 0) (i32.const 0) (i32.const 4))
	)
)
"#;
		// The default `caller` is ALICE. Therefore not root.
		let output = execute(CODE_CALLER_IS_ROOT, vec![], MockExt::default()).unwrap();
		assert_eq!(output, ExecReturnValue { flags: ReturnFlags::empty(), data: 0u32.encode() },);

		// The caller is forced to be root instead of using the default ALICE.
		let output = execute(
			CODE_CALLER_IS_ROOT,
			vec![],
			MockExt { caller: Origin::Root, ..MockExt::default() },
		)
		.unwrap();
		assert_eq!(output, ExecReturnValue { flags: ReturnFlags::empty(), data: 1u32.encode() },);
	}

	#[test]
	fn set_code_hash() {
		const CODE: &str = r#"
(module
	(import "seal0" "seal_set_code_hash" (func $seal_set_code_hash (param i32) (result i32)))
	(import "env" "memory" (memory 1 1))
	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)
	(func (export "call")
		(local $exit_code i32)
		(set_local $exit_code
			(call $seal_set_code_hash (i32.const 0))
		)
		(call $assert
			(i32.eq (get_local $exit_code) (i32.const 0)) ;; ReturnCode::Success
		)
	)

	(func (export "deploy"))

	;; Hash of code.
	(data (i32.const 0)
		"\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11"
		"\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11"
	)
)
"#;

		let mut mock_ext = MockExt::default();
		execute(CODE, [0u8; 32].encode(), &mut mock_ext).unwrap();

		assert_eq!(mock_ext.code_hashes.pop().unwrap(), H256::from_slice(&[17u8; 32]));
	}

	#[test]
	fn reentrance_count_works() {
		const CODE: &str = r#"
(module
	(import "seal0" "reentrance_count" (func $reentrance_count (result i32)))
	(import "env" "memory" (memory 1 1))
	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)
	(func (export "call")
		(local $return_val i32)
		(set_local $return_val
			(call $reentrance_count)
		)
		(call $assert
			(i32.eq (get_local $return_val) (i32.const 12))
		)
	)

	(func (export "deploy"))
)
"#;

		let mut mock_ext = MockExt::default();
		execute(CODE, vec![], &mut mock_ext).unwrap();
	}

	#[test]
	fn account_reentrance_count_works() {
		const CODE: &str = r#"
(module
	(import "seal0" "account_reentrance_count" (func $account_reentrance_count (param i32) (result i32)))
	(import "env" "memory" (memory 1 1))
	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)
	(func (export "call")
		(local $return_val i32)
		(set_local $return_val
			(call $account_reentrance_count (i32.const 0))
		)
		(call $assert
			(i32.eq (get_local $return_val) (i32.const 12))
		)
	)

	(func (export "deploy"))
)
"#;

		let mut mock_ext = MockExt::default();
		execute(CODE, vec![], &mut mock_ext).unwrap();
	}

	#[test]
	fn instantiation_nonce_works() {
		const CODE: &str = r#"
(module
	(import "seal0" "instantiation_nonce" (func $nonce (result i64)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)
	(func (export "call")
		(call $assert
			(i64.eq (call $nonce) (i64.const 995))
		)
	)
	(func (export "deploy"))
)
"#;

		let mut mock_ext = MockExt::default();
		execute(CODE, vec![], &mut mock_ext).unwrap();
	}

	/// This test check that an unstable interface cannot be deployed. In case of runtime
	/// benchmarks we always allow unstable interfaces. This is why this test does not
	/// work when this feature is enabled.
	#[cfg(not(feature = "runtime-benchmarks"))]
	#[test]
	fn cannot_deploy_unstable() {
		const CANNOT_DEPLOY_UNSTABLE: &str = r#"
(module
	(import "seal0" "reentrance_count" (func $reentrance_count (result i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "call"))
	(func (export "deploy"))
)
"#;
		assert_err!(
			execute_no_unstable(CANNOT_DEPLOY_UNSTABLE, vec![], MockExt::default()),
			<Error<Test>>::CodeRejected,
		);
		assert_ok!(execute(CANNOT_DEPLOY_UNSTABLE, vec![], MockExt::default()));
	}

	/// The random interface is deprecated and hence new contracts using it should not be deployed.
	/// In case of runtime benchmarks we always allow deprecated interfaces. This is why this
	/// test doesn't work if this feature is enabled.
	#[cfg(not(feature = "runtime-benchmarks"))]
	#[test]
	fn cannot_deploy_deprecated() {
		const CODE_RANDOM_0: &str = r#"
(module
	(import "seal0" "seal_random" (func $seal_random (param i32 i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "call"))
	(func (export "deploy"))
)
	"#;
		const CODE_RANDOM_1: &str = r#"
(module
	(import "seal1" "seal_random" (func $seal_random (param i32 i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "call"))
	(func (export "deploy"))
)
	"#;
		const CODE_RANDOM_2: &str = r#"
(module
	(import "seal0" "random" (func $seal_random (param i32 i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "call"))
	(func (export "deploy"))
)
	"#;
		const CODE_RANDOM_3: &str = r#"
(module
	(import "seal1" "random" (func $seal_random (param i32 i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "call"))
	(func (export "deploy"))
)
	"#;

		assert_ok!(execute_unvalidated(CODE_RANDOM_0, vec![], MockExt::default()));
		assert_err!(
			execute_instantiate_unvalidated(CODE_RANDOM_0, vec![], MockExt::default()),
			<Error<Test>>::CodeRejected,
		);
		assert_err!(
			execute(CODE_RANDOM_0, vec![], MockExt::default()),
			<Error<Test>>::CodeRejected,
		);

		assert_ok!(execute_unvalidated(CODE_RANDOM_1, vec![], MockExt::default()));
		assert_err!(
			execute_instantiate_unvalidated(CODE_RANDOM_1, vec![], MockExt::default()),
			<Error<Test>>::CodeRejected,
		);
		assert_err!(
			execute(CODE_RANDOM_1, vec![], MockExt::default()),
			<Error<Test>>::CodeRejected,
		);

		assert_ok!(execute_unvalidated(CODE_RANDOM_2, vec![], MockExt::default()));
		assert_err!(
			execute_instantiate_unvalidated(CODE_RANDOM_2, vec![], MockExt::default()),
			<Error<Test>>::CodeRejected,
		);
		assert_err!(
			execute(CODE_RANDOM_2, vec![], MockExt::default()),
			<Error<Test>>::CodeRejected,
		);

		assert_ok!(execute_unvalidated(CODE_RANDOM_3, vec![], MockExt::default()));
		assert_err!(
			execute_instantiate_unvalidated(CODE_RANDOM_3, vec![], MockExt::default()),
			<Error<Test>>::CodeRejected,
		);
		assert_err!(
			execute(CODE_RANDOM_3, vec![], MockExt::default()),
			<Error<Test>>::CodeRejected,
		);
	}

	#[test]
	fn add_remove_delegate_dependency() {
		const CODE_ADD_REMOVE_DELEGATE_DEPENDENCY: &str = r#"
(module
	(import "seal0" "add_delegate_dependency" (func $add_delegate_dependency (param i32)))
	(import "seal0" "remove_delegate_dependency" (func $remove_delegate_dependency (param i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(call $add_delegate_dependency (i32.const 0))
		(call $add_delegate_dependency (i32.const 32))
		(call $remove_delegate_dependency (i32.const 32))
	)
	(func (export "deploy"))

	;;  hash1 (32 bytes)
	(data (i32.const 0)
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
	)

	;;  hash2 (32 bytes)
	(data (i32.const 32)
		"\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02"
		"\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02"
	)
)
"#;
		let mut mock_ext = MockExt::default();
		assert_ok!(execute(&CODE_ADD_REMOVE_DELEGATE_DEPENDENCY, vec![], &mut mock_ext));
		let delegate_dependencies: Vec<_> =
			mock_ext.delegate_dependencies.into_inner().into_iter().collect();
		assert_eq!(delegate_dependencies.len(), 1);
		assert_eq!(delegate_dependencies[0].as_bytes(), [1; 32]);
	}
}
