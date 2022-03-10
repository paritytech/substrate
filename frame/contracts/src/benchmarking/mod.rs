// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

//! Benchmarks for the contracts pallet

#![cfg(feature = "runtime-benchmarks")]

mod code;
mod sandbox;

use self::{
	code::{
		body::{self, DynInstr::*},
		DataSegment, ImportedFunction, ImportedMemory, Location, ModuleDefinition, WasmModule,
	},
	sandbox::Sandbox,
};
use crate::{
	exec::{AccountIdOf, StorageKey},
	schedule::{API_BENCHMARK_BATCH_SIZE, INSTR_BENCHMARK_BATCH_SIZE},
	storage::Storage,
	wasm::CallFlags,
	Pallet as Contracts, *,
};
use codec::{Encode, MaxEncodedLen};
use frame_benchmarking::{account, benchmarks, whitelisted_caller};
use frame_support::weights::Weight;
use frame_system::RawOrigin;
use sp_runtime::{
	traits::{Bounded, Hash},
	Perbill,
};
use sp_std::prelude::*;
use wasm_instrument::parity_wasm::elements::{BlockType, BrTableData, Instruction, ValueType};

/// How many batches we do per API benchmark.
const API_BENCHMARK_BATCHES: u32 = 20;

/// How many batches we do per Instruction benchmark.
const INSTR_BENCHMARK_BATCHES: u32 = 50;

/// An instantiated and deployed contract.
struct Contract<T: Config> {
	caller: T::AccountId,
	account_id: T::AccountId,
	addr: <T::Lookup as StaticLookup>::Source,
	value: BalanceOf<T>,
}

impl<T: Config> Contract<T>
where
	T: Config,
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
	<BalanceOf<T> as HasCompact>::Type: Clone + Eq + PartialEq + Debug + TypeInfo + Encode,
{
	/// Create new contract and use a default account id as instantiator.
	fn new(module: WasmModule<T>, data: Vec<u8>) -> Result<Contract<T>, &'static str> {
		Self::with_index(0, module, data)
	}

	/// Create new contract and use an account id derived from the supplied index as instantiator.
	fn with_index(
		index: u32,
		module: WasmModule<T>,
		data: Vec<u8>,
	) -> Result<Contract<T>, &'static str> {
		Self::with_caller(account("instantiator", index, 0), module, data)
	}

	/// Create new contract and use the supplied `caller` as instantiator.
	fn with_caller(
		caller: T::AccountId,
		module: WasmModule<T>,
		data: Vec<u8>,
	) -> Result<Contract<T>, &'static str> {
		let value = T::Currency::minimum_balance();
		T::Currency::make_free_balance_be(&caller, caller_funding::<T>());
		let salt = vec![0xff];
		let addr = Contracts::<T>::contract_address(&caller, &module.hash, &salt);

		Contracts::<T>::store_code_raw(module.code, caller.clone())?;
		Contracts::<T>::instantiate(
			RawOrigin::Signed(caller.clone()).into(),
			value,
			Weight::MAX,
			None,
			module.hash,
			data,
			salt,
		)?;

		let result =
			Contract { caller, account_id: addr.clone(), addr: T::Lookup::unlookup(addr), value };

		ContractInfoOf::<T>::insert(&result.account_id, result.info()?);

		Ok(result)
	}

	/// Create a new contract with the supplied storage item count and size each.
	fn with_storage(
		code: WasmModule<T>,
		stor_num: u32,
		stor_size: u32,
	) -> Result<Self, &'static str> {
		let contract = Contract::<T>::new(code, vec![])?;
		let storage_items = (0..stor_num)
			.map(|i| {
				let hash = T::Hashing::hash_of(&i)
					.as_ref()
					.try_into()
					.map_err(|_| "Hash too big for storage key")?;
				Ok((hash, vec![42u8; stor_size as usize]))
			})
			.collect::<Result<Vec<_>, &'static str>>()?;
		contract.store(&storage_items)?;
		Ok(contract)
	}

	/// Store the supplied storage items into this contracts storage.
	fn store(&self, items: &Vec<(StorageKey, Vec<u8>)>) -> Result<(), &'static str> {
		let info = self.info()?;
		for item in items {
			Storage::<T>::write(&info.trie_id, &item.0, Some(item.1.clone()), None, false)
				.map_err(|_| "Failed to write storage to restoration dest")?;
		}
		<ContractInfoOf<T>>::insert(&self.account_id, info.clone());
		Ok(())
	}

	/// Get the `ContractInfo` of the `addr` or an error if it no longer exists.
	fn address_info(addr: &T::AccountId) -> Result<ContractInfo<T>, &'static str> {
		ContractInfoOf::<T>::get(addr).ok_or("Expected contract to exist at this point.")
	}

	/// Get the `ContractInfo` of this contract or an error if it no longer exists.
	fn info(&self) -> Result<ContractInfo<T>, &'static str> {
		Self::address_info(&self.account_id)
	}

	/// Set the balance of the contract to the supplied amount.
	fn set_balance(&self, balance: BalanceOf<T>) {
		T::Currency::make_free_balance_be(&self.account_id, balance);
	}

	/// Returns `true` iff all storage entries related to code storage exist.
	fn code_exists(hash: &CodeHash<T>) -> bool {
		<PristineCode<T>>::contains_key(hash) &&
			<CodeStorage<T>>::contains_key(&hash) &&
			<OwnerInfoOf<T>>::contains_key(&hash)
	}

	/// Returns `true` iff no storage entry related to code storage exist.
	fn code_removed(hash: &CodeHash<T>) -> bool {
		!<PristineCode<T>>::contains_key(hash) &&
			!<CodeStorage<T>>::contains_key(&hash) &&
			!<OwnerInfoOf<T>>::contains_key(&hash)
	}
}

/// The funding that each account that either calls or instantiates contracts is funded with.
fn caller_funding<T: Config>() -> BalanceOf<T> {
	BalanceOf::<T>::max_value() / 2u32.into()
}

/// Load the specified contract file from disk by including it into the runtime.
///
/// We need to load a different version of ink! contracts when the benchmark is run as
/// a test. This is because ink! contracts depend on the sizes of types that are defined
/// differently in the test environment. Solang is more lax in that regard.
macro_rules! load_benchmark {
	($name:expr) => {{
		#[cfg(not(test))]
		{
			include_bytes!(concat!("../../benchmarks/", $name, ".wasm"))
		}
		#[cfg(test)]
		{
			include_bytes!(concat!("../../benchmarks/", $name, "_test.wasm"))
		}
	}};
}

benchmarks! {
	where_clause { where
		T::AccountId: UncheckedFrom<T::Hash>,
		T::AccountId: AsRef<[u8]>,
		<BalanceOf<T> as codec::HasCompact>::Type: Clone + Eq + PartialEq + sp_std::fmt::Debug + scale_info::TypeInfo + codec::Encode,
	}

	// The base weight without any actual work performed apart from the setup costs.
	on_initialize {}: {
		Storage::<T>::process_deletion_queue_batch(Weight::MAX)
	}

	#[skip_meta]
	on_initialize_per_trie_key {
		let k in 0..1024;
		let instance = Contract::<T>::with_storage(WasmModule::dummy(), k, T::Schedule::get().limits.payload_len)?;
		Storage::<T>::queue_trie_for_deletion(&instance.info()?)?;
	}: {
		Storage::<T>::process_deletion_queue_batch(Weight::MAX)
	}

	on_initialize_per_queue_item {
		let q in 0..1024.min(T::DeletionQueueDepth::get());
		for i in 0 .. q {
			let instance = Contract::<T>::with_index(i, WasmModule::dummy(), vec![])?;
			Storage::<T>::queue_trie_for_deletion(&instance.info()?)?;
			ContractInfoOf::<T>::remove(instance.account_id);
		}
	}: {
		Storage::<T>::process_deletion_queue_batch(Weight::MAX)
	}

	// This benchmarks the additional weight that is charged when a contract is executed the
	// first time after a new schedule was deployed: For every new schedule a contract needs
	// to re-run the instrumentation once.
	reinstrument {
		let c in 0 .. T::Schedule::get().limits.code_len;
		let WasmModule { code, hash, .. } = WasmModule::<T>::sized(c, Location::Call);
		Contracts::<T>::store_code_raw(code, whitelisted_caller())?;
		let schedule = T::Schedule::get();
		let mut gas_meter = GasMeter::new(Weight::MAX);
		let mut module = PrefabWasmModule::from_storage(hash, &schedule, &mut gas_meter)?;
	}: {
		Contracts::<T>::reinstrument_module(&mut module, &schedule)?;
	}

	// This benchmarks the overhead of loading a code of size `c` byte from storage and into
	// the sandbox. This does **not** include the actual execution for which the gas meter
	// is responsible. This is achieved by generating all code to the `deploy` function
	// which is in the wasm module but not executed on `call`.
	// The results are supposed to be used as `call_with_code_kb(c) - call_with_code_kb(0)`.
	call_with_code_per_byte {
		let c in 0 .. T::Schedule::get().limits.code_len;
		let instance = Contract::<T>::with_caller(
			whitelisted_caller(), WasmModule::sized(c, Location::Deploy), vec![],
		)?;
		let value = T::Currency::minimum_balance();
		let origin = RawOrigin::Signed(instance.caller.clone());
		let callee = instance.addr.clone();
	}: call(origin, callee, value, Weight::MAX, None, vec![])

	// This constructs a contract that is maximal expensive to instrument.
	// It creates a maximum number of metering blocks per byte.
	// The size of the salt influences the runtime because is is hashed in order to
	// determine the contract address. All code is generated to the `call` function so that
	// we don't benchmark the actual execution of this code but merely what it takes to load
	// a code of that size into the sandbox.
	//
	// `c`: Size of the code in kilobytes.
	// `s`: Size of the salt in kilobytes.
	//
	// # Note
	//
	// We cannot let `c` grow to the maximum code size because the code is not allowed
	// to be larger than the maximum size **after instrumentation**.
	instantiate_with_code {
		let c in 0 .. Perbill::from_percent(49).mul_ceil(T::Schedule::get().limits.code_len);
		let s in 0 .. code::max_pages::<T>() * 64 * 1024;
		let salt = vec![42u8; s as usize];
		let value = T::Currency::minimum_balance();
		let caller = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, caller_funding::<T>());
		let WasmModule { code, hash, .. } = WasmModule::<T>::sized(c, Location::Call);
		let origin = RawOrigin::Signed(caller.clone());
		let addr = Contracts::<T>::contract_address(&caller, &hash, &salt);
	}: _(origin, value, Weight::MAX, None, code, vec![], salt)
	verify {
		// the contract itself does not trigger any reserves
		let deposit = T::Currency::reserved_balance(&addr);
		// uploading the code reserves some balance in the callers account
		let code_deposit = T::Currency::reserved_balance(&caller);
		assert_eq!(
			T::Currency::free_balance(&caller),
			caller_funding::<T>() - value - deposit - code_deposit,
		);
		// contract has the full value
		assert_eq!(T::Currency::free_balance(&addr), value);
		// instantiate should leave a contract
		Contract::<T>::address_info(&addr)?;
	}

	// Instantiate uses a dummy contract constructor to measure the overhead of the instantiate.
	// `s`: Size of the salt in kilobytes.
	instantiate {
		let s in 0 .. code::max_pages::<T>() * 64 * 1024;
		let salt = vec![42u8; s as usize];
		let value = T::Currency::minimum_balance();
		let caller = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, caller_funding::<T>());
		let WasmModule { code, hash, .. } = WasmModule::<T>::dummy();
		let origin = RawOrigin::Signed(caller.clone());
		let addr = Contracts::<T>::contract_address(&caller, &hash, &salt);
		Contracts::<T>::store_code_raw(code, caller.clone())?;
	}: _(origin, value, Weight::MAX, None, hash, vec![], salt)
	verify {
		// the contract itself does not trigger any reserves
		let deposit = T::Currency::reserved_balance(&addr);
		// value was removed from the caller
		assert_eq!(T::Currency::free_balance(&caller), caller_funding::<T>() - value - deposit);
		// contract has the full value
		assert_eq!(T::Currency::free_balance(&addr), value);
		// instantiate should leave a contract
		Contract::<T>::address_info(&addr)?;
	}

	// We just call a dummy contract to measure the overhead of the call extrinsic.
	// The size of the data has no influence on the costs of this extrinsic as long as the contract
	// won't call `seal_input` in its constructor to copy the data to contract memory.
	// The dummy contract used here does not do this. The costs for the data copy is billed as
	// part of `seal_input`. The costs for invoking a contract of a specific size are not part
	// of this benchmark because we cannot know the size of the contract when issuing a call
	// transaction. See `invoke_per_code_kb` for this.
	call {
		let data = vec![42u8; 1024];
		let instance = Contract::<T>::with_caller(
			whitelisted_caller(), WasmModule::dummy(), vec![],
		)?;
		let value = T::Currency::minimum_balance();
		let origin = RawOrigin::Signed(instance.caller.clone());
		let callee = instance.addr.clone();
		let before = T::Currency::free_balance(&instance.account_id);
	}: _(origin, callee, value, Weight::MAX, None, data)
	verify {
		// the contract itself does not trigger any reserves
		let deposit = T::Currency::reserved_balance(&instance.account_id);
		// value and value transfered via call should be removed from the caller
		assert_eq!(
			T::Currency::free_balance(&instance.caller),
			caller_funding::<T>() - instance.value - value - deposit,
		);
		// contract should have received the value
		assert_eq!(T::Currency::free_balance(&instance.account_id), before + value);
		// contract should still exist
		instance.info()?;
	}

	// This constructs a contract that is maximal expensive to instrument.
	// It creates a maximum number of metering blocks per byte.
	// `c`: Size of the code in kilobytes.
	//
	// # Note
	//
	// We cannot let `c` grow to the maximum code size because the code is not allowed
	// to be larger than the maximum size **after instrumentation**.
	upload_code {
		let c in 0 .. Perbill::from_percent(50).mul_ceil(T::Schedule::get().limits.code_len);
		let caller = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, caller_funding::<T>());
		let WasmModule { code, hash, .. } = WasmModule::<T>::sized(c, Location::Call);
		let origin = RawOrigin::Signed(caller.clone());
	}: _(origin, code, None)
	verify {
		// uploading the code reserves some balance in the callers account
		assert!(T::Currency::reserved_balance(&caller) > 0u32.into());
		assert!(<Contract<T>>::code_exists(&hash));
	}

	// Removing code does not depend on the size of the contract because all the information
	// needed to verify the removal claim (refcount, owner) is stored in a separate storage
	// item (`OwnerInfoOf`).
	remove_code {
		let caller = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, caller_funding::<T>());
		let WasmModule { code, hash, .. } = WasmModule::<T>::dummy();
		let origin = RawOrigin::Signed(caller.clone());
		let uploaded = <Contracts<T>>::bare_upload_code(caller.clone(), code, None)?;
		assert_eq!(uploaded.code_hash, hash);
		assert_eq!(uploaded.deposit, T::Currency::reserved_balance(&caller));
		assert!(<Contract<T>>::code_exists(&hash));
	}: _(origin, hash)
	verify {
		// removing the code should have unreserved the deposit
		assert_eq!(T::Currency::reserved_balance(&caller), 0u32.into());
		assert!(<Contract<T>>::code_removed(&hash));
	}

	seal_caller {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let instance = Contract::<T>::new(WasmModule::getter(
			"seal_caller", r * API_BENCHMARK_BATCH_SIZE
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	seal_is_contract {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let accounts = (0 .. r * API_BENCHMARK_BATCH_SIZE)
			.map(|n| account::<T::AccountId>("account", n, 0))
			.collect::<Vec<_>>();
		let account_len = accounts.get(0).map(|i| i.encode().len()).unwrap_or(0);
		let accounts_bytes = accounts.iter().map(|a| a.encode()).flatten().collect::<Vec<_>>();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_is_contract",
				params: vec![ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: accounts_bytes
				},
			],
			call_body: Some(body::repeated_dyn(r * API_BENCHMARK_BATCH_SIZE, vec![
				Counter(0, account_len as u32), // address_ptr
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let info = instance.info()?;
		// every account would be a contract (worst case)
		for acc in accounts.iter() {
			<ContractInfoOf<T>>::insert(acc, info.clone());
		}
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	seal_caller_is_origin {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_caller_is_origin",
				params: vec![],
				return_type: Some(ValueType::I32),
			}],
			call_body: Some(body::repeated(r * API_BENCHMARK_BATCH_SIZE, &[
				Instruction::Call(0),
				Instruction::Drop,
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	seal_address {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let instance = Contract::<T>::new(WasmModule::getter(
			"seal_address", r * API_BENCHMARK_BATCH_SIZE
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	seal_gas_left {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let instance = Contract::<T>::new(WasmModule::getter(
			"seal_gas_left", r * API_BENCHMARK_BATCH_SIZE
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	seal_balance {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let instance = Contract::<T>::new(WasmModule::getter(
			"seal_balance", r * API_BENCHMARK_BATCH_SIZE
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	seal_value_transferred {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let instance = Contract::<T>::new(WasmModule::getter(
			"seal_value_transferred", r * API_BENCHMARK_BATCH_SIZE
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	seal_minimum_balance {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let instance = Contract::<T>::new(WasmModule::getter(
			"seal_minimum_balance", r * API_BENCHMARK_BATCH_SIZE
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	seal_block_number {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let instance = Contract::<T>::new(WasmModule::getter(
			"seal_block_number", r * API_BENCHMARK_BATCH_SIZE
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	seal_now {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let instance = Contract::<T>::new(WasmModule::getter(
			"seal_now", r * API_BENCHMARK_BATCH_SIZE
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	seal_weight_to_fee {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let pages = code::max_pages::<T>();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_weight_to_fee",
				params: vec![ValueType::I64, ValueType::I32, ValueType::I32],
				return_type: None,
			}],
			data_segments: vec![DataSegment {
				offset: 0,
				value: (pages * 64 * 1024 - 4).to_le_bytes().to_vec(),
			}],
			call_body: Some(body::repeated(r * API_BENCHMARK_BATCH_SIZE, &[
				Instruction::I64Const(500_000),
				Instruction::I32Const(4),
				Instruction::I32Const(0),
				Instruction::Call(0),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	seal_gas {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let code = WasmModule::<T>::from(ModuleDefinition {
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "gas",
				params: vec![ValueType::I32],
				return_type: None,
			}],
			call_body: Some(body::repeated(r * API_BENCHMARK_BATCH_SIZE, &[
				Instruction::I32Const(42),
				Instruction::Call(0),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());

	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	seal_input {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_input",
				params: vec![ValueType::I32, ValueType::I32],
				return_type: None,
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: 0u32.to_le_bytes().to_vec(),
				},
			],
			call_body: Some(body::repeated(r * API_BENCHMARK_BATCH_SIZE, &[
				Instruction::I32Const(4), // ptr where to store output
				Instruction::I32Const(0), // ptr to length
				Instruction::Call(0),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	seal_input_per_kb {
		let n in 0 .. code::max_pages::<T>() * 64;
		let pages = code::max_pages::<T>();
		let buffer_size = pages * 64 * 1024 - 4;
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_input",
				params: vec![ValueType::I32, ValueType::I32],
				return_type: None,
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: buffer_size.to_le_bytes().to_vec(),
				},
			],
			call_body: Some(body::repeated(API_BENCHMARK_BATCH_SIZE, &[
				Instruction::I32Const(4), // ptr where to store output
				Instruction::I32Const(0), // ptr to length
				Instruction::Call(0),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let data = vec![42u8; (n * 1024).min(buffer_size) as usize];
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, data)

	// We cannot call `seal_return` multiple times. Therefore our weight determination is not
	// as precise as with other APIs. Because this function can only be called once per
	// contract it cannot be used as an attack vector.
	seal_return {
		let r in 0 .. 1;
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_return",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: None,
			}],
			call_body: Some(body::repeated(r, &[
				Instruction::I32Const(0), // flags
				Instruction::I32Const(0), // data_ptr
				Instruction::I32Const(0), // data_len
				Instruction::Call(0),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	seal_return_per_kb {
		let n in 0 .. code::max_pages::<T>() * 64;
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_return",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: None,
			}],
			call_body: Some(body::plain(vec![
				Instruction::I32Const(0), // flags
				Instruction::I32Const(0), // data_ptr
				Instruction::I32Const((n * 1024) as i32), // data_len
				Instruction::Call(0),
				Instruction::End,
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// The same argument as for `seal_return` is true here.
	seal_terminate {
		let r in 0 .. 1;
		let beneficiary = account::<T::AccountId>("beneficiary", 0, 0);
		let beneficiary_bytes = beneficiary.encode();
		let beneficiary_len = beneficiary_bytes.len();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_terminate",
				params: vec![ValueType::I32, ValueType::I32],
				return_type: None,
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: beneficiary_bytes,
				},
			],
			call_body: Some(body::repeated(r, &[
				Instruction::I32Const(0), // beneficiary_ptr
				Instruction::I32Const(beneficiary_len as i32), // beneficiary_len
				Instruction::Call(0),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
		assert_eq!(T::Currency::total_balance(&beneficiary), 0u32.into());
		assert_eq!(T::Currency::free_balance(&instance.account_id), T::Currency::minimum_balance());
		assert_ne!(T::Currency::reserved_balance(&instance.account_id), 0u32.into());
	}: call(origin, instance.addr.clone(), 0u32.into(), Weight::MAX, None, vec![])
	verify {
		if r > 0 {
			assert_eq!(T::Currency::total_balance(&instance.account_id), 0u32.into());
			assert_eq!(T::Currency::total_balance(&beneficiary), T::Currency::minimum_balance());
		}
	}

	// We benchmark only for the maximum subject length. We assume that this is some lowish
	// number (< 1 KB). Therefore we are not overcharging too much in case a smaller subject is
	// used.
	seal_random {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let pages = code::max_pages::<T>();
		let subject_len = T::Schedule::get().limits.subject_len;
		assert!(subject_len < 1024);
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_random",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: None,
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: (pages * 64 * 1024 - subject_len - 4).to_le_bytes().to_vec(),
				},
			],
			call_body: Some(body::repeated(r * API_BENCHMARK_BATCH_SIZE, &[
				Instruction::I32Const(4), // subject_ptr
				Instruction::I32Const(subject_len as i32), // subject_len
				Instruction::I32Const((subject_len + 4) as i32), // out_ptr
				Instruction::I32Const(0),	// out_len_ptr
				Instruction::Call(0),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// Overhead of calling the function without any topic.
	// We benchmark for the worst case (largest event).
	seal_deposit_event {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_deposit_event",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: None,
			}],
			call_body: Some(body::repeated(r * API_BENCHMARK_BATCH_SIZE, &[
				Instruction::I32Const(0), // topics_ptr
				Instruction::I32Const(0), // topics_len
				Instruction::I32Const(0), // data_ptr
				Instruction::I32Const(0), // data_len
				Instruction::Call(0),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// Benchmark the overhead that topics generate.
	// `t`: Number of topics
	// `n`: Size of event payload in kb
	seal_deposit_event_per_topic_and_kb {
		let t in 0 .. T::Schedule::get().limits.event_topics;
		let n in 0 .. T::Schedule::get().limits.payload_len / 1024;
		let mut topics = (0..API_BENCHMARK_BATCH_SIZE)
			.map(|n| (n * t..n * t + t).map(|i| T::Hashing::hash_of(&i)).collect::<Vec<_>>().encode())
			.peekable();
		let topics_len = topics.peek().map(|i| i.len()).unwrap_or(0);
		let topics = topics.flatten().collect();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_deposit_event",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: None,
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: topics,
				},
			],
			call_body: Some(body::repeated_dyn(API_BENCHMARK_BATCH_SIZE, vec![
				Counter(0, topics_len as u32), // topics_ptr
				Regular(Instruction::I32Const(topics_len as i32)), // topics_len
				Regular(Instruction::I32Const(0)), // data_ptr
				Regular(Instruction::I32Const((n * 1024) as i32)), // data_len
				Regular(Instruction::Call(0)),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// The size of the supplied message does not influence the weight because as it is never
	// processed during on-chain execution: It is only ever read during debugging which happens
	// when the contract is called as RPC where weights do not matter.
	seal_debug_message {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let max_bytes = code::max_pages::<T>() * 64 * 1024;
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory { min_pages: 1, max_pages: 1 }),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_debug_message",
				params: vec![ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			call_body: Some(body::repeated(r * API_BENCHMARK_BATCH_SIZE, &[
				Instruction::I32Const(0), // value_ptr
				Instruction::I32Const(max_bytes as i32), // value_len
				Instruction::Call(0),
				Instruction::Drop,
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// Only the overhead of calling the function itself with minimal arguments.
	// The contract is a bit more complex because I needs to use different keys in order
	// to generate unique storage accesses. However, it is still dominated by the storage
	// accesses.
	#[skip_meta]
	seal_set_storage {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let keys = (0 .. r * API_BENCHMARK_BATCH_SIZE)
			.map(|n| T::Hashing::hash_of(&n).as_ref().to_vec())
			.collect::<Vec<_>>();
		let key_len = keys.get(0).map(|i| i.len() as u32).unwrap_or(0);
		let key_bytes = keys.iter().flatten().cloned().collect::<Vec<_>>();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "__unstable__",
				name: "seal_set_storage",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: key_bytes,
				},
			],
			call_body: Some(body::repeated_dyn(r * API_BENCHMARK_BATCH_SIZE, vec![
				Counter(0, key_len as u32), // key_ptr
				Regular(Instruction::I32Const(0)), // value_ptr
				Regular(Instruction::I32Const(0)), // value_len
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let info = instance.info()?;
		for key in keys {
			Storage::<T>::write(
				&info.trie_id,
				key.as_slice().try_into().map_err(|e| "Key has wrong length")?,
				Some(vec![]),
				None,
				false,
			)
			.map_err(|_| "Failed to write to storage during setup.")?;
		}
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[skip_meta]
	seal_set_storage_per_new_kb {
		let n in 0 .. T::Schedule::get().limits.payload_len / 1024;
		let keys = (0 .. API_BENCHMARK_BATCH_SIZE)
			.map(|n| T::Hashing::hash_of(&n).as_ref().to_vec())
			.collect::<Vec<_>>();
		let key_len = keys.get(0).map(|i| i.len() as u32).unwrap_or(0);
		let key_bytes = keys.iter().flatten().cloned().collect::<Vec<_>>();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "__unstable__",
				name: "seal_set_storage",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: key_bytes,
				},
			],
			call_body: Some(body::repeated_dyn(API_BENCHMARK_BATCH_SIZE, vec![
				Counter(0, key_len as u32), // key_ptr
				Regular(Instruction::I32Const(0)), // value_ptr
				Regular(Instruction::I32Const((n * 1024) as i32)), // value_len
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let info = instance.info()?;
		for key in keys {
			Storage::<T>::write(
				&info.trie_id,
				key.as_slice().try_into().map_err(|e| "Key has wrong length")?,
				Some(vec![]),
				None,
				false,
			)
			.map_err(|_| "Failed to write to storage during setup.")?;
		}
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[skip_meta]
	seal_set_storage_per_old_kb {
		let n in 0 .. T::Schedule::get().limits.payload_len / 1024;
		let keys = (0 .. API_BENCHMARK_BATCH_SIZE)
			.map(|n| T::Hashing::hash_of(&n).as_ref().to_vec())
			.collect::<Vec<_>>();
		let key_len = keys.get(0).map(|i| i.len() as u32).unwrap_or(0);
		let key_bytes = keys.iter().flatten().cloned().collect::<Vec<_>>();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "__unstable__",
				name: "seal_set_storage",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: key_bytes,
				},
			],
			call_body: Some(body::repeated_dyn(API_BENCHMARK_BATCH_SIZE, vec![
				Counter(0, key_len as u32), // key_ptr
				Regular(Instruction::I32Const(0)), // value_ptr
				Regular(Instruction::I32Const(0)), // value_len
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let info = instance.info()?;
		for key in keys {
			Storage::<T>::write(
				&info.trie_id,
				key.as_slice().try_into().map_err(|e| "Key has wrong length")?,
				Some(vec![42u8; (n * 1024) as usize]),
				None,
				false,
			)
			.map_err(|_| "Failed to write to storage during setup.")?;
		}
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// Similar to seal_set_storage. However, we store all the keys that we are about to
	// delete beforehand in order to prevent any optimizations that could occur when
	// deleting a non existing key.
	#[skip_meta]
	seal_clear_storage {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let keys = (0 .. r * API_BENCHMARK_BATCH_SIZE)
			.map(|n| T::Hashing::hash_of(&n).as_ref().to_vec())
			.collect::<Vec<_>>();
		let key_bytes = keys.iter().flatten().cloned().collect::<Vec<_>>();
		let key_len = keys.get(0).map(|i| i.len() as u32).unwrap_or(0);
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "__unstable__",
				name: "seal_clear_storage",
				params: vec![ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: key_bytes,
				},
			],
			call_body: Some(body::repeated_dyn(r * API_BENCHMARK_BATCH_SIZE, vec![
				Counter(0, key_len as u32),
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let info = instance.info()?;
		for key in keys {
			Storage::<T>::write(
				&info.trie_id,
				key.as_slice().try_into().map_err(|e| "Key has wrong length")?,
				Some(vec![]),
				None,
				false,
			)
			.map_err(|_| "Failed to write to storage during setup.")?;
		}
		<ContractInfoOf<T>>::insert(&instance.account_id, info.clone());
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[skip_meta]
	seal_clear_storage_per_kb {
		let n in 0 .. T::Schedule::get().limits.payload_len / 1024;
		let keys = (0 .. API_BENCHMARK_BATCH_SIZE)
			.map(|n| T::Hashing::hash_of(&n).as_ref().to_vec())
			.collect::<Vec<_>>();
		let key_len = keys.get(0).map(|i| i.len() as u32).unwrap_or(0);
		let key_bytes = keys.iter().flatten().cloned().collect::<Vec<_>>();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "__unstable__",
				name: "seal_clear_storage",
				params: vec![ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: key_bytes,
				},
			],
			call_body: Some(body::repeated_dyn(API_BENCHMARK_BATCH_SIZE, vec![
				Counter(0, key_len as u32), // key_ptr
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let info = instance.info()?;
		for key in keys {
			Storage::<T>::write(
				&info.trie_id,
				key.as_slice().try_into().map_err(|e| "Key has wrong length")?,
				Some(vec![42u8; (n * 1024) as usize]),
				None,
				false,
			)
			.map_err(|_| "Failed to write to storage during setup.")?;
		}
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// We make sure that all storage accesses are to unique keys.
	#[skip_meta]
	seal_get_storage {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let keys = (0 .. r * API_BENCHMARK_BATCH_SIZE)
			.map(|n| T::Hashing::hash_of(&n).as_ref().to_vec())
			.collect::<Vec<_>>();
		let key_len = keys.get(0).map(|i| i.len() as u32).unwrap_or(0);
		let key_bytes = keys.iter().flatten().cloned().collect::<Vec<_>>();
		let key_bytes_len = key_bytes.len();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_get_storage",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: key_bytes,
				},
				DataSegment {
					offset: key_bytes_len as u32,
					value: T::Schedule::get().limits.payload_len.to_le_bytes().into(),
				},
			],
			call_body: Some(body::repeated_dyn(r * API_BENCHMARK_BATCH_SIZE, vec![
				Counter(0, key_len as u32), // key_ptr
				Regular(Instruction::I32Const((key_bytes_len + 4) as i32)), // out_ptr
				Regular(Instruction::I32Const(key_bytes_len as i32)), // out_len_ptr
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let info = instance.info()?;
		for key in keys {
			Storage::<T>::write(
				&info.trie_id,
				key.as_slice().try_into().map_err(|e| "Key has wrong length")?,
				Some(vec![]),
				None,
				false,
			)
			.map_err(|_| "Failed to write to storage during setup.")?;
		}
		<ContractInfoOf<T>>::insert(&instance.account_id, info.clone());
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[skip_meta]
	seal_get_storage_per_kb {
		let n in 0 .. T::Schedule::get().limits.payload_len / 1024;
		let keys = (0 .. API_BENCHMARK_BATCH_SIZE)
			.map(|n| T::Hashing::hash_of(&n).as_ref().to_vec())
			.collect::<Vec<_>>();
		let key_len = keys.get(0).map(|i| i.len() as u32).unwrap_or(0);
		let key_bytes = keys.iter().flatten().cloned().collect::<Vec<_>>();
		let key_bytes_len = key_bytes.len();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_get_storage",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: key_bytes,
				},
				DataSegment {
					offset: key_bytes_len as u32,
					value: T::Schedule::get().limits.payload_len.to_le_bytes().into(),
				},
			],
			call_body: Some(body::repeated_dyn(API_BENCHMARK_BATCH_SIZE, vec![
				Counter(0, key_len as u32), // key_ptr
				Regular(Instruction::I32Const((key_bytes_len + 4) as i32)), // out_ptr
				Regular(Instruction::I32Const(key_bytes_len as i32)), // out_len_ptr
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let info = instance.info()?;
		for key in keys {
			Storage::<T>::write(
				&info.trie_id,
				key.as_slice().try_into().map_err(|e| "Key has wrong length")?,
				Some(vec![42u8; (n * 1024) as usize]),
				None,
				false,
			)
			.map_err(|_| "Failed to write to storage during setup.")?;
		}
		<ContractInfoOf<T>>::insert(&instance.account_id, info.clone());
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// We make sure that all storage accesses are to unique keys.
	#[skip_meta]
	seal_contains_storage {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let keys = (0 .. r * API_BENCHMARK_BATCH_SIZE)
			.map(|n| T::Hashing::hash_of(&n).as_ref().to_vec())
			.collect::<Vec<_>>();
		let key_len = keys.get(0).map(|i| i.len() as u32).unwrap_or(0);
		let key_bytes = keys.iter().flatten().cloned().collect::<Vec<_>>();
		let key_bytes_len = key_bytes.len();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "__unstable__",
				name: "seal_contains_storage",
				params: vec![ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: key_bytes,
				},
			],
			call_body: Some(body::repeated_dyn(r * API_BENCHMARK_BATCH_SIZE, vec![
				Counter(0, key_len as u32), // key_ptr
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let info = instance.info()?;
		for key in keys {
			Storage::<T>::write(
				&info.trie_id,
				key.as_slice().try_into().map_err(|e| "Key has wrong length")?,
				Some(vec![]),
				None,
				false,
			)
			.map_err(|_| "Failed to write to storage during setup.")?;
		}
		<ContractInfoOf<T>>::insert(&instance.account_id, info.clone());
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[skip_meta]
	seal_contains_storage_per_kb {
		let n in 0 .. T::Schedule::get().limits.payload_len / 1024;
		let keys = (0 .. API_BENCHMARK_BATCH_SIZE)
			.map(|n| T::Hashing::hash_of(&n).as_ref().to_vec())
			.collect::<Vec<_>>();
		let key_len = keys.get(0).map(|i| i.len() as u32).unwrap_or(0);
		let key_bytes = keys.iter().flatten().cloned().collect::<Vec<_>>();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "__unstable__",
				name: "seal_contains_storage",
				params: vec![ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: key_bytes,
				},
			],
			call_body: Some(body::repeated_dyn(API_BENCHMARK_BATCH_SIZE, vec![
				Counter(0, key_len as u32), // key_ptr
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let info = instance.info()?;
		for key in keys {
			Storage::<T>::write(
				&info.trie_id,
				key.as_slice().try_into().map_err(|e| "Key has wrong length")?,
				Some(vec![42u8; (n * 1024) as usize]),
				None,
				false,
			)
			.map_err(|_| "Failed to write to storage during setup.")?;
		}
		<ContractInfoOf<T>>::insert(&instance.account_id, info.clone());
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[skip_meta]
	seal_take_storage {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let keys = (0 .. r * API_BENCHMARK_BATCH_SIZE)
			.map(|n| T::Hashing::hash_of(&n).as_ref().to_vec())
			.collect::<Vec<_>>();
		let key_len = keys.get(0).map(|i| i.len() as u32).unwrap_or(0);
		let key_bytes = keys.iter().flatten().cloned().collect::<Vec<_>>();
		let key_bytes_len = key_bytes.len();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "__unstable__",
				name: "seal_take_storage",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: key_bytes,
				},
				DataSegment {
					offset: key_bytes_len as u32,
					value: T::Schedule::get().limits.payload_len.to_le_bytes().into(),
				},
			],
			call_body: Some(body::repeated_dyn(r * API_BENCHMARK_BATCH_SIZE, vec![
				Counter(0, key_len as u32), // key_ptr
				Regular(Instruction::I32Const((key_bytes_len + 4) as i32)), // out_ptr
				Regular(Instruction::I32Const(key_bytes_len as i32)), // out_len_ptr
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let info = instance.info()?;
		for key in keys {
			Storage::<T>::write(
				&info.trie_id,
				key.as_slice().try_into().map_err(|e| "Key has wrong length")?,
				Some(vec![]),
				None,
				false,
			)
			.map_err(|_| "Failed to write to storage during setup.")?;
		}
		<ContractInfoOf<T>>::insert(&instance.account_id, info.clone());
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[skip_meta]
	seal_take_storage_per_kb {
		let n in 0 .. T::Schedule::get().limits.payload_len / 1024;
		let keys = (0 .. API_BENCHMARK_BATCH_SIZE)
			.map(|n| T::Hashing::hash_of(&n).as_ref().to_vec())
			.collect::<Vec<_>>();
		let key_len = keys.get(0).map(|i| i.len() as u32).unwrap_or(0);
		let key_bytes = keys.iter().flatten().cloned().collect::<Vec<_>>();
		let key_bytes_len = key_bytes.len();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "__unstable__",
				name: "seal_take_storage",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: key_bytes,
				},
				DataSegment {
					offset: key_bytes_len as u32,
					value: T::Schedule::get().limits.payload_len.to_le_bytes().into(),
				},
			],
			call_body: Some(body::repeated_dyn(API_BENCHMARK_BATCH_SIZE, vec![
				Counter(0, key_len as u32), // key_ptr
				Regular(Instruction::I32Const((key_bytes_len + 4) as i32)), // out_ptr
				Regular(Instruction::I32Const(key_bytes_len as i32)), // out_len_ptr
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let info = instance.info()?;
		for key in keys {
			Storage::<T>::write(
				&info.trie_id,
				key.as_slice().try_into().map_err(|e| "Key has wrong length")?,
				Some(vec![42u8; (n * 1024) as usize]),
				None,
				false,
			)
			.map_err(|_| "Failed to write to storage during setup.")?;
		}
		<ContractInfoOf<T>>::insert(&instance.account_id, info.clone());
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// We transfer to unique accounts.
	seal_transfer {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let accounts = (0..r * API_BENCHMARK_BATCH_SIZE)
			.map(|i| account::<T::AccountId>("receiver", i, 0))
			.collect::<Vec<_>>();
		let account_len = accounts.get(0).map(|i| i.encode().len()).unwrap_or(0);
		let account_bytes = accounts.iter().flat_map(|x| x.encode()).collect();
		let value = T::Currency::minimum_balance();
		assert!(value > 0u32.into());
		let value_bytes = value.encode();
		let value_len = value_bytes.len();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_transfer",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: value_bytes,
				},
				DataSegment {
					offset: value_len as u32,
					value: account_bytes,
				},
			],
			call_body: Some(body::repeated_dyn(r * API_BENCHMARK_BATCH_SIZE, vec![
				Counter(value_len as u32, account_len as u32), // account_ptr
				Regular(Instruction::I32Const(account_len as i32)), // account_len
				Regular(Instruction::I32Const(0)), // value_ptr
				Regular(Instruction::I32Const(value_len as i32)), // value_len
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		instance.set_balance(value * (r * API_BENCHMARK_BATCH_SIZE + 1).into());
		let origin = RawOrigin::Signed(instance.caller.clone());
		for account in &accounts {
			assert_eq!(T::Currency::total_balance(account), 0u32.into());
		}
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])
	verify {
		for account in &accounts {
			assert_eq!(T::Currency::total_balance(account), value);
		}
	}

	// We call unique accounts.
	seal_call {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let dummy_code = WasmModule::<T>::dummy_with_bytes(0);
		let callees = (0..r * API_BENCHMARK_BATCH_SIZE)
			.map(|i| Contract::with_index(i + 1, dummy_code.clone(), vec![]))
			.collect::<Result<Vec<_>, _>>()?;
		let callee_len = callees.get(0).map(|i| i.account_id.encode().len()).unwrap_or(0);
		let callee_bytes = callees.iter().flat_map(|x| x.account_id.encode()).collect();
		let value: BalanceOf<T> = 0u32.into();
		let value_bytes = value.encode();
		let value_len = value_bytes.len();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_call",
				params: vec![
					ValueType::I32,
					ValueType::I32,
					ValueType::I64,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
				],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: value_bytes,
				},
				DataSegment {
					offset: value_len as u32,
					value: callee_bytes,
				},
			],
			call_body: Some(body::repeated_dyn(r * API_BENCHMARK_BATCH_SIZE, vec![
				Counter(value_len as u32, callee_len as u32), // callee_ptr
				Regular(Instruction::I32Const(callee_len as i32)), // callee_len
				Regular(Instruction::I64Const(0)), // gas
				Regular(Instruction::I32Const(0)), // value_ptr
				Regular(Instruction::I32Const(value_len as i32)), // value_len
				Regular(Instruction::I32Const(0)), // input_data_ptr
				Regular(Instruction::I32Const(0)), // input_data_len
				Regular(Instruction::I32Const(SENTINEL as i32)), // output_ptr
				Regular(Instruction::I32Const(0)), // output_len_ptr
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	seal_delegate_call {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let hashes = (0..r * API_BENCHMARK_BATCH_SIZE)
			.map(|i| {
				let code = WasmModule::<T>::dummy_with_bytes(i);
				Contracts::<T>::store_code_raw(code.code, whitelisted_caller())?;
				Ok(code.hash)
			})
			.collect::<Result<Vec<_>, &'static str>>()?;
		let hash_len = hashes.get(0).map(|x| x.encode().len()).unwrap_or(0);
		let hashes_bytes = hashes.iter().flat_map(|x| x.encode()).collect::<Vec<_>>();
		let hashes_len = hashes_bytes.len();
		let hashes_offset = 0;

		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "__unstable__",
				name: "seal_delegate_call",
				params: vec![
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
				],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: hashes_offset as u32,
					value: hashes_bytes,
				},
			],
			call_body: Some(body::repeated_dyn(r * API_BENCHMARK_BATCH_SIZE, vec![
				Regular(Instruction::I32Const(0)), // flags
				Counter(hashes_offset as u32, hash_len as u32), // code_hash_ptr
				Regular(Instruction::I32Const(0)), // input_data_ptr
				Regular(Instruction::I32Const(0)), // input_data_len
				Regular(Instruction::I32Const(u32::max_value() as i32)), // output_ptr
				Regular(Instruction::I32Const(0)), // output_len_ptr
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let callee = instance.addr.clone();
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, callee, 0u32.into(), Weight::MAX, None, vec![])

	seal_call_per_transfer_clone_kb {
		let t in 0 .. 1;
		let c in 0 .. code::max_pages::<T>() * 64;
		let callees = (0..API_BENCHMARK_BATCH_SIZE)
			.map(|i| Contract::with_index(i + 1, <WasmModule<T>>::dummy(), vec![]))
			.collect::<Result<Vec<_>, _>>()?;
		let callee_len = callees.get(0).map(|i| i.account_id.encode().len()).unwrap_or(0);
		let callee_bytes = callees.iter().flat_map(|x| x.account_id.encode()).collect::<Vec<_>>();
		let value: BalanceOf<T> = t.into();
		let value_bytes = value.encode();
		let value_len = value_bytes.len();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal1",
				name: "seal_call",
				params: vec![
					ValueType::I32,
					ValueType::I32,
					ValueType::I64,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
				],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: value_bytes,
				},
				DataSegment {
					offset: value_len as u32,
					value: callee_bytes,
				},
			],
			call_body: Some(body::repeated_dyn(API_BENCHMARK_BATCH_SIZE, vec![
				Regular(Instruction::I32Const(CallFlags::CLONE_INPUT.bits() as i32)), // flags
				Counter(value_len as u32, callee_len as u32), // callee_ptr
				Regular(Instruction::I64Const(0)), // gas
				Regular(Instruction::I32Const(0)), // value_ptr
				Regular(Instruction::I32Const(0)), // input_data_ptr
				Regular(Instruction::I32Const(0)), // input_data_len
				Regular(Instruction::I32Const(SENTINEL as i32)), // output_ptr
				Regular(Instruction::I32Const(0)), // output_len_ptr
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
		let bytes = vec![42; (c * 1024) as usize];
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, bytes)

	// We assume that every instantiate sends at least the minimum balance.
	seal_instantiate {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let hashes = (0..r * API_BENCHMARK_BATCH_SIZE)
			.map(|i| {
				let code = WasmModule::<T>::from(ModuleDefinition {
					memory: Some(ImportedMemory::max::<T>()),
					call_body: Some(body::plain(vec![
						// we need to add this in order to make contracts unique
						// so that they can be deployed from the same sender
						Instruction::I32Const(i as i32),
						Instruction::Drop,
						Instruction::End,
					])),
					.. Default::default()
				});
				Contracts::<T>::store_code_raw(code.code, whitelisted_caller())?;
				Ok(code.hash)
			})
			.collect::<Result<Vec<_>, &'static str>>()?;
		let hash_len = hashes.get(0).map(|x| x.encode().len()).unwrap_or(0);
		let hashes_bytes = hashes.iter().flat_map(|x| x.encode()).collect::<Vec<_>>();
		let hashes_len = hashes_bytes.len();
		let value = T::Currency::minimum_balance();
		assert!(value > 0u32.into());
		let value_bytes = value.encode();
		let value_len = value_bytes.len();
		let addr_len = T::AccountId::max_encoded_len();

		// offsets where to place static data in contract memory
		let value_offset = 0;
		let hashes_offset = value_offset + value_len;
		let addr_len_offset = hashes_offset + hashes_len;
		let addr_offset = addr_len_offset + addr_len;

		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_instantiate",
				params: vec![
					ValueType::I32,
					ValueType::I32,
					ValueType::I64,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
				],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: value_offset as u32,
					value: value_bytes,
				},
				DataSegment {
					offset: hashes_offset as u32,
					value: hashes_bytes,
				},
				DataSegment {
					offset: addr_len_offset as u32,
					value: addr_len.to_le_bytes().into(),
				},
			],
			call_body: Some(body::repeated_dyn(r * API_BENCHMARK_BATCH_SIZE, vec![
				Counter(hashes_offset as u32, hash_len as u32), // code_hash_ptr
				Regular(Instruction::I32Const(hash_len as i32)), // code_hash_len
				Regular(Instruction::I64Const(0)), // gas
				Regular(Instruction::I32Const(value_offset as i32)), // value_ptr
				Regular(Instruction::I32Const(value_len as i32)), // value_len
				Regular(Instruction::I32Const(0)), // input_data_ptr
				Regular(Instruction::I32Const(0)), // input_data_len
				Regular(Instruction::I32Const(addr_offset as i32)), // address_ptr
				Regular(Instruction::I32Const(addr_len_offset as i32)), // address_len_ptr
				Regular(Instruction::I32Const(SENTINEL as i32)), // output_ptr
				Regular(Instruction::I32Const(0)), // output_len_ptr
				Regular(Instruction::I32Const(0)), // salt_ptr
				Regular(Instruction::I32Const(0)), // salt_ptr_len
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		instance.set_balance(value * (r * API_BENCHMARK_BATCH_SIZE + 1).into());
		let origin = RawOrigin::Signed(instance.caller.clone());
		let callee = instance.addr.clone();
		let addresses = hashes
			.iter()
			.map(|hash| Contracts::<T>::contract_address(
				&instance.account_id, hash, &[],
			))
			.collect::<Vec<_>>();

		for addr in &addresses {
			if let Some(_) = ContractInfoOf::<T>::get(&addr) {
				return Err("Expected that contract does not exist at this point.".into());
			}
		}
	}: call(origin, callee, 0u32.into(), Weight::MAX, None, vec![])
	verify {
		for addr in &addresses {
			ContractInfoOf::<T>::get(&addr)
				.ok_or_else(|| "Contract should have been instantiated")?;
		}
	}

	seal_instantiate_per_transfer_salt_kb {
		let t in 0 .. 1;
		let s in 0 .. (code::max_pages::<T>() - 1) * 64;
		let callee_code = WasmModule::<T>::dummy();
		let hash = callee_code.hash.clone();
		let hash_bytes = callee_code.hash.encode();
		let hash_len = hash_bytes.len();
		Contracts::<T>::store_code_raw(callee_code.code, whitelisted_caller())?;
		let salts = (0..API_BENCHMARK_BATCH_SIZE).map(|x| x.encode()).collect::<Vec<_>>();
		let salt_len = salts.get(0).map(|x| x.len()).unwrap_or(0);
		let salt_bytes = salts.iter().cloned().flatten().collect::<Vec<_>>();
		let salts_len = salt_bytes.len();
		let value: BalanceOf<T> = t.into();
		let value_bytes = value.encode();
		let value_len = value_bytes.len();
		let addr_len = T::AccountId::max_encoded_len();

		// offsets where to place static data in contract memory
		let salt_offset = 0;
		let value_offset = salts_len;
		let hash_offset = value_offset + value_len;
		let addr_len_offset = hash_offset + hash_len;

		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_instantiate",
				params: vec![
					ValueType::I32,
					ValueType::I32,
					ValueType::I64,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
					ValueType::I32,
				],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: salt_offset as u32,
					value: salt_bytes,
				},
				DataSegment {
					offset: value_offset as u32,
					value: value_bytes,
				},
				DataSegment {
					offset: hash_offset as u32,
					value: hash_bytes,
				},
				DataSegment {
					offset: addr_len_offset as u32,
					value: (addr_len as u32).to_le_bytes().into(),
				},
			],
			call_body: Some(body::repeated_dyn(API_BENCHMARK_BATCH_SIZE, vec![
				Regular(Instruction::I32Const(hash_offset as i32)), // code_hash_ptr
				Regular(Instruction::I32Const(hash_len as i32)), // code_hash_len
				Regular(Instruction::I64Const(0)), // gas
				Regular(Instruction::I32Const(value_offset as i32)), // value_ptr
				Regular(Instruction::I32Const(value_len as i32)), // value_len
				Regular(Instruction::I32Const(0)), // input_data_ptr
				Regular(Instruction::I32Const(0)), // input_data_len
				Regular(Instruction::I32Const((addr_len_offset + addr_len) as i32)), // address_ptr
				Regular(Instruction::I32Const(addr_len_offset as i32)), // address_len_ptr
				Regular(Instruction::I32Const(SENTINEL as i32)), // output_ptr
				Regular(Instruction::I32Const(0)), // output_len_ptr
				Counter(salt_offset as u32, salt_len as u32), // salt_ptr
				Regular(Instruction::I32Const((s * 1024).max(salt_len as u32) as i32)), // salt_len
				Regular(Instruction::Call(0)),
				Regular(Instruction::I32Eqz),
				Regular(Instruction::If(BlockType::NoResult)),
				Regular(Instruction::Nop),
				Regular(Instruction::Else),
				Regular(Instruction::Unreachable),
				Regular(Instruction::End),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		instance.set_balance(value * (API_BENCHMARK_BATCH_SIZE + 1).into());
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// Only the overhead of calling the function itself with minimal arguments.
	seal_hash_sha2_256 {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let instance = Contract::<T>::new(WasmModule::hasher(
			"seal_hash_sha2_256", r * API_BENCHMARK_BATCH_SIZE, 0,
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// `n`: Input to hash in kilobytes
	seal_hash_sha2_256_per_kb {
		let n in 0 .. code::max_pages::<T>() * 64;
		let instance = Contract::<T>::new(WasmModule::hasher(
			"seal_hash_sha2_256", API_BENCHMARK_BATCH_SIZE, n * 1024,
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// Only the overhead of calling the function itself with minimal arguments.
	seal_hash_keccak_256 {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let instance = Contract::<T>::new(WasmModule::hasher(
			"seal_hash_keccak_256", r * API_BENCHMARK_BATCH_SIZE, 0,
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// `n`: Input to hash in kilobytes
	seal_hash_keccak_256_per_kb {
		let n in 0 .. code::max_pages::<T>() * 64;
		let instance = Contract::<T>::new(WasmModule::hasher(
			"seal_hash_keccak_256", API_BENCHMARK_BATCH_SIZE, n * 1024,
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// Only the overhead of calling the function itself with minimal arguments.
	seal_hash_blake2_256 {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let instance = Contract::<T>::new(WasmModule::hasher(
			"seal_hash_blake2_256", r * API_BENCHMARK_BATCH_SIZE, 0,
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// `n`: Input to hash in kilobytes
	seal_hash_blake2_256_per_kb {
		let n in 0 .. code::max_pages::<T>() * 64;
		let instance = Contract::<T>::new(WasmModule::hasher(
			"seal_hash_blake2_256", API_BENCHMARK_BATCH_SIZE, n * 1024,
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// Only the overhead of calling the function itself with minimal arguments.
	seal_hash_blake2_128 {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let instance = Contract::<T>::new(WasmModule::hasher(
			"seal_hash_blake2_128", r * API_BENCHMARK_BATCH_SIZE, 0,
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// `n`: Input to hash in kilobytes
	seal_hash_blake2_128_per_kb {
		let n in 0 .. code::max_pages::<T>() * 64;
		let instance = Contract::<T>::new(WasmModule::hasher(
			"seal_hash_blake2_128", API_BENCHMARK_BATCH_SIZE, n * 1024,
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// Only calling the function itself with valid arguments.
	// It generates different private keys and signatures for the message "Hello world".
	seal_ecdsa_recover {
		let r in 0 .. API_BENCHMARK_BATCHES;

		let message_hash = sp_io::hashing::blake2_256("Hello world".as_bytes());
		let key_type = sp_core::crypto::KeyTypeId(*b"code");
		let signatures = (0..r * API_BENCHMARK_BATCH_SIZE)
			.map(|i| {
				let pub_key = sp_io::crypto::ecdsa_generate(key_type, None);
				let sig = sp_io::crypto::ecdsa_sign_prehashed(key_type, &pub_key, &message_hash).expect("Generates signature");
				AsRef::<[u8; 65]>::as_ref(&sig).to_vec()
			})
			.collect::<Vec<_>>();
		let signatures = signatures.iter().flatten().cloned().collect::<Vec<_>>();
		let signatures_bytes_len = signatures.len() as i32;

		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "__unstable__",
				name: "seal_ecdsa_recover",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: message_hash[..].to_vec(),
				},
				DataSegment {
					offset: 32,
					value: signatures,
				},
			],
			call_body: Some(body::repeated_dyn(r * API_BENCHMARK_BATCH_SIZE, vec![
				Counter(32, 65), // signature_ptr
				Regular(Instruction::I32Const(0)), // message_hash_ptr
				Regular(Instruction::I32Const(signatures_bytes_len + 32)), // output_len_ptr
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	seal_set_code_hash {
		let r in 0 .. API_BENCHMARK_BATCHES;
		let code_hashes = (0..r * API_BENCHMARK_BATCH_SIZE)
			.map(|i| {
				let new_code = WasmModule::<T>::dummy_with_bytes(i);
				Contracts::<T>::store_code_raw(new_code.code, whitelisted_caller())?;
				Ok(new_code.hash)
			})
			.collect::<Result<Vec<_>, &'static str>>()?;
		let code_hash_len = code_hashes.get(0).map(|x| x.encode().len()).unwrap_or(0);
		let code_hashes_bytes = code_hashes.iter().flat_map(|x| x.encode()).collect::<Vec<_>>();
		let code_hashes_len = code_hashes_bytes.len();

		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "__unstable__",
				name: "seal_set_code_hash",
				params: vec![
					ValueType::I32,
				],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: code_hashes_bytes,
				},
			],
			call_body: Some(body::repeated_dyn(r * API_BENCHMARK_BATCH_SIZE, vec![
				Counter(0, code_hash_len as u32), // code_hash_ptr
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// We make the assumption that pushing a constant and dropping a value takes roughly
	// the same amount of time. We follow that `t.load` and `drop` both have the weight
	// of this benchmark / 2. We need to make this assumption because there is no way
	// to measure them on their own using a valid wasm module. We need their individual
	// values to derive the weight of individual instructions (by substraction) from
	// benchmarks that include those for parameter pushing and return type dropping.
	// We call the weight of `t.load` and `drop`: `w_param`.
	// The weight that would result from the respective benchmark we call: `w_bench`.
	//
	// w_i{32,64}const = w_drop = w_bench / 2
	instr_i64const {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			call_body: Some(body::repeated_dyn(r * INSTR_BENCHMARK_BATCH_SIZE, vec![
				RandomI64Repeated(1),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	// w_i{32,64}load = w_bench - 2 * w_param
	instr_i64load {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			call_body: Some(body::repeated_dyn(r * INSTR_BENCHMARK_BATCH_SIZE, vec![
				RandomUnaligned(0, code::max_pages::<T>() * 64 * 1024 - 8),
				Regular(Instruction::I64Load(3, 0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	// w_i{32,64}store{...} = w_bench - 2 * w_param
	instr_i64store {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			call_body: Some(body::repeated_dyn(r * INSTR_BENCHMARK_BATCH_SIZE, vec![
				RandomUnaligned(0, code::max_pages::<T>() * 64 * 1024 - 8),
				RandomI64Repeated(1),
				Regular(Instruction::I64Store(3, 0)),
			])),
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	// w_select = w_bench - 4 * w_param
	instr_select {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			call_body: Some(body::repeated_dyn(r * INSTR_BENCHMARK_BATCH_SIZE, vec![
				RandomI64Repeated(1),
				RandomI64Repeated(1),
				RandomI32(0, 2),
				Regular(Instruction::Select),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	// w_if = w_bench - 3 * w_param
	instr_if {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			call_body: Some(body::repeated_dyn(r * INSTR_BENCHMARK_BATCH_SIZE, vec![
				RandomI32(0, 2),
				Regular(Instruction::If(BlockType::Value(ValueType::I64))),
				RandomI64Repeated(1),
				Regular(Instruction::Else),
				RandomI64Repeated(1),
				Regular(Instruction::End),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	// w_br = w_bench - 2 * w_param
	// Block instructions are not counted.
	instr_br {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			call_body: Some(body::repeated_dyn(r * INSTR_BENCHMARK_BATCH_SIZE, vec![
				Regular(Instruction::Block(BlockType::NoResult)),
				Regular(Instruction::Block(BlockType::NoResult)),
				Regular(Instruction::Block(BlockType::NoResult)),
				Regular(Instruction::Br(1)),
				RandomI64Repeated(1),
				Regular(Instruction::Drop),
				Regular(Instruction::End),
				RandomI64Repeated(1),
				Regular(Instruction::Drop),
				Regular(Instruction::End),
				RandomI64Repeated(1),
				Regular(Instruction::Drop),
				Regular(Instruction::End),
			])),
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	// w_br_if = w_bench - 3 * w_param
	// Block instructions are not counted.
	instr_br_if {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			call_body: Some(body::repeated_dyn(r * INSTR_BENCHMARK_BATCH_SIZE, vec![
				Regular(Instruction::Block(BlockType::NoResult)),
				Regular(Instruction::Block(BlockType::NoResult)),
				Regular(Instruction::Block(BlockType::NoResult)),
				Regular(Instruction::I32Const(1)),
				Regular(Instruction::BrIf(1)),
				RandomI64Repeated(1),
				Regular(Instruction::Drop),
				Regular(Instruction::End),
				RandomI64Repeated(1),
				Regular(Instruction::Drop),
				Regular(Instruction::End),
				RandomI64Repeated(1),
				Regular(Instruction::Drop),
				Regular(Instruction::End),
			])),
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	// w_br_table = w_bench - 3 * w_param
	// Block instructions are not counted.
	instr_br_table {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let table = Box::new(BrTableData {
			table: Box::new([1, 1, 1]),
			default: 1,
		});
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			call_body: Some(body::repeated_dyn(r * INSTR_BENCHMARK_BATCH_SIZE, vec![
				Regular(Instruction::Block(BlockType::NoResult)),
				Regular(Instruction::Block(BlockType::NoResult)),
				Regular(Instruction::Block(BlockType::NoResult)),
				RandomI32(0, 4),
				Regular(Instruction::BrTable(table)),
				RandomI64Repeated(1),
				Regular(Instruction::Drop),
				Regular(Instruction::End),
				RandomI64Repeated(1),
				Regular(Instruction::Drop),
				Regular(Instruction::End),
				RandomI64Repeated(1),
				Regular(Instruction::Drop),
				Regular(Instruction::End),
			])),
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	// w_br_table_per_entry = w_bench
	instr_br_table_per_entry {
		let e in 1 .. T::Schedule::get().limits.br_table_size;
		let entry: Vec<u32> = [0, 1].iter()
			.cloned()
			.cycle()
			.take((e / 2) as usize).collect();
		let table = Box::new(BrTableData {
			table: entry.into_boxed_slice(),
			default: 0,
		});
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			call_body: Some(body::repeated_dyn(INSTR_BENCHMARK_BATCH_SIZE, vec![
				Regular(Instruction::Block(BlockType::NoResult)),
				Regular(Instruction::Block(BlockType::NoResult)),
				Regular(Instruction::Block(BlockType::NoResult)),
				RandomI32(0, (e + 1) as i32), // Make sure the default entry is also used
				Regular(Instruction::BrTable(table)),
				RandomI64Repeated(1),
				Regular(Instruction::Drop),
				Regular(Instruction::End),
				RandomI64Repeated(1),
				Regular(Instruction::Drop),
				Regular(Instruction::End),
				RandomI64Repeated(1),
				Regular(Instruction::Drop),
				Regular(Instruction::End),
			])),
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	// w_call = w_bench - 2 * w_param
	instr_call {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			// We need to make use of the stack here in order to trigger stack height
			// instrumentation.
			aux_body: Some(body::plain(vec![
				Instruction::I64Const(42),
				Instruction::Drop,
				Instruction::End,
			])),
			call_body: Some(body::repeated(r * INSTR_BENCHMARK_BATCH_SIZE, &[
				Instruction::Call(2), // call aux
			])),
			inject_stack_metering: true,
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	// w_call_indrect = w_bench - 3 * w_param
	instr_call_indirect {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let num_elements = T::Schedule::get().limits.table_size;
		use self::code::TableSegment;
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			// We need to make use of the stack here in order to trigger stack height
			// instrumentation.
			aux_body: Some(body::plain(vec![
				Instruction::I64Const(42),
				Instruction::Drop,
				Instruction::End,
			])),
			call_body: Some(body::repeated_dyn(r * INSTR_BENCHMARK_BATCH_SIZE, vec![
				RandomI32(0, num_elements as i32),
				Regular(Instruction::CallIndirect(0, 0)), // we only have one sig: 0
			])),
			inject_stack_metering: true,
			table: Some(TableSegment {
				num_elements,
				function_index: 2, // aux
			}),
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	// w_instr_call_indirect_per_param = w_bench - 1 * w_param
	// Calling a function indirectly causes it to go through a thunk function whose runtime
	// linearly depend on the amount of parameters to this function.
	// Please note that this is not necessary with a direct call.
	instr_call_indirect_per_param {
		let p in 0 .. T::Schedule::get().limits.parameters;
		let num_elements = T::Schedule::get().limits.table_size;
		use self::code::TableSegment;
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			// We need to make use of the stack here in order to trigger stack height
			// instrumentation.
			aux_body: Some(body::plain(vec![
				Instruction::I64Const(42),
				Instruction::Drop,
				Instruction::End,
			])),
			aux_arg_num: p,
			call_body: Some(body::repeated_dyn(INSTR_BENCHMARK_BATCH_SIZE, vec![
				RandomI64Repeated(p as usize),
				RandomI32(0, num_elements as i32),
				Regular(Instruction::CallIndirect(p.min(1), 0)), // aux signature: 1 or 0
			])),
			inject_stack_metering: true,
			table: Some(TableSegment {
				num_elements,
				function_index: 2, // aux
			}),
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	// w_local_get = w_bench - 1 * w_param
	instr_local_get {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let max_locals = T::Schedule::get().limits.stack_height.unwrap_or(512);
		let mut call_body = body::repeated_dyn(r * INSTR_BENCHMARK_BATCH_SIZE, vec![
			RandomGetLocal(0, max_locals),
			Regular(Instruction::Drop),
		]);
		body::inject_locals(&mut call_body, max_locals);
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			call_body: Some(call_body),
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	// w_local_set = w_bench - 1 * w_param
	instr_local_set {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let max_locals = T::Schedule::get().limits.stack_height.unwrap_or(512);
		let mut call_body = body::repeated_dyn(r * INSTR_BENCHMARK_BATCH_SIZE, vec![
			RandomI64Repeated(1),
			RandomSetLocal(0, max_locals),
		]);
		body::inject_locals(&mut call_body, max_locals);
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			call_body: Some(call_body),
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	// w_local_tee = w_bench - 2 * w_param
	instr_local_tee {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let max_locals = T::Schedule::get().limits.stack_height.unwrap_or(512);
		let mut call_body = body::repeated_dyn(r * INSTR_BENCHMARK_BATCH_SIZE, vec![
			RandomI64Repeated(1),
			RandomTeeLocal(0, max_locals),
			Regular(Instruction::Drop),
		]);
		body::inject_locals(&mut call_body, max_locals);
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			call_body: Some(call_body),
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	// w_global_get = w_bench - 1 * w_param
	instr_global_get {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let max_globals = T::Schedule::get().limits.globals;
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			call_body: Some(body::repeated_dyn(r * INSTR_BENCHMARK_BATCH_SIZE, vec![
				RandomGetGlobal(0, max_globals),
				Regular(Instruction::Drop),
			])),
			num_globals: max_globals,
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	// w_global_set = w_bench - 1 * w_param
	instr_global_set {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let max_globals = T::Schedule::get().limits.globals;
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			call_body: Some(body::repeated_dyn(r * INSTR_BENCHMARK_BATCH_SIZE, vec![
				RandomI64Repeated(1),
				RandomSetGlobal(0, max_globals),
			])),
			num_globals: max_globals,
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	// w_memory_get = w_bench - 1 * w_param
	instr_memory_current {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			call_body: Some(body::repeated(r * INSTR_BENCHMARK_BATCH_SIZE, &[
				Instruction::CurrentMemory(0),
				Instruction::Drop
			])),
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	// w_memory_grow = w_bench - 2 * w_param
	// We can only allow allocate as much memory as it is allowed in a a contract.
	// Therefore the repeat count is limited by the maximum memory any contract can have.
	// Using a contract with more memory will skew the benchmark because the runtime of grow
	// depends on how much memory is already allocated.
	instr_memory_grow {
		let r in 0 .. 1;
		let max_pages = ImportedMemory::max::<T>().max_pages;
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory {
				min_pages: 0,
				max_pages,
			}),
			call_body: Some(body::repeated(r * max_pages, &[
				Instruction::I32Const(1),
				Instruction::GrowMemory(0),
				Instruction::Drop,
			])),
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	// Unary numeric instructions.
	// All use w = w_bench - 2 * w_param.

	instr_i64clz {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::unary_instr(
			Instruction::I64Clz,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64ctz {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::unary_instr(
			Instruction::I64Ctz,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64popcnt {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::unary_instr(
			Instruction::I64Popcnt,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64eqz {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::unary_instr(
			Instruction::I64Eqz,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64extendsi32 {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			call_body: Some(body::repeated_dyn(r * INSTR_BENCHMARK_BATCH_SIZE, vec![
				RandomI32Repeated(1),
				Regular(Instruction::I64ExtendSI32),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	instr_i64extendui32 {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			call_body: Some(body::repeated_dyn(r * INSTR_BENCHMARK_BATCH_SIZE, vec![
				RandomI32Repeated(1),
				Regular(Instruction::I64ExtendUI32),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	instr_i32wrapi64 {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::unary_instr(
			Instruction::I32WrapI64,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	// Binary numeric instructions.
	// All use w = w_bench - 3 * w_param.

	instr_i64eq {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64Eq,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64ne {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64Ne,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64lts {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64LtS,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64ltu {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64LtU,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64gts {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64GtS,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64gtu {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64GtU,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64les {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64LeS,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64leu {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64LeU,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64ges {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64GeS,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64geu {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64GeU,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64add {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64Add,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64sub {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64Sub,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64mul {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64Mul,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64divs {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64DivS,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64divu {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64DivU,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64rems {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64RemS,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64remu {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64RemU,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64and {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64And,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64or {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64Or,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64xor {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64Xor,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64shl {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64Shl,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64shrs {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64ShrS,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64shru {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64ShrU,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64rotl {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64Rotl,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	instr_i64rotr {
		let r in 0 .. INSTR_BENCHMARK_BATCHES;
		let mut sbox = Sandbox::from(&WasmModule::<T>::binary_instr(
			Instruction::I64Rotr,
			r * INSTR_BENCHMARK_BATCH_SIZE,
		));
	}: {
		sbox.invoke();
	}

	// This is no benchmark. It merely exist to have an easy way to pretty print the curently
	// configured `Schedule` during benchmark development.
	// It can be outputed using the following command:
	// cargo run --manifest-path=bin/node/cli/Cargo.toml --release \
	//     --features runtime-benchmarks -- benchmark --extra --dev --execution=native \
	//     -p pallet_contracts -e print_schedule --no-median-slopes --no-min-squares
	#[extra]
	print_schedule {
		#[cfg(feature = "std")]
		{
			let weight_per_key = T::WeightInfo::on_initialize_per_trie_key(1) -
				T::WeightInfo::on_initialize_per_trie_key(0);
			let weight_per_queue_item = T::WeightInfo::on_initialize_per_queue_item(1) -
				T::WeightInfo::on_initialize_per_queue_item(0);
			let weight_limit = T::DeletionWeightLimit::get();
			let queue_depth: u64 = T::DeletionQueueDepth::get().into();
			println!("{:#?}", Schedule::<T>::default());
			println!("###############################################");
			println!("Lazy deletion throughput per block (empty queue, full queue): {}, {}",
				weight_limit / weight_per_key,
				(weight_limit - weight_per_queue_item * queue_depth) / weight_per_key,
			);
		}
		#[cfg(not(feature = "std"))]
		Err("Run this bench with a native runtime in order to see the schedule.")?;
	}: {}

	// Execute one erc20 transfer using the ink! erc20 example contract.
	//
	// `g` is used to enable gas instrumentation to compare the performance impact of
	// that instrumentation at runtime.
	#[extra]
	ink_erc20_transfer {
		let g in 0 .. 1;
		let gas_metering = if g == 0 { false } else { true };
		let code = load_benchmark!("ink_erc20");
		let data = {
			let new: ([u8; 4], BalanceOf<T>) = ([0x9b, 0xae, 0x9d, 0x5e], 1000u32.into());
			new.encode()
		};
		let instance = Contract::<T>::new(
			WasmModule::instrumented(code, gas_metering, true), data,
		)?;
		let data = {
			let transfer: ([u8; 4], AccountIdOf<T>, BalanceOf<T>) = (
				[0x84, 0xa1, 0x5d, 0xa1],
				account::<T::AccountId>("receiver", 0, 0),
				1u32.into(),
			);
			transfer.encode()
		};
	}: {
		<Contracts<T>>::bare_call(
			instance.caller,
			instance.account_id,
			0u32.into(),
			Weight::MAX,
			None,
			data,
			false,
		)
		.result?;
	}

	// Execute one erc20 transfer using the open zeppelin erc20 contract compiled with solang.
	//
	// `g` is used to enable gas instrumentation to compare the performance impact of
	// that instrumentation at runtime.
	#[extra]
	solang_erc20_transfer {
		let g in 0 .. 1;
		let gas_metering = if g == 0 { false } else { true };
		let code = include_bytes!("../../benchmarks/solang_erc20.wasm");
		let caller = account::<T::AccountId>("instantiator", 0, 0);
		let mut balance = [0u8; 32];
		balance[0] = 100;
		let data = {
			let new: ([u8; 4], &str, &str, [u8; 32], AccountIdOf<T>) = (
				[0xa6, 0xf1, 0xf5, 0xe1],
				"KSM",
				"K",
				balance,
				caller.clone(),
			);
			new.encode()
		};
		let instance = Contract::<T>::with_caller(
			caller, WasmModule::instrumented(code, gas_metering, true), data,
		)?;
		balance[0] = 1;
		let data = {
			let transfer: ([u8; 4], AccountIdOf<T>, [u8; 32]) = (
				[0x6a, 0x46, 0x73, 0x94],
				account::<T::AccountId>("receiver", 0, 0),
				balance,
			);
			transfer.encode()
		};
	}: {
		<Contracts<T>>::bare_call(
			instance.caller,
			instance.account_id,
			0u32.into(),
			Weight::MAX,
			None,
			data,
			false,
		)
		.result?;
	}

	impl_benchmark_test_suite!(
		Contracts,
		crate::tests::ExtBuilder::default().build(),
		crate::tests::Test,
	)
}
