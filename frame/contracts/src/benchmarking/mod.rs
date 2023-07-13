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
	exec::{AccountIdOf, Key},
	migration::{v09, v10, v11, v12, MigrationStep},
	wasm::CallFlags,
	Pallet as Contracts, *,
};
use codec::{Encode, MaxEncodedLen};
use frame_benchmarking::v1::{account, benchmarks, whitelisted_caller};
use frame_support::{pallet_prelude::StorageVersion, weights::Weight};
use frame_system::RawOrigin;
use sp_runtime::traits::{Bounded, Hash};
use sp_std::prelude::*;
use wasm_instrument::parity_wasm::elements::{BlockType, Instruction, ValueType};

/// How many runs we do per API benchmark.
///
/// This is picked more or less arbitrary. We experimented with different numbers until
/// the results appeared to be stable. Reducing the number would speed up the benchmarks
/// but might make the results less precise.
const API_BENCHMARK_RUNS: u32 = 1600;

/// How many runs we do per instruction benchmark.
///
/// Same rationale as for [`API_BENCHMARK_RUNS`]. The number is bigger because instruction
/// benchmarks are faster.
const INSTR_BENCHMARK_RUNS: u32 = 5000;

/// An instantiated and deployed contract.
struct Contract<T: Config> {
	caller: T::AccountId,
	account_id: T::AccountId,
	addr: AccountIdLookupOf<T>,
	value: BalanceOf<T>,
}

impl<T: Config> Contract<T>
where
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
		let value = Pallet::<T>::min_balance();
		T::Currency::make_free_balance_be(&caller, caller_funding::<T>());
		let salt = vec![0xff];
		let addr = Contracts::<T>::contract_address(&caller, &module.hash, &data, &salt);

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
	fn store(&self, items: &Vec<([u8; 32], Vec<u8>)>) -> Result<(), &'static str> {
		let info = self.info()?;
		for item in items {
			info.write(&Key::Fix(item.0), Some(item.1.clone()), None, false)
				.map_err(|_| "Failed to write storage to restoration dest")?;
		}
		<ContractInfoOf<T>>::insert(&self.account_id, info);
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
		<PristineCode<T>>::contains_key(hash) && <CodeInfoOf<T>>::contains_key(&hash)
	}

	/// Returns `true` iff no storage entry related to code storage exist.
	fn code_removed(hash: &CodeHash<T>) -> bool {
		!<PristineCode<T>>::contains_key(hash) && !<CodeInfoOf<T>>::contains_key(&hash)
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
		<BalanceOf<T> as codec::HasCompact>::Type: Clone + Eq + PartialEq + sp_std::fmt::Debug + scale_info::TypeInfo + codec::Encode,
	}

	// The base weight consumed on processing contracts deletion queue.
	#[pov_mode = Measured]
	on_process_deletion_queue_batch {}: {
		ContractInfo::<T>::process_deletion_queue_batch(Weight::MAX)
	}

	#[skip_meta]
	#[pov_mode = Measured]
	on_initialize_per_trie_key {
		let k in 0..1024;
		let instance = Contract::<T>::with_storage(WasmModule::dummy(), k, T::Schedule::get().limits.payload_len)?;
		instance.info()?.queue_trie_for_deletion();
	}: {
		ContractInfo::<T>::process_deletion_queue_batch(Weight::MAX)
	}

	// This benchmarks the v9 migration step (update codeStorage).
	#[pov_mode = Measured]
	v9_migration_step {
		let c in 0 .. T::MaxCodeLen::get();
		v09::store_old_dummy_code::<T>(c as usize);
		let mut m = v09::Migration::<T>::default();
	}: {
		m.step();
	}

	// This benchmarks the v10 migration step (use dedicated deposit_account).
	#[pov_mode = Measured]
	v10_migration_step {
		let contract = <Contract<T>>::with_caller(
			whitelisted_caller(), WasmModule::dummy(), vec![],
		)?;

		v10::store_old_contract_info::<T>(contract.account_id.clone(), contract.info()?);
		let mut m = v10::Migration::<T>::default();
	}: {
		m.step();
	}

	// This benchmarks the v11 migration step (Don't rely on reserved balances keeping an account alive).
	#[pov_mode = Measured]
	v11_migration_step {
		let k in 0 .. 1024;
		v11::fill_old_queue::<T>(k as usize);
		let mut m = v11::Migration::<T>::default();
	}: {
		m.step();
	}

	// This benchmarks the v12 migration step (Move `OwnerInfo` to `CodeInfo`,
	// add `determinism` field to the latter, clear `CodeStorage`
	// and repay deposits).
	#[pov_mode = Measured]
	v12_migration_step {
		let c in 0 .. T::MaxCodeLen::get();
		v12::store_old_dummy_code::<T>(c as usize, account::<T::AccountId>("account", 0, 0));
		let mut m = v12::Migration::<T>::default();
	}: {
		m.step();
	}

	// This benchmarks the weight of executing Migration::migrate to execute a noop migration.
	#[pov_mode = Measured]
	migration_noop {
		assert_eq!(StorageVersion::get::<Pallet<T>>(), 2);
	}:  {
		Migration::<T>::migrate(Weight::MAX)
	} verify {
		assert_eq!(StorageVersion::get::<Pallet<T>>(), 2);
	}

	// This benchmarks the weight of dispatching migrate to execute 1 `NoopMigraton`
	#[pov_mode = Measured]
	migrate {
		StorageVersion::new(0).put::<Pallet<T>>();
		<Migration::<T, false> as frame_support::traits::OnRuntimeUpgrade>::on_runtime_upgrade();
		let caller: T::AccountId = whitelisted_caller();
		let origin = RawOrigin::Signed(caller.clone());
	}: _(origin, Weight::MAX)
	verify {
		assert_eq!(StorageVersion::get::<Pallet<T>>(), 1);
	}

	// This benchmarks the weight of running on_runtime_upgrade when there are no migration in progress.
	#[pov_mode = Measured]
	on_runtime_upgrade_noop {
		assert_eq!(StorageVersion::get::<Pallet<T>>(), 2);
	}:  {
		<Migration::<T, false> as frame_support::traits::OnRuntimeUpgrade>::on_runtime_upgrade()
	} verify {
		assert!(MigrationInProgress::<T>::get().is_none());
	}

	// This benchmarks the weight of running on_runtime_upgrade when there is a migration in progress.
	#[pov_mode = Measured]
	on_runtime_upgrade_in_progress {
		StorageVersion::new(0).put::<Pallet<T>>();
		let v = vec![42u8].try_into().ok();
		MigrationInProgress::<T>::set(v.clone());
	}:  {
		<Migration::<T, false> as frame_support::traits::OnRuntimeUpgrade>::on_runtime_upgrade()
	} verify {
		assert!(MigrationInProgress::<T>::get().is_some());
		assert_eq!(MigrationInProgress::<T>::get(), v);
	}

	// This benchmarks the weight of running on_runtime_upgrade when there is a migration to process.
	#[pov_mode = Measured]
	on_runtime_upgrade {
		StorageVersion::new(0).put::<Pallet<T>>();
	}:  {
		<Migration::<T, false> as frame_support::traits::OnRuntimeUpgrade>::on_runtime_upgrade()
	} verify {
		assert!(MigrationInProgress::<T>::get().is_some());
	}

	// This benchmarks the overhead of loading a code of size `c` byte from storage and into
	// the sandbox. This does **not** include the actual execution for which the gas meter
	// is responsible. This is achieved by generating all code to the `deploy` function
	// which is in the wasm module but not executed on `call`.
	// The results are supposed to be used as `call_with_code_per_byte(c) - call_with_code_per_byte(0)`.
	#[pov_mode = Measured]
	call_with_code_per_byte {
		let c in 0 .. T::MaxCodeLen::get();
		let instance = Contract::<T>::with_caller(
			whitelisted_caller(), WasmModule::sized(c, Location::Deploy), vec![],
		)?;
		let value = Pallet::<T>::min_balance();
		let origin = RawOrigin::Signed(instance.caller.clone());
		let callee = instance.addr;
	}: call(origin, callee, value, Weight::MAX, None, vec![])

	// This constructs a contract that is maximal expensive to instrument.
	// It creates a maximum number of metering blocks per byte.
	// The size of the salt influences the runtime because is is hashed in order to
	// determine the contract address. All code is generated to the `call` function so that
	// we don't benchmark the actual execution of this code but merely what it takes to load
	// a code of that size into the sandbox.
	//
	// `c`: Size of the code in bytes.
	// `i`: Size of the input in bytes.
	// `s`: Size of the salt in bytes.
	#[pov_mode = Measured]
	instantiate_with_code {
		let c in 0 .. T::MaxCodeLen::get();
		let i in 0 .. code::max_pages::<T>() * 64 * 1024;
		let s in 0 .. code::max_pages::<T>() * 64 * 1024;
		let input = vec![42u8; i as usize];
		let salt = vec![42u8; s as usize];
		let value = Pallet::<T>::min_balance();
		let caller = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, caller_funding::<T>());
		let WasmModule { code, hash, .. } = WasmModule::<T>::sized(c, Location::Call);
		let origin = RawOrigin::Signed(caller.clone());
		let addr = Contracts::<T>::contract_address(&caller, &hash, &input, &salt);
	}: _(origin, value, Weight::MAX, None, code, input, salt)
	verify {
		let deposit_account = Contract::<T>::address_info(&addr)?.deposit_account().clone();
		let deposit = T::Currency::free_balance(&deposit_account);
		// uploading the code reserves some balance in the callers account
		let code_deposit = T::Currency::reserved_balance(&caller);
		assert_eq!(
			T::Currency::free_balance(&caller),
			caller_funding::<T>() - value - deposit - code_deposit - Pallet::<T>::min_balance(),
		);
		// contract has the full value
		assert_eq!(T::Currency::free_balance(&addr), value + Pallet::<T>::min_balance());
	}

	// Instantiate uses a dummy contract constructor to measure the overhead of the instantiate.
	// `i`: Size of the input in bytes.
	// `s`: Size of the salt in bytes.
	#[pov_mode = Measured]
	instantiate {
		let i in 0 .. code::max_pages::<T>() * 64 * 1024;
		let s in 0 .. code::max_pages::<T>() * 64 * 1024;
		let input = vec![42u8; i as usize];
		let salt = vec![42u8; s as usize];
		let value = Pallet::<T>::min_balance();
		let caller = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, caller_funding::<T>());
		let WasmModule { code, hash, .. } = WasmModule::<T>::dummy();
		let origin = RawOrigin::Signed(caller.clone());
		let addr = Contracts::<T>::contract_address(&caller, &hash, &input, &salt);
		Contracts::<T>::store_code_raw(code, caller.clone())?;
	}: _(origin, value, Weight::MAX, None, hash, input, salt)
	verify {
		let deposit_account = Contract::<T>::address_info(&addr)?.deposit_account().clone();
		let deposit = T::Currency::free_balance(&deposit_account);
		// value was removed from the caller
		assert_eq!(
			T::Currency::free_balance(&caller),
			caller_funding::<T>() - value - deposit - Pallet::<T>::min_balance(),
		);
		// contract has the full value
		assert_eq!(T::Currency::free_balance(&addr), value + Pallet::<T>::min_balance());
	}

	// We just call a dummy contract to measure the overhead of the call extrinsic.
	// The size of the data has no influence on the costs of this extrinsic as long as the contract
	// won't call `seal_input` in its constructor to copy the data to contract memory.
	// The dummy contract used here does not do this. The costs for the data copy is billed as
	// part of `seal_input`. The costs for invoking a contract of a specific size are not part
	// of this benchmark because we cannot know the size of the contract when issuing a call
	// transaction. See `call_with_code_per_byte` for this.
	#[pov_mode = Measured]
	call {
		let data = vec![42u8; 1024];
		let instance = Contract::<T>::with_caller(
			whitelisted_caller(), WasmModule::dummy(), vec![],
		)?;
		let deposit_account = instance.info()?.deposit_account().clone();
		let value = Pallet::<T>::min_balance();
		let origin = RawOrigin::Signed(instance.caller.clone());
		let callee = instance.addr.clone();
		let before = T::Currency::free_balance(&instance.account_id);
		let before_deposit = T::Currency::free_balance(&deposit_account);
	}: _(origin, callee, value, Weight::MAX, None, data)
	verify {
		let deposit = T::Currency::free_balance(&deposit_account);
		// value and value transferred via call should be removed from the caller
		assert_eq!(
			T::Currency::free_balance(&instance.caller),
			caller_funding::<T>() - instance.value - value - deposit - Pallet::<T>::min_balance(),
		);
		// contract should have received the value
		assert_eq!(T::Currency::free_balance(&instance.account_id), before + value);
		// contract should still exist
		instance.info()?;
	}

	// This constructs a contract that is maximal expensive to instrument.
	// It creates a maximum number of metering blocks per byte.
	// `c`: Size of the code in bytes.
	#[pov_mode = Measured]
	upload_code {
		let c in 0 .. T::MaxCodeLen::get();
		let caller = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, caller_funding::<T>());
		let WasmModule { code, hash, .. } = WasmModule::<T>::sized(c, Location::Call);
		let origin = RawOrigin::Signed(caller.clone());
	}: _(origin, code, None, Determinism::Enforced)
	verify {
		// uploading the code reserves some balance in the callers account
		assert!(T::Currency::reserved_balance(&caller) > 0u32.into());
		assert!(<Contract<T>>::code_exists(&hash));
	}

	// Removing code does not depend on the size of the contract because all the information
	// needed to verify the removal claim (refcount, owner) is stored in a separate storage
	// item (`CodeInfoOf`).
	#[pov_mode = Measured]
	remove_code {
		let caller = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, caller_funding::<T>());
		let WasmModule { code, hash, .. } = WasmModule::<T>::dummy();
		let origin = RawOrigin::Signed(caller.clone());
		let uploaded = <Contracts<T>>::bare_upload_code(caller.clone(), code, None, Determinism::Enforced)?;
		assert_eq!(uploaded.code_hash, hash);
		assert_eq!(uploaded.deposit, T::Currency::reserved_balance(&caller));
		assert!(<Contract<T>>::code_exists(&hash));
	}: _(origin, hash)
	verify {
		// removing the code should have unreserved the deposit
		assert_eq!(T::Currency::reserved_balance(&caller), 0u32.into());
		assert!(<Contract<T>>::code_removed(&hash));
	}

	#[pov_mode = Measured]
	set_code {
		let instance = <Contract<T>>::with_caller(
			whitelisted_caller(), WasmModule::dummy(), vec![],
		)?;
		// we just add some bytes so that the code hash is different
		let WasmModule { code, hash, .. } = <WasmModule<T>>::dummy_with_bytes(128);
		<Contracts<T>>::store_code_raw(code, instance.caller.clone())?;
		let callee = instance.addr.clone();
		assert_ne!(instance.info()?.code_hash, hash);
	}: _(RawOrigin::Root, callee, hash)
	verify {
		assert_eq!(instance.info()?.code_hash, hash);
	}

	#[pov_mode = Measured]
	seal_caller {
		let r in 0 .. API_BENCHMARK_RUNS;
		let instance = Contract::<T>::new(WasmModule::getter(
			"seal0", "seal_caller", r
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[pov_mode = Measured]
	seal_is_contract {
		let r in 0 .. API_BENCHMARK_RUNS;
		let accounts = (0 .. r)
			.map(|n| account::<T::AccountId>("account", n, 0))
			.collect::<Vec<_>>();
		let account_len = accounts.get(0).map(|i| i.encode().len()).unwrap_or(0);
		let accounts_bytes = accounts.iter().flat_map(|a| a.encode()).collect::<Vec<_>>();
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
			call_body: Some(body::repeated_dyn(r, vec![
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

	#[pov_mode = Measured]
	seal_code_hash {
		let r in 0 .. API_BENCHMARK_RUNS;
		let accounts = (0 .. r)
			.map(|n| account::<T::AccountId>("account", n, 0))
			.collect::<Vec<_>>();
		let account_len = accounts.get(0).map(|i| i.encode().len()).unwrap_or(0);
		let accounts_bytes = accounts.iter().flat_map(|a| a.encode()).collect::<Vec<_>>();
		let accounts_len = accounts_bytes.len();
		let pages = code::max_pages::<T>();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_code_hash",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: 32u32.to_le_bytes().to_vec(), // output length
				},
				DataSegment {
					offset: 36,
					value: accounts_bytes,
				},
			],
			call_body: Some(body::repeated_dyn(r, vec![
				Counter(36, account_len as u32), // address_ptr
				Regular(Instruction::I32Const(4)), // ptr to output data
				Regular(Instruction::I32Const(0)), // ptr to output length
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

	#[pov_mode = Measured]
	seal_own_code_hash {
		let r in 0 .. API_BENCHMARK_RUNS;
		let instance = Contract::<T>::new(WasmModule::getter(
			"seal0", "seal_own_code_hash", r
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[pov_mode = Measured]
	seal_caller_is_origin {
		let r in 0 .. API_BENCHMARK_RUNS;
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_caller_is_origin",
				params: vec![],
				return_type: Some(ValueType::I32),
			}],
			call_body: Some(body::repeated(r, &[
				Instruction::Call(0),
				Instruction::Drop,
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[pov_mode = Measured]
	seal_caller_is_root {
		let r in 0 .. API_BENCHMARK_RUNS;

		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "caller_is_root",
				params: vec![],
				return_type: Some(ValueType::I32),
			}],
			call_body: Some(body::repeated(r, &[
				Instruction::Call(0),
				Instruction::Drop,
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Root;
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[pov_mode = Measured]
	seal_address {
		let r in 0 .. API_BENCHMARK_RUNS;
		let instance = Contract::<T>::new(WasmModule::getter(
			"seal0", "seal_address", r
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[pov_mode = Measured]
	seal_gas_left {
		let r in 0 .. API_BENCHMARK_RUNS;
		let instance = Contract::<T>::new(WasmModule::getter(
			"seal1", "gas_left", r
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[pov_mode = Measured]
	seal_balance {
		let r in 0 .. API_BENCHMARK_RUNS;
		let instance = Contract::<T>::new(WasmModule::getter(
			"seal0", "seal_balance", r
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[pov_mode = Measured]
	seal_value_transferred {
		let r in 0 .. API_BENCHMARK_RUNS;
		let instance = Contract::<T>::new(WasmModule::getter(
			"seal0", "seal_value_transferred", r
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[pov_mode = Measured]
	seal_minimum_balance {
		let r in 0 .. API_BENCHMARK_RUNS;
		let instance = Contract::<T>::new(WasmModule::getter(
			"seal0", "seal_minimum_balance", r
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[pov_mode = Measured]
	seal_block_number {
		let r in 0 .. API_BENCHMARK_RUNS;
		let instance = Contract::<T>::new(WasmModule::getter(
			"seal0", "seal_block_number", r
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[pov_mode = Measured]
	seal_now {
		let r in 0 .. API_BENCHMARK_RUNS;
		let instance = Contract::<T>::new(WasmModule::getter(
			"seal0", "seal_now", r
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[pov_mode = Measured]
	seal_weight_to_fee {
		let r in 0 .. API_BENCHMARK_RUNS;
		let pages = code::max_pages::<T>();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal1",
				name: "weight_to_fee",
				params: vec![ValueType::I64, ValueType::I64, ValueType::I32, ValueType::I32],
				return_type: None,
			}],
			data_segments: vec![DataSegment {
				offset: 0,
				value: (pages * 64 * 1024 - 4).to_le_bytes().to_vec(),
			}],
			call_body: Some(body::repeated(r, &[
				Instruction::I64Const(500_000),
				Instruction::I64Const(300_000),
				Instruction::I32Const(4),
				Instruction::I32Const(0),
				Instruction::Call(0),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[pov_mode = Measured]
	seal_input {
		let r in 0 .. API_BENCHMARK_RUNS;
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
			call_body: Some(body::repeated(r, &[
				Instruction::I32Const(4), // ptr where to store output
				Instruction::I32Const(0), // ptr to length
				Instruction::Call(0),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[pov_mode = Measured]
	seal_input_per_byte {
		let n in 0 .. code::max_pages::<T>() * 64 * 1024;
		let buffer_size = code::max_pages::<T>() * 64 * 1024 - 4;
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
			call_body: Some(body::plain(vec![
				Instruction::I32Const(4), // ptr where to store output
				Instruction::I32Const(0), // ptr to length
				Instruction::Call(0),
				Instruction::End,
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let data = vec![42u8; n.min(buffer_size) as usize];
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, data)

	// We cannot call `seal_return` multiple times. Therefore our weight determination is not
	// as precise as with other APIs. Because this function can only be called once per
	// contract it cannot be used as an attack vector.
	#[pov_mode = Measured]
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

	#[pov_mode = Measured]
	seal_return_per_byte {
		let n in 0 .. code::max_pages::<T>() * 64 * 1024;
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
				Instruction::I32Const(n as i32), // data_len
				Instruction::Call(0),
				Instruction::End,
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// The same argument as for `seal_return` is true here.
	#[pov_mode = Measured]
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
		let deposit_account = instance.info()?.deposit_account().clone();
		assert_eq!(<T::Currency as Currency<_>>::total_balance(&beneficiary), 0u32.into());
		assert_eq!(T::Currency::free_balance(&instance.account_id), Pallet::<T>::min_balance() * 2u32.into());
		assert_ne!(T::Currency::free_balance(&deposit_account), 0u32.into());
	}: call(origin, instance.addr.clone(), 0u32.into(), Weight::MAX, None, vec![])
	verify {
		if r > 0 {
			assert_eq!(<T::Currency as Currency<_>>::total_balance(&instance.account_id), 0u32.into());
			assert_eq!(<T::Currency as Currency<_>>::total_balance(&deposit_account), 0u32.into());
			assert_eq!(<T::Currency as Currency<_>>::total_balance(&beneficiary), Pallet::<T>::min_balance() * 2u32.into());
		}
	}

	// We benchmark only for the maximum subject length. We assume that this is some lowish
	// number (< 1 KB). Therefore we are not overcharging too much in case a smaller subject is
	// used.
	#[pov_mode = Measured]
	seal_random {
		let r in 0 .. API_BENCHMARK_RUNS;
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
			call_body: Some(body::repeated(r, &[
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
	#[pov_mode = Measured]
	seal_deposit_event {
		let r in 0 .. API_BENCHMARK_RUNS;
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_deposit_event",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: None,
			}],
			call_body: Some(body::repeated(r, &[
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
	// `n`: Size of event payload in bytes
	#[pov_mode = Measured]
	seal_deposit_event_per_topic_and_byte {
		let t in 0 .. T::Schedule::get().limits.event_topics;
		let n in 0 .. T::Schedule::get().limits.payload_len;
		let topics = (0..t).map(|i| T::Hashing::hash_of(&i)).collect::<Vec<_>>().encode();
		let topics_len = topics.len();
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
			call_body: Some(body::plain(vec![
				Instruction::I32Const(0), // topics_ptr
				Instruction::I32Const(topics_len as i32), // topics_len
				Instruction::I32Const(0), // data_ptr
				Instruction::I32Const(n as i32), // data_len
				Instruction::Call(0),
				Instruction::End,
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// Benchmark debug_message call with zero input data.
	// Whereas this function is used in RPC mode only, it still should be secured
	// against an excessive use.
	#[pov_mode = Measured]
	seal_debug_message {
		let r in 0 .. API_BENCHMARK_RUNS;
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory { min_pages: 1, max_pages: 1 }),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_debug_message",
				params: vec![ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			call_body: Some(body::repeated(r, &[
				Instruction::I32Const(0), // value_ptr
				Instruction::I32Const(0), // value_len
				Instruction::Call(0),
				Instruction::Drop,
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
	}: {
		<Contracts<T>>::bare_call(
			instance.caller,
			instance.account_id,
			0u32.into(),
			Weight::MAX,
			None,
			vec![],
			DebugInfo::UnsafeDebug,
			CollectEvents::Skip,
			Determinism::Enforced,
		)
		.result?;
	}

	seal_debug_message_per_byte {
		// Vary size of input in bytes up to maximum allowed contract memory
		// or maximum allowed debug buffer size, whichever is less.
		let i in 0 .. (T::Schedule::get().limits.memory_pages * 64 * 1024).min(T::MaxDebugBufferLen::get());
		// We benchmark versus messages containing printable ASCII codes.
		// About 1Kb goes to the contract code instructions,
		// whereas all the space left we use for the initialization of the debug messages data.
		let message = (0 .. T::MaxCodeLen::get() - 1024).zip((32..127).cycle()).map(|i| i.1).collect::<Vec<_>>();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory {
				min_pages: T::Schedule::get().limits.memory_pages,
				max_pages: T::Schedule::get().limits.memory_pages,
			}),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_debug_message",
				params: vec![ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			 }],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: message,
				},
			],
			call_body: Some(body::plain(vec![
				Instruction::I32Const(0), // value_ptr
				Instruction::I32Const(i as i32), // value_len
				Instruction::Call(0),
				Instruction::Drop,
				Instruction::End,
			])),
			..Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
	}: {
		<Contracts<T>>::bare_call(
			instance.caller,
			instance.account_id,
			0u32.into(),
			Weight::MAX,
			None,
			vec![],
			DebugInfo::UnsafeDebug,
			CollectEvents::Skip,
			Determinism::Enforced,
		)
		.result?;
	}

	// Only the overhead of calling the function itself with minimal arguments.
	// The contract is a bit more complex because it needs to use different keys in order
	// to generate unique storage accesses. However, it is still dominated by the storage
	// accesses. We store something at all the keys that we are about to write to
	// because re-writing at an existing key is always more expensive than writing
	// to an key with no data behind it.
	//
	// # Note
	//
	// We need to use a smaller `r` because the keys are big and writing them all into the wasm
	// might exceed the code size.
	#[skip_meta]
	#[pov_mode = Measured]
	seal_set_storage {
		let r in 0 .. API_BENCHMARK_RUNS/2;
		let max_key_len = T::MaxStorageKeyLen::get();
		let keys = (0 .. r)
				.map(|n| { let mut h = T::Hashing::hash_of(&n).as_ref().to_vec();
						h.resize(max_key_len.try_into().unwrap(), n.to_le_bytes()[0]); h })
		.collect::<Vec<_>>();
		let keys_bytes = keys.iter().flatten().cloned().collect::<Vec<_>>();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal2",
				name: "set_storage",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: keys_bytes,
				},
			],
			call_body: Some(body::repeated_dyn(r, vec![
				Counter(0, max_key_len as u32), // key_ptr
				Regular(Instruction::I32Const(max_key_len as i32)), // key_len
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
			info.write(
				&Key::<T>::try_from_var(key).map_err(|e| "Key has wrong length")?,
				Some(vec![]),
				None,
				false,
			)
			.map_err(|_| "Failed to write to storage during setup.")?;
		}
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[skip_meta]
	#[pov_mode = Measured]
	seal_set_storage_per_new_byte {
		let n in 0 .. T::Schedule::get().limits.payload_len;
		let max_key_len = T::MaxStorageKeyLen::get();
		let key = vec![0u8; max_key_len as usize];
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal2",
				name: "set_storage",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: key.clone(),
				},
			],
			call_body: Some(body::plain(vec![
				Instruction::I32Const(0), // key_ptr
				Instruction::I32Const(max_key_len as i32), // key_len
				Instruction::I32Const(0), // value_ptr
				Instruction::I32Const(n as i32), // value_len
				Instruction::Call(0),
				Instruction::Drop,
				Instruction::End,
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let info = instance.info()?;
		info.write(
			&Key::<T>::try_from_var(key).map_err(|e| "Key has wrong length")?,
			Some(vec![]),
			None,
			false,
		)
		.map_err(|_| "Failed to write to storage during setup.")?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[skip_meta]
	#[pov_mode = Measured]
	seal_set_storage_per_old_byte {
		let n in 0 .. T::Schedule::get().limits.payload_len;
		let max_key_len = T::MaxStorageKeyLen::get();
		let key = vec![0u8; max_key_len as usize];
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal2",
				name: "set_storage",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: key.clone(),
				},
			],
			call_body: Some(body::plain(vec![
				Instruction::I32Const(0), // key_ptr
				Instruction::I32Const(max_key_len as i32), // key_len
				Instruction::I32Const(0), // value_ptr
				Instruction::I32Const(0), // value_len is 0 as testing vs pre-existing value len
				Instruction::Call(0),
				Instruction::Drop,
				Instruction::End,
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let info = instance.info()?;
		info.write(
			&Key::<T>::try_from_var(key).map_err(|e| "Key has wrong length")?,
			Some(vec![42u8; n as usize]),
			None,
			false,
		)
		.map_err(|_| "Failed to write to storage during setup.")?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// Similar to seal_set_storage. We store all the keys that we are about to
	// delete beforehand in order to prevent any optimizations that could occur when
	// deleting a non existing key. We generate keys of a maximum length, and have to
	// the amount of runs in order to make resulting contract code size less than MaxCodeLen.
	#[skip_meta]
	#[pov_mode = Measured]
	seal_clear_storage {
		let r in 0 .. API_BENCHMARK_RUNS/2;
		let max_key_len = T::MaxStorageKeyLen::get();
		let keys = (0 .. r)
				.map(|n| { let mut h = T::Hashing::hash_of(&n).as_ref().to_vec();
						h.resize(max_key_len.try_into().unwrap(), n.to_le_bytes()[0]); h })
		.collect::<Vec<_>>();
		let key_bytes = keys.iter().flatten().cloned().collect::<Vec<_>>();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal1",
				name: "clear_storage",
				params: vec![ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: key_bytes,
				},
			],
			call_body: Some(body::repeated_dyn(r, vec![
				Counter(0, max_key_len as u32), // key_ptr
				Regular(Instruction::I32Const(max_key_len as i32)), // key_len
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let info = instance.info()?;
		for key in keys {
			info.write(
				&Key::<T>::try_from_var(key).map_err(|e| "Key has wrong length")?,
				Some(vec![]),
				None,
				false,
			)
			.map_err(|_| "Failed to write to storage during setup.")?;
		}
		<ContractInfoOf<T>>::insert(&instance.account_id, info);
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[skip_meta]
	#[pov_mode = Measured]
	seal_clear_storage_per_byte {
		let n in 0 .. T::Schedule::get().limits.payload_len;
		let max_key_len = T::MaxStorageKeyLen::get();
		let key = vec![0u8; max_key_len as usize];
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal1",
				name: "clear_storage",
				params: vec![ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: key.clone(),
				},
			],
			call_body: Some(body::plain(vec![
				Instruction::I32Const(0), // key_ptr
				Instruction::I32Const(max_key_len as i32), // key_len
				Instruction::Call(0),
				Instruction::Drop,
				Instruction::End,
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let info = instance.info()?;
		info.write(
			&Key::<T>::try_from_var(key).map_err(|e| "Key has wrong length")?,
			Some(vec![42u8; n as usize]),
			None,
			false,
		)
		.map_err(|_| "Failed to write to storage during setup.")?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// We make sure that all storage accesses are to unique keys.
	#[skip_meta]
	#[pov_mode = Measured]
	seal_get_storage {
		let r in 0 .. API_BENCHMARK_RUNS/2;
		let max_key_len = T::MaxStorageKeyLen::get();
		let keys = (0 .. r)
				.map(|n| { let mut h = T::Hashing::hash_of(&n).as_ref().to_vec();
						h.resize(max_key_len.try_into().unwrap(), n.to_le_bytes()[0]); h })
		.collect::<Vec<_>>();
		let key_bytes = keys.iter().flatten().cloned().collect::<Vec<_>>();
		let key_bytes_len = key_bytes.len();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal1",
				name: "get_storage",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32, ValueType::I32],
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
			call_body: Some(body::repeated_dyn(r, vec![
				Counter(0, max_key_len), // key_ptr
				Regular(Instruction::I32Const(max_key_len as i32)), // key_len
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
			info.write(
				&Key::<T>::try_from_var(key).map_err(|e| "Key has wrong length")?,
				Some(vec![]),
				None,
				false,
			)
			.map_err(|_| "Failed to write to storage during setup.")?;
		}
		<ContractInfoOf<T>>::insert(&instance.account_id, info);
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[skip_meta]
	#[pov_mode = Measured]
	seal_get_storage_per_byte {
		let n in 0 .. T::Schedule::get().limits.payload_len;
		let max_key_len = T::MaxStorageKeyLen::get();
		let key = vec![0u8; max_key_len as usize];
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal1",
				name: "get_storage",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: key.clone(),
				},
				DataSegment {
					offset: max_key_len,
					value: T::Schedule::get().limits.payload_len.to_le_bytes().into(),
				},
			],
			call_body: Some(body::plain(vec![
				Instruction::I32Const(0), // key_ptr
				Instruction::I32Const(max_key_len as i32), // key_len
				Instruction::I32Const((max_key_len + 4) as i32), // out_ptr
				Instruction::I32Const(max_key_len as i32), // out_len_ptr
				Instruction::Call(0),
				Instruction::Drop,
				Instruction::End,
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let info = instance.info()?;
		info.write(
			&Key::<T>::try_from_var(key).map_err(|e| "Key has wrong length")?,
			Some(vec![42u8; n as usize]),
			None,
			false,
		)
		.map_err(|_| "Failed to write to storage during setup.")?;
		<ContractInfoOf<T>>::insert(&instance.account_id, info);
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// We make sure that all storage accesses are to unique keys.
	#[skip_meta]
	#[pov_mode = Measured]
	seal_contains_storage {
		let r in 0 .. API_BENCHMARK_RUNS/2;
		let max_key_len = T::MaxStorageKeyLen::get();
		let keys = (0 .. r)
				.map(|n| { let mut h = T::Hashing::hash_of(&n).as_ref().to_vec();
						h.resize(max_key_len.try_into().unwrap(), n.to_le_bytes()[0]); h })
		.collect::<Vec<_>>();
		let key_bytes = keys.iter().flatten().cloned().collect::<Vec<_>>();
		let key_bytes_len = key_bytes.len();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal1",
				name: "contains_storage",
				params: vec![ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: key_bytes,
				},
			],
			call_body: Some(body::repeated_dyn(r, vec![
				Counter(0, max_key_len as u32), // key_ptr
				Regular(Instruction::I32Const(max_key_len as i32)), // key_len
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let info = instance.info()?;
		for key in keys {
			info.write(
				&Key::<T>::try_from_var(key).map_err(|e| "Key has wrong length")?,
				Some(vec![]),
				None,
				false,
			)
			.map_err(|_| "Failed to write to storage during setup.")?;
		}
		<ContractInfoOf<T>>::insert(&instance.account_id, info);
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[skip_meta]
	#[pov_mode = Measured]
	seal_contains_storage_per_byte {
		let n in 0 .. T::Schedule::get().limits.payload_len;
		let max_key_len = T::MaxStorageKeyLen::get();
		let key = vec![0u8; max_key_len as usize];
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal1",
				name: "contains_storage",
				params: vec![ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: key.clone(),
				},
			],
			call_body: Some(body::plain(vec![
				Instruction::I32Const(0), // key_ptr
				Instruction::I32Const(max_key_len as i32), // key_len
				Instruction::Call(0),
				Instruction::Drop,
				Instruction::End,
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let info = instance.info()?;
		info.write(
			&Key::<T>::try_from_var(key).map_err(|e| "Key has wrong length")?,
			Some(vec![42u8; n as usize]),
			None,
			false,
		)
		.map_err(|_| "Failed to write to storage during setup.")?;
		<ContractInfoOf<T>>::insert(&instance.account_id, info);
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[skip_meta]
	#[pov_mode = Measured]
	seal_take_storage {
		let r in 0 .. API_BENCHMARK_RUNS/2;
		let max_key_len = T::MaxStorageKeyLen::get();
		let keys = (0 .. r)
				.map(|n| { let mut h = T::Hashing::hash_of(&n).as_ref().to_vec();
						h.resize(max_key_len.try_into().unwrap(), n.to_le_bytes()[0]); h })
		.collect::<Vec<_>>();
		let key_bytes = keys.iter().flatten().cloned().collect::<Vec<_>>();
		let key_bytes_len = key_bytes.len();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "take_storage",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32, ValueType::I32],
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
			call_body: Some(body::repeated_dyn(r, vec![
				Counter(0, max_key_len as u32), // key_ptr
				Regular(Instruction::I32Const(max_key_len as i32)), // key_len
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
			info.write(
				&Key::<T>::try_from_var(key).map_err(|e| "Key has wrong length")?,
				Some(vec![]),
				None,
				false,
			)
			.map_err(|_| "Failed to write to storage during setup.")?;
		}
		<ContractInfoOf<T>>::insert(&instance.account_id, info);
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[skip_meta]
	#[pov_mode = Measured]
	seal_take_storage_per_byte {
		let n in 0 .. T::Schedule::get().limits.payload_len;
		let max_key_len = T::MaxStorageKeyLen::get();
		let key = vec![0u8; max_key_len as usize];
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "take_storage",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: key.clone(),
				},
				DataSegment {
					offset: max_key_len,
					value: T::Schedule::get().limits.payload_len.to_le_bytes().into(),
				},
			],
			call_body: Some(body::plain(vec![
				Instruction::I32Const(0), // key_ptr
				Instruction::I32Const(max_key_len as i32), // key_len
				Instruction::I32Const((max_key_len + 4) as i32), // out_ptr
				Instruction::I32Const(max_key_len as i32), // out_len_ptr
				Instruction::Call(0),
				Instruction::Drop,
				Instruction::End,
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let info = instance.info()?;
		info.write(
			&Key::<T>::try_from_var(key).map_err(|e| "Key has wrong length")?,
			Some(vec![42u8; n as usize]),
			None,
			false,
		)
		.map_err(|_| "Failed to write to storage during setup.")?;
		<ContractInfoOf<T>>::insert(&instance.account_id, info);
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// We transfer to unique accounts.
	#[pov_mode = Measured]
	seal_transfer {
		let r in 0 .. API_BENCHMARK_RUNS;
		let accounts = (0..r)
			.map(|i| account::<T::AccountId>("receiver", i, 0))
			.collect::<Vec<_>>();
		let account_len = accounts.get(0).map(|i| i.encode().len()).unwrap_or(0);
		let account_bytes = accounts.iter().flat_map(|x| x.encode()).collect();
		let value = Pallet::<T>::min_balance();
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
			call_body: Some(body::repeated_dyn(r, vec![
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
		instance.set_balance(value * (r + 1).into());
		let origin = RawOrigin::Signed(instance.caller.clone());
		for account in &accounts {
			assert_eq!(<T::Currency as Currency<_>>::total_balance(account), 0u32.into());
		}
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])
	verify {
		for account in &accounts {
			assert_eq!(<T::Currency as Currency<_>>::total_balance(account), value);
		}
	}

	// We call unique accounts.
	//
	// This is a slow call: We redeuce the number of runs.
	#[pov_mode = Measured]
	seal_call {
		let r in 0 .. API_BENCHMARK_RUNS / 2;
		let dummy_code = WasmModule::<T>::dummy_with_bytes(0);
		let callees = (0..r)
			.map(|i| Contract::with_index(i + 1, dummy_code.clone(), vec![]))
			.collect::<Result<Vec<_>, _>>()?;
		let callee_len = callees.get(0).map(|i| i.account_id.encode().len()).unwrap_or(0);
		let callee_bytes = callees.iter().flat_map(|x| x.account_id.encode()).collect();
		let value: BalanceOf<T> = 0u32.into();
		let value_bytes = value.encode();
		let value_len = BalanceOf::<T>::max_encoded_len() as u32;
		// Set an own limit every 2nd call
		let own_limit = (u32::MAX - 100).into();
		let deposits = (0..r)
			.map(|i| if i % 2 == 0 { 0u32.into() } else { own_limit } )
			.collect::<Vec<BalanceOf<T>>>();
		let deposits_bytes: Vec<u8> = deposits.iter().flat_map(|i| i.encode()).collect();
		let deposits_len = deposits_bytes.len() as u32;
		let deposit_len = value_len.clone();
		let callee_offset = value_len + deposits_len;
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal2",
				name: "call",
				params: vec![
					ValueType::I32,
					ValueType::I32,
					ValueType::I64,
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
					offset: value_len,
					value: deposits_bytes,
				},
				DataSegment {
					offset: callee_offset,
					value: callee_bytes,
				},
			],
			call_body: Some(body::repeated_dyn(r, vec![
				Regular(Instruction::I32Const(0)), // flags
				Counter(callee_offset, callee_len as u32), // callee_ptr
				Regular(Instruction::I64Const(0)), // ref_time weight
				Regular(Instruction::I64Const(0)), // proof_size weight
				Counter(value_len, deposit_len as u32), // deposit_limit_ptr
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
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, Some(BalanceOf::<T>::from(u32::MAX).into()), vec![])

	// This is a slow call: We redeuce the number of runs.
	#[pov_mode = Measured]
	seal_delegate_call {
		let r in 0 .. API_BENCHMARK_RUNS / 2;
		let hashes = (0..r)
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
				module: "seal0",
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
			call_body: Some(body::repeated_dyn(r, vec![
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
		let origin = RawOrigin::Signed(instance.caller);
	}: call(origin, callee, 0u32.into(), Weight::MAX, None, vec![])

	#[pov_mode = Measured]
	seal_call_per_transfer_clone_byte {
		let t in 0 .. 1;
		let c in 0 .. code::max_pages::<T>() * 64 * 1024;
		let callee = Contract::with_index(5, <WasmModule<T>>::dummy(), vec![])?;
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
					value: callee.account_id.encode(),
				},
			],
			call_body: Some(body::plain(vec![
				Instruction::I32Const(CallFlags::CLONE_INPUT.bits() as i32), // flags
				Instruction::I32Const(value_len as i32), // callee_ptr
				Instruction::I64Const(0), // gas
				Instruction::I32Const(0), // value_ptr
				Instruction::I32Const(0), // input_data_ptr
				Instruction::I32Const(0), // input_data_len
				Instruction::I32Const(SENTINEL as i32), // output_ptr
				Instruction::I32Const(0), // output_len_ptr
				Instruction::Call(0),
				Instruction::Drop,
				Instruction::End,
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
		let bytes = vec![42; c as usize];
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, bytes)

	// We assume that every instantiate sends at least the minimum balance.
	// This is a slow call: we reduce the number of runs.
	#[pov_mode = Measured]
	seal_instantiate {
		let r in 1 .. API_BENCHMARK_RUNS / 2;
		let hashes = (0..r)
			.map(|i| {
				let code = WasmModule::<T>::from(ModuleDefinition {
					memory: Some(ImportedMemory::max::<T>()),
					call_body: Some(body::plain(vec![
						// We need to add this in order to make contracts unique,
						// so that they can be deployed from the same sender.
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
		let hashes_len = &hashes_bytes.len();
		let value = Pallet::<T>::min_balance();
		assert!(value > 0u32.into());
		let value_bytes = value.encode();
		let value_len = BalanceOf::<T>::max_encoded_len();
		let addr_len = T::AccountId::max_encoded_len();
		// Offsets where to place static data in contract memory.
		let hashes_offset = value_len;
		let addr_len_offset = hashes_offset + hashes_len;
		let addr_offset = addr_len_offset + addr_len;
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal2",
				name: "instantiate",
				params: vec![
					ValueType::I32,
					ValueType::I64,
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
					offset: 0,
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
			call_body: Some(body::repeated_dyn(r, vec![
				Counter(hashes_offset as u32, hash_len as u32), // code_hash_ptr
				Regular(Instruction::I64Const(0)), // ref_time weight
				Regular(Instruction::I64Const(0)), // proof_size weight
				Regular(Instruction::I32Const(SENTINEL as i32)), // deposit limit ptr: use parent's limit
				Regular(Instruction::I32Const(0)), // value_ptr
				Regular(Instruction::I32Const(0)), // input_data_ptr
				Regular(Instruction::I32Const(0)), // input_data_len
				Regular(Instruction::I32Const(addr_offset as i32)), // address_ptr
				Regular(Instruction::I32Const(addr_len_offset as i32)), // address_len_ptr
				Regular(Instruction::I32Const(SENTINEL as i32)), // output_ptr
				Regular(Instruction::I32Const(0)), // output_len_ptr
				Regular(Instruction::I32Const(0)), // salt_ptr
				Regular(Instruction::I32Const(0)), // salt_len_ptr
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		instance.set_balance((value + Pallet::<T>::min_balance()) * (r + 1).into());
		let origin = RawOrigin::Signed(instance.caller.clone());
		let callee = instance.addr.clone();
		let addresses = hashes
			.iter()
			.map(|hash| Contracts::<T>::contract_address(
				&instance.account_id, hash, &[], &[],
			))
			.collect::<Vec<_>>();

		for addr in &addresses {
			if ContractInfoOf::<T>::get(&addr).is_some() {
				return Err("Expected that contract does not exist at this point.".into());
			}
		}
	}: call(origin, callee, 0u32.into(), Weight::MAX, None, vec![])
	verify {
		for addr in &addresses {
			ContractInfoOf::<T>::get(&addr)
				.ok_or("Contract should have been instantiated")?;
		}
	}

	#[pov_mode = Measured]
	seal_instantiate_per_transfer_input_salt_byte {
		let t in 0 .. 1;
		let i in 0 .. (code::max_pages::<T>() - 1) * 64 * 1024;
		let s in 0 .. (code::max_pages::<T>() - 1) * 64 * 1024;
		let callee_code = WasmModule::<T>::dummy();
		let hash = callee_code.hash;
		let hash_bytes = callee_code.hash.encode();
		let hash_len = hash_bytes.len();
		Contracts::<T>::store_code_raw(callee_code.code, whitelisted_caller())?;
		let value: BalanceOf<T> =  t.into();
		let value_bytes = value.encode();

		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal1",
				name: "seal_instantiate",
				params: vec![
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
				],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: hash_bytes,
				},
				DataSegment {
					offset: hash_len as u32,
					value: value_bytes,
				},
			],
			call_body: Some(body::plain(vec![
				Instruction::I32Const(0 as i32), // code_hash_ptr
				Instruction::I64Const(0), // gas
				Instruction::I32Const(hash_len as i32), // value_ptr
				Instruction::I32Const(0 as i32), // input_data_ptr
				Instruction::I32Const(i as i32), // input_data_len
				Instruction::I32Const(SENTINEL as i32), // address_ptr
				Instruction::I32Const(0), // address_len_ptr
				Instruction::I32Const(SENTINEL as i32), // output_ptr
				Instruction::I32Const(0), // output_len_ptr
				Instruction::I32Const(0 as i32), // salt_ptr
				Instruction::I32Const(s as i32), // salt_len
				Instruction::Call(0),
				Instruction::I32Eqz,
				Instruction::If(BlockType::NoResult),
				Instruction::Nop,
				Instruction::Else,
				Instruction::Unreachable,
				Instruction::End,
				Instruction::End,
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		instance.set_balance(value + (Pallet::<T>::min_balance() * 2u32.into()));
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// Only the overhead of calling the function itself with minimal arguments.
	#[pov_mode = Measured]
	seal_hash_sha2_256 {
		let r in 0 .. API_BENCHMARK_RUNS;
		let instance = Contract::<T>::new(WasmModule::hasher(
			"seal_hash_sha2_256", r, 0,
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// `n`: Input to hash in bytes
	#[pov_mode = Measured]
	seal_hash_sha2_256_per_byte {
		let n in 0 .. code::max_pages::<T>() * 64 * 1024;
		let instance = Contract::<T>::new(WasmModule::hasher(
			"seal_hash_sha2_256", 1, n,
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// Only the overhead of calling the function itself with minimal arguments.
	#[pov_mode = Measured]
	seal_hash_keccak_256 {
		let r in 0 .. API_BENCHMARK_RUNS;
		let instance = Contract::<T>::new(WasmModule::hasher(
			"seal_hash_keccak_256", r, 0,
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// `n`: Input to hash in bytes
	#[pov_mode = Measured]
	seal_hash_keccak_256_per_byte {
		let n in 0 .. code::max_pages::<T>() * 64 * 1024;
		let instance = Contract::<T>::new(WasmModule::hasher(
			"seal_hash_keccak_256", 1, n,
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// Only the overhead of calling the function itself with minimal arguments.
	#[pov_mode = Measured]
	seal_hash_blake2_256 {
		let r in 0 .. API_BENCHMARK_RUNS;
		let instance = Contract::<T>::new(WasmModule::hasher(
			"seal_hash_blake2_256", r, 0,
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// `n`: Input to hash in bytes
	#[pov_mode = Measured]
	seal_hash_blake2_256_per_byte {
		let n in 0 .. code::max_pages::<T>() * 64 * 1024;
		let instance = Contract::<T>::new(WasmModule::hasher(
			"seal_hash_blake2_256", 1, n,
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// Only the overhead of calling the function itself with minimal arguments.
	#[pov_mode = Measured]
	seal_hash_blake2_128 {
		let r in 0 .. API_BENCHMARK_RUNS;
		let instance = Contract::<T>::new(WasmModule::hasher(
			"seal_hash_blake2_128", r, 0,
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// `n`: Input to hash in bytes
	#[pov_mode = Measured]
	seal_hash_blake2_128_per_byte {
		let n in 0 .. code::max_pages::<T>() * 64 * 1024;
		let instance = Contract::<T>::new(WasmModule::hasher(
			"seal_hash_blake2_128", 1, n,
		), vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// `n`: Message input length to verify in bytes.
	#[pov_mode = Measured]
	seal_sr25519_verify_per_byte {
		let n in 0 .. T::MaxCodeLen::get() - 255; // need some buffer so the code size does not
												  // exceed the max code size.

		let message = (0..n).zip((32u8..127u8).cycle()).map(|(_, c)| c).collect::<Vec<_>>();
		let message_len = message.len() as i32;

		let key_type = sp_core::crypto::KeyTypeId(*b"code");
		let pub_key = sp_io::crypto::sr25519_generate(key_type, None);
		let sig = sp_io::crypto::sr25519_sign(key_type, &pub_key, &message).expect("Generates signature");
		let sig = AsRef::<[u8; 64]>::as_ref(&sig).to_vec();

		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "sr25519_verify",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: sig,
				},
				DataSegment {
					offset: 64,
					value: pub_key.to_vec(),
				},
				DataSegment {
					offset: 96,
					value: message,
				},
			],
			call_body: Some(body::plain(vec![
				Instruction::I32Const(0), // signature_ptr
				Instruction::I32Const(64), // pub_key_ptr
				Instruction::I32Const(message_len), // message_len
				Instruction::I32Const(96), // message_ptr
				Instruction::Call(0),
				Instruction::Drop,
				Instruction::End,
			])),
			.. Default::default()
		});

		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// Only calling the function itself with valid arguments.
	// It generates different private keys and signatures for the message "Hello world".
	// This is a slow call: We reduce the number of runs.
	#[pov_mode = Measured]
	seal_sr25519_verify {
		let r in 0 .. API_BENCHMARK_RUNS / 10;

		let message = b"Hello world".to_vec();
		let message_len = message.len() as i32;
		let key_type = sp_core::crypto::KeyTypeId(*b"code");
		let sig_params = (0..r)
			.map(|i| {
				let pub_key = sp_io::crypto::sr25519_generate(key_type, None);
				let sig = sp_io::crypto::sr25519_sign(key_type, &pub_key, &message).expect("Generates signature");
				let data: [u8; 96] = [AsRef::<[u8]>::as_ref(&sig), AsRef::<[u8]>::as_ref(&pub_key)].concat().try_into().unwrap();
				data
			})
			.flatten()
			.collect::<Vec<_>>();
		let sig_params_len = sig_params.len() as i32;

		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "sr25519_verify",
				params: vec![ValueType::I32, ValueType::I32, ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: sig_params
				},
				DataSegment {
					offset: sig_params_len as u32,
					value: message,
				},
			],
			call_body: Some(body::repeated_dyn(r, vec![
				Counter(0, 96), // signature_ptr
				Counter(64, 96), // pub_key_ptr
				Regular(Instruction::I32Const(message_len)), // message_len
				Regular(Instruction::I32Const(sig_params_len)), // message_ptr
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// Only calling the function itself with valid arguments.
	// It generates different private keys and signatures for the message "Hello world".
	// This is a slow call: We reduce the number of runs.
	#[pov_mode = Measured]
	seal_ecdsa_recover {
		let r in 0 .. API_BENCHMARK_RUNS / 10;

		let message_hash = sp_io::hashing::blake2_256("Hello world".as_bytes());
		let key_type = sp_core::crypto::KeyTypeId(*b"code");
		let signatures = (0..r)
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
				module: "seal0",
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
			call_body: Some(body::repeated_dyn(r, vec![
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

	// Only calling the function itself for the list of
	// generated different ECDSA keys.
	// This is a slow call: We redeuce the number of runs.
	#[pov_mode = Measured]
	seal_ecdsa_to_eth_address {
		let r in 0 .. API_BENCHMARK_RUNS / 10;
		let key_type = sp_core::crypto::KeyTypeId(*b"code");
		let pub_keys_bytes = (0..r)
			.flat_map(|_| {
				sp_io::crypto::ecdsa_generate(key_type, None).0
			})
		.collect::<Vec<_>>();
		let pub_keys_bytes_len = pub_keys_bytes.len() as i32;
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "seal_ecdsa_to_eth_address",
				params: vec![ValueType::I32, ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: pub_keys_bytes,
				},
			],
			call_body: Some(body::repeated_dyn(r, vec![
				Counter(0, 33), // pub_key_ptr
				Regular(Instruction::I32Const(pub_keys_bytes_len)), // out_ptr
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[pov_mode = Measured]
	seal_set_code_hash {
		let r in 0 .. API_BENCHMARK_RUNS;
		let code_hashes = (0..r)
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
				module: "seal0",
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
			call_body: Some(body::repeated_dyn(r, vec![
				Counter(0, code_hash_len as u32), // code_hash_ptr
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[pov_mode = Measured]
	seal_reentrance_count {
		let r in 0 .. API_BENCHMARK_RUNS;
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "reentrance_count",
				params: vec![],
				return_type: Some(ValueType::I32),
			}],
			call_body: Some(body::repeated(r, &[
				Instruction::Call(0),
				Instruction::Drop,
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[pov_mode = Measured]
	seal_account_reentrance_count {
		let r in 0 .. API_BENCHMARK_RUNS;
		let dummy_code = WasmModule::<T>::dummy_with_bytes(0);
		let accounts = (0..r)
			.map(|i| Contract::with_index(i + 1, dummy_code.clone(), vec![]))
			.collect::<Result<Vec<_>, _>>()?;
		let account_id_len = accounts.get(0).map(|i| i.account_id.encode().len()).unwrap_or(0);
		let account_id_bytes = accounts.iter().flat_map(|x| x.account_id.encode()).collect();
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "account_reentrance_count",
				params: vec![ValueType::I32],
				return_type: Some(ValueType::I32),
			}],
			data_segments: vec![
				DataSegment {
					offset: 0,
					value: account_id_bytes,
				},
			],
			call_body: Some(body::repeated_dyn(r, vec![
				Counter(0, account_id_len as u32), // account_ptr
				Regular(Instruction::Call(0)),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	#[pov_mode = Measured]
	seal_instantiation_nonce {
		let r in 0 .. API_BENCHMARK_RUNS;
		let code = WasmModule::<T>::from(ModuleDefinition {
			memory: Some(ImportedMemory::max::<T>()),
			imported_functions: vec![ImportedFunction {
				module: "seal0",
				name: "instantiation_nonce",
				params: vec![],
				return_type: Some(ValueType::I64),
			}],
			call_body: Some(body::repeated(r, &[
				Instruction::Call(0),
				Instruction::Drop,
			])),
			.. Default::default()
		});
		let instance = Contract::<T>::new(code, vec![])?;
		let origin = RawOrigin::Signed(instance.caller.clone());
	}: call(origin, instance.addr, 0u32.into(), Weight::MAX, None, vec![])

	// We make the assumption that pushing a constant and dropping a value takes roughly
	// the same amount of time. We call this weight `w_base`.
	// The weight that would result from the respective benchmark we call: `w_bench`.
	//
	// w_base = w_i{32,64}const = w_drop = w_bench / 2
	#[pov_mode = Ignored]
	instr_i64const {
		let r in 0 .. INSTR_BENCHMARK_RUNS;
		let mut sbox = Sandbox::from(&WasmModule::<T>::from(ModuleDefinition {
			call_body: Some(body::repeated_dyn(r, vec![
				RandomI64Repeated(1),
				Regular(Instruction::Drop),
			])),
			.. Default::default()
		}));
	}: {
		sbox.invoke();
	}

	// This is no benchmark. It merely exist to have an easy way to pretty print the currently
	// configured `Schedule` during benchmark development.
	// It can be outputted using the following command:
	// cargo run --manifest-path=bin/node/cli/Cargo.toml \
	//     --features runtime-benchmarks -- benchmark pallet --extra --dev --execution=native \
	//     -p pallet_contracts -e print_schedule --no-median-slopes --no-min-squares
	#[extra]
	#[pov_mode = Ignored]
	print_schedule {
		#[cfg(feature = "std")]
		{
			let max_weight = <T as frame_system::Config>::BlockWeights::get().max_block;
			let (weight_per_key, key_budget) = ContractInfo::<T>::deletion_budget(max_weight);
			println!("{:#?}", Schedule::<T>::default());
			println!("###############################################");
			println!("Lazy deletion weight per key: {weight_per_key}");
			println!("Lazy deletion throughput per block: {key_budget}");
		}
		#[cfg(not(feature = "std"))]
		Err("Run this bench with a native runtime in order to see the schedule.")?;
	}: {}

	// Execute one erc20 transfer using the ink! erc20 example contract.
	#[extra]
	#[pov_mode = Measured]
	ink_erc20_transfer {
		let code = load_benchmark!("ink_erc20");
		let data = {
			let new: ([u8; 4], BalanceOf<T>) = ([0x9b, 0xae, 0x9d, 0x5e], 1000u32.into());
			new.encode()
		};
		let instance = Contract::<T>::new(
			WasmModule::from_code(code), data,
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
			DebugInfo::Skip,
			CollectEvents::Skip,
			Determinism::Enforced,
		)
		.result?;
	}

	// Execute one erc20 transfer using the open zeppelin erc20 contract compiled with solang.
	#[extra]
	#[pov_mode = Measured]
	solang_erc20_transfer {
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
			caller, WasmModule::from_code(code), data,
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
			DebugInfo::Skip,
			CollectEvents::Skip,
			Determinism::Enforced,
		)
		.result?;
	}

	impl_benchmark_test_suite!(
		Contracts,
		crate::tests::ExtBuilder::default().build(),
		crate::tests::Test,
	)
}
