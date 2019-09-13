// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Wasm interface module.
//!
//! This module defines and implements the wasm part of Substrate Host Interface and provides
//! an interface for calling into the wasm runtime.

use std::str;
use wasmi::{
	Module, ModuleInstance, MemoryInstance, MemoryRef, TableRef, ImportsBuilder, ModuleRef,
	memory_units::Pages, RuntimeValue::{I32, I64, self},
};
use crate::error::{Error, Result};
use codec::{Encode, Decode};
use primitives::{sandbox as sandbox_primitives, Blake2Hasher, traits::Externalities};
use crate::host_interface::SubstrateExternals;
use crate::sandbox;
use crate::allocator;
use log::trace;
use wasm_interface::{
	FunctionContext, HostFunctions, Pointer, WordSize, Sandbox, MemoryId, Result as WResult,
};

struct FunctionExecutor {
	sandbox_store: sandbox::Store<wasmi::FuncRef>,
	heap: allocator::FreeingBumpHeapAllocator,
	memory: MemoryRef,
	table: Option<TableRef>,
}

impl FunctionExecutor {
	fn new(m: MemoryRef, heap_base: u32, t: Option<TableRef>) -> Result<Self> {
		Ok(FunctionExecutor {
			sandbox_store: sandbox::Store::new(),
			heap: allocator::FreeingBumpHeapAllocator::new(heap_base),
			memory: m,
			table: t,
		})
	}
}

impl sandbox::SandboxCapabilities for FunctionExecutor {
	type SupervisorFuncRef = wasmi::FuncRef;

	fn store(&self) -> &sandbox::Store<Self::SupervisorFuncRef> {
		&self.sandbox_store
	}
	fn store_mut(&mut self) -> &mut sandbox::Store<Self::SupervisorFuncRef> {
		&mut self.sandbox_store
	}
	fn allocate(&mut self, len: WordSize) -> Result<Pointer<u8>> {
		let heap = &mut self.heap;
		self.memory.with_direct_access_mut(|mem| {
			heap.allocate(mem, len)
		})
	}
	fn deallocate(&mut self, ptr: Pointer<u8>) -> Result<()> {
		let heap = &mut self.heap;
		self.memory.with_direct_access_mut(|mem| {
			heap.deallocate(mem, ptr)
		})
	}
	fn write_memory(&mut self, ptr: Pointer<u8>, data: &[u8]) -> Result<()> {
		self.memory.set(ptr.into(), data).map_err(Into::into)
	}
	fn read_memory(&self, ptr: Pointer<u8>, len: WordSize) -> Result<Vec<u8>> {
		self.memory.get(ptr.into(), len as usize).map_err(Into::into)
	}

	fn invoke(
		&mut self,
		dispatch_thunk: &Self::SupervisorFuncRef,
		invoke_args_ptr: Pointer<u8>,
		invoke_args_len: WordSize,
		state: u32,
		func_idx: sandbox::SupervisorFuncIndex,
	) -> Result<i64>
	{
		let result = wasmi::FuncInstance::invoke(
			dispatch_thunk,
			&[
				RuntimeValue::I32(u32::from(invoke_args_ptr) as i32),
				RuntimeValue::I32(invoke_args_len as i32),
				RuntimeValue::I32(state as i32),
				RuntimeValue::I32(usize::from(func_idx) as i32),
			],
			self,
		);
		match result {
			Ok(Some(RuntimeValue::I64(val))) => Ok(val),
			Ok(_) => return Err("Supervisor function returned unexpected result!".into()),
			Err(err) => Err(Error::Trap(err)),
		}
	}
}

impl FunctionContext for FunctionExecutor {
	fn read_memory_into(&self, address: Pointer<u8>, dest: &mut [u8]) -> WResult<()> {
		self.memory.get_into(address.into(), dest).map_err(|e| format!("{:?}", e))
	}

	fn write_memory(&mut self, address: Pointer<u8>, data: &[u8]) -> WResult<()> {
		self.memory.set(address.into(), data).map_err(|e| format!("{:?}", e))
	}

	fn allocate_memory(&mut self, size: WordSize) -> WResult<Pointer<u8>> {
		let heap = &mut self.heap;
		self.memory.with_direct_access_mut(|mem| {
			heap.allocate(mem, size).map_err(|e| format!("{:?}", e))
		})
	}

	fn deallocate_memory(&mut self, ptr: Pointer<u8>) -> WResult<()> {
		let heap = &mut self.heap;
		self.memory.with_direct_access_mut(|mem| {
			heap.deallocate(mem, ptr).map_err(|e| format!("{:?}", e))
		})
	}

	fn sandbox(&mut self) -> &mut dyn Sandbox {
		self
	}
}

impl Sandbox for FunctionExecutor {
	fn memory_get(
		&self,
		memory_id: MemoryId,
		offset: WordSize,
		buf_ptr: Pointer<u8>,
		buf_len: WordSize,
	) -> WResult<u32> {
		let sandboxed_memory = self.sandbox_store.memory(memory_id).map_err(|e| format!("{:?}", e))?;

		match MemoryInstance::transfer(
			&sandboxed_memory,
			offset as usize,
			&self.memory,
			buf_ptr.into(),
			buf_len as usize,
		) {
			Ok(()) => Ok(sandbox_primitives::ERR_OK),
			Err(_) => Ok(sandbox_primitives::ERR_OUT_OF_BOUNDS),
		}
	}

	fn memory_set(
		&mut self,
		memory_id: MemoryId,
		offset: WordSize,
		val_ptr: Pointer<u8>,
		val_len: WordSize,
	) -> WResult<u32> {
		let sandboxed_memory = self.sandbox_store.memory(memory_id).map_err(|e| format!("{:?}", e))?;

		match MemoryInstance::transfer(
			&self.memory,
			val_ptr.into(),
			&sandboxed_memory,
			offset as usize,
			val_len as usize,
		) {
			Ok(()) => Ok(sandbox_primitives::ERR_OK),
			Err(_) => Ok(sandbox_primitives::ERR_OUT_OF_BOUNDS),
		}
	}

	fn memory_teardown(&mut self, memory_id: MemoryId) -> WResult<()> {
		self.sandbox_store.memory_teardown(memory_id).map_err(|e| format!("{:?}", e))
	}

	fn memory_new(
		&mut self,
		initial: u32,
		maximum: u32,
	) -> WResult<MemoryId> {
		self.sandbox_store.new_memory(initial, maximum).map_err(|e| format!("{:?}", e))
	}

	fn invoke(
		&mut self,
		instance_id: u32,
		export_name: &str,
		args: &[u8],
		return_val: Pointer<u8>,
		return_val_len: WordSize,
		state: u32,
	) -> WResult<u32> {
		trace!(target: "sr-sandbox", "invoke, instance_idx={}", instance_id);

		// Deserialize arguments and convert them into wasmi types.
		let args = Vec::<sandbox_primitives::TypedValue>::decode(&mut &args[..])
			.map_err(|_| "Can't decode serialized arguments for the invocation")?
			.into_iter()
			.map(Into::into)
			.collect::<Vec<_>>();

		let instance = self.sandbox_store.instance(instance_id).map_err(|e| format!("{:?}", e))?;
		let result = instance.invoke(export_name, &args, self, state);

		match result {
			Ok(None) => Ok(sandbox_primitives::ERR_OK),
			Ok(Some(val)) => {
				// Serialize return value and write it back into the memory.
				sandbox_primitives::ReturnValue::Value(val.into()).using_encoded(|val| {
					if val.len() > return_val_len as usize {
						Err("Return value buffer is too small")?;
					}
					self.write_memory(return_val, val).map_err(|_| "Return value buffer is OOB")?;
					Ok(sandbox_primitives::ERR_OK)
				})
			}
			Err(_) => Ok(sandbox_primitives::ERR_EXECUTION),
		}
	}

	fn instance_teardown(&mut self, instance_id: u32) -> WResult<()> {
		self.sandbox_store.instance_teardown(instance_id).map_err(|e| format!("{:?}", e))
	}

	fn instance_new(
		&mut self,
		dispatch_thunk_id: u32,
		wasm: &[u8],
		raw_env_def: &[u8],
		state: u32,
	) -> WResult<u32> {
		// Extract a dispatch thunk from instance's table by the specified index.
		let dispatch_thunk = {
			let table = self.table.as_ref()
				.ok_or_else(|| "Runtime doesn't have a table; sandbox is unavailable")?;
			table.get(dispatch_thunk_id)
				.map_err(|_| "dispatch_thunk_idx is out of the table bounds")?
				.ok_or_else(|| "dispatch_thunk_idx points on an empty table entry")?
				.clone()
		};

		let instance_idx_or_err_code =
			match sandbox::instantiate(self, dispatch_thunk, wasm, raw_env_def, state) {
				Ok(instance_idx) => instance_idx,
				Err(sandbox::InstantiationError::StartTrapped) =>
					sandbox_primitives::ERR_EXECUTION,
				Err(_) => sandbox_primitives::ERR_MODULE,
			};

		Ok(instance_idx_or_err_code as u32)
	}
}

impl FunctionExecutor {
	fn resolver() -> &'static dyn wasmi::ModuleImportResolver {
		struct Resolver;
		impl wasmi::ModuleImportResolver for Resolver {
			fn resolve_func(&self, name: &str, signature: &wasmi::Signature)
				-> std::result::Result<wasmi::FuncRef, wasmi::Error>
			{
				let signature = wasm_interface::Signature::from(signature);

				if let Some((index, func)) = SubstrateExternals::functions().iter()
					.enumerate()
					.find(|f| name == f.1.name())
				{
					if signature == func.signature() {
						Ok(wasmi::FuncInstance::alloc_host(signature.into(), index))
					} else {
						Err(wasmi::Error::Instantiation(
							format!(
								"Invalid signature for function `{}` expected `{:?}`, got `{:?}`",
								func.name(),
								signature,
								func.signature(),
							)
						))
					}
				} else {
					Err(wasmi::Error::Instantiation(
						format!("Export {} not found", name),
					))
				}
			}
		}
		&Resolver
	}
}

impl wasmi::Externals for FunctionExecutor {
	fn invoke_index(&mut self, index: usize, args: wasmi::RuntimeArgs)
		-> std::result::Result<Option<wasmi::RuntimeValue>, wasmi::Trap>
	{
		let mut args = args.as_ref().iter().copied().map(Into::into);
		let function = SubstrateExternals::functions().get(index).ok_or_else(||
			Error::from(
				format!("Could not find host function with index: {}", index),
			)
		)?;

		function.execute(self, &mut args)
			.map_err(Error::FunctionExecution)
			.map_err(wasmi::Trap::from)
			.map(|v| v.map(Into::into))
	}
}

/// Call a given method in the given code.
///
/// Signature of this method needs to be `(I32, I32) -> I64`.
///
/// This should be used for tests only.
#[cfg(test)]
pub fn call(
	ext: &mut dyn Externalities<Blake2Hasher>,
	heap_pages: usize,
	code: &[u8],
	method: &str,
	data: &[u8],
) -> Result<Vec<u8>> {
	let module = wasmi::Module::from_buffer(code)?;
	let module = instantiate_module(heap_pages, &module)?;

	call_in_wasm_module(ext, &module, method, data)
}

fn get_mem_instance(module: &ModuleRef) -> Result<MemoryRef> {
	Ok(module
		.export_by_name("memory")
		.ok_or_else(|| Error::InvalidMemoryReference)?
		.as_memory()
		.ok_or_else(|| Error::InvalidMemoryReference)?
		.clone())
}

/// Find the global named `__heap_base` in the given wasm module instance and
/// tries to get its value.
fn get_heap_base(module: &ModuleRef) -> Result<u32> {
	let heap_base_val = module
		.export_by_name("__heap_base")
		.ok_or_else(|| Error::HeapBaseNotFoundOrInvalid)?
		.as_global()
		.ok_or_else(|| Error::HeapBaseNotFoundOrInvalid)?
		.get();

	match heap_base_val {
		wasmi::RuntimeValue::I32(v) => Ok(v as u32),
		_ => Err(Error::HeapBaseNotFoundOrInvalid),
	}
}

/// Call a given method in the given wasm-module runtime.
pub fn call_in_wasm_module(
	ext: &mut dyn Externalities<Blake2Hasher>,
	module_instance: &ModuleRef,
	method: &str,
	data: &[u8],
) -> Result<Vec<u8>> {
	call_in_wasm_module_with_custom_signature(
		ext,
		module_instance,
		method,
		|alloc| {
			let offset = alloc(data)?;
			Ok(vec![I32(offset as i32), I32(data.len() as i32)])
		},
		|res, memory| {
			if let Some(I64(r)) = res {
				let offset = r as u32;
				let length = (r as u64 >> 32) as usize;
				memory.get(offset, length).map_err(|_| Error::Runtime).map(Some)
			} else {
				Ok(None)
			}
		}
	)
}

/// Call a given method in the given wasm-module runtime.
fn call_in_wasm_module_with_custom_signature<
	F: FnOnce(&mut dyn FnMut(&[u8]) -> Result<u32>) -> Result<Vec<RuntimeValue>>,
	FR: FnOnce(Option<RuntimeValue>, &MemoryRef) -> Result<Option<R>>,
	R,
>(
	ext: &mut dyn Externalities<Blake2Hasher>,
	module_instance: &ModuleRef,
	method: &str,
	create_parameters: F,
	filter_result: FR,
) -> Result<R> {
	// extract a reference to a linear memory, optional reference to a table
	// and then initialize FunctionExecutor.
	let memory = get_mem_instance(module_instance)?;
	let table: Option<TableRef> = module_instance
		.export_by_name("__indirect_function_table")
		.and_then(|e| e.as_table().cloned());
	let heap_base = get_heap_base(module_instance)?;

	let mut fec = FunctionExecutor::new(
		memory.clone(),
		heap_base,
		table,
	)?;

	let parameters = create_parameters(&mut |data: &[u8]| {
		let offset = fec.allocate_memory(data.len() as u32)?;
		fec.write_memory(offset, data).map(|_| offset.into()).map_err(Into::into)
	})?;

	let result = runtime_io::with_externalities(
		ext,
		|| module_instance.invoke_export(method, &parameters, &mut fec),
	);

	match result {
		Ok(val) => match filter_result(val, &memory)? {
			Some(val) => Ok(val),
			None => Err(Error::InvalidReturn),
		},
		Err(e) => {
			trace!(
				target: "wasm-executor",
				"Failed to execute code with {} pages",
				memory.current_size().0
			);
			Err(e.into())
		},
	}
}

/// Prepare module instance
pub fn instantiate_module(
	heap_pages: usize,
	module: &Module,
) -> Result<ModuleRef> {
	// start module instantiation. Don't run 'start' function yet.
	let intermediate_instance = ModuleInstance::new(
		module,
		&ImportsBuilder::new()
			.with_resolver("env", FunctionExecutor::resolver())
	)?;

	// Verify that the module has the heap base global variable.
	let _ = get_heap_base(intermediate_instance.not_started_instance())?;

	// Extract a reference to a linear memory.
	let memory = get_mem_instance(intermediate_instance.not_started_instance())?;
	memory.grow(Pages(heap_pages)).map_err(|_| Error::Runtime)?;

	if intermediate_instance.has_start() {
		// Runtime is not allowed to have the `start` function.
		Err(Error::RuntimeHasStartFn)
	} else {
		Ok(intermediate_instance.assert_no_start())
	}
}


#[cfg(test)]
mod tests {
	use super::*;

	use state_machine::TestExternalities as CoreTestExternalities;
	use hex_literal::hex;
	use primitives::{blake2_128, blake2_256, ed25519, sr25519, map, Pair};
	use runtime_test::WASM_BINARY;
	use substrate_offchain::testing;
	use trie::{TrieConfiguration, trie_types::Layout};

	type TestExternalities<H> = CoreTestExternalities<H, u64>;

	#[test]
	fn returning_should_work() {
		let mut ext = TestExternalities::default();
		let test_code = WASM_BINARY;

		let output = call(&mut ext, 8, &test_code[..], "test_empty_return", &[]).unwrap();
		assert_eq!(output, vec![0u8; 0]);
	}

	#[test]
	fn panicking_should_work() {
		let mut ext = TestExternalities::default();
		let test_code = WASM_BINARY;

		let output = call(&mut ext, 8, &test_code[..], "test_panic", &[]);
		assert!(output.is_err());

		let output = call(&mut ext, 8, &test_code[..], "test_conditional_panic", &[]);
		assert_eq!(output.unwrap(), vec![0u8; 0]);

		let output = call(&mut ext, 8, &test_code[..], "test_conditional_panic", &[2]);
		assert!(output.is_err());
	}

	#[test]
	fn storage_should_work() {
		let mut ext = TestExternalities::default();
		ext.set_storage(b"foo".to_vec(), b"bar".to_vec());
		let test_code = WASM_BINARY;

		let output = call(&mut ext, 8, &test_code[..], "test_data_in", b"Hello world").unwrap();

		assert_eq!(output, b"all ok!".to_vec());

		let expected = TestExternalities::new((map![
			b"input".to_vec() => b"Hello world".to_vec(),
			b"foo".to_vec() => b"bar".to_vec(),
			b"baz".to_vec() => b"bar".to_vec()
		], map![]));
		assert_eq!(ext, expected);
	}

	#[test]
	fn clear_prefix_should_work() {
		let mut ext = TestExternalities::default();
		ext.set_storage(b"aaa".to_vec(), b"1".to_vec());
		ext.set_storage(b"aab".to_vec(), b"2".to_vec());
		ext.set_storage(b"aba".to_vec(), b"3".to_vec());
		ext.set_storage(b"abb".to_vec(), b"4".to_vec());
		ext.set_storage(b"bbb".to_vec(), b"5".to_vec());
		let test_code = WASM_BINARY;

		// This will clear all entries which prefix is "ab".
		let output = call(&mut ext, 8, &test_code[..], "test_clear_prefix", b"ab").unwrap();

		assert_eq!(output, b"all ok!".to_vec());

		let expected = TestExternalities::new((map![
			b"aaa".to_vec() => b"1".to_vec(),
			b"aab".to_vec() => b"2".to_vec(),
			b"bbb".to_vec() => b"5".to_vec()
		], map![]));
		assert_eq!(expected, ext);
	}

	#[test]
	fn blake2_256_should_work() {
		let mut ext = TestExternalities::default();
		let test_code = WASM_BINARY;
		assert_eq!(
			call(&mut ext, 8, &test_code[..], "test_blake2_256", &[]).unwrap(),
			blake2_256(&b""[..]).encode()
		);
		assert_eq!(
			call(&mut ext, 8, &test_code[..], "test_blake2_256", b"Hello world!").unwrap(),
			blake2_256(&b"Hello world!"[..]).encode()
		);
	}

	#[test]
	fn blake2_128_should_work() {
		let mut ext = TestExternalities::default();
		let test_code = WASM_BINARY;
		assert_eq!(
			call(&mut ext, 8, &test_code[..], "test_blake2_128", &[]).unwrap(),
			blake2_128(&b""[..]).encode()
		);
		assert_eq!(
			call(&mut ext, 8, &test_code[..], "test_blake2_128", b"Hello world!").unwrap(),
			blake2_128(&b"Hello world!"[..]).encode()
		);
	}

	#[test]
	fn twox_256_should_work() {
		let mut ext = TestExternalities::default();
		let test_code = WASM_BINARY;
		assert_eq!(
			call(&mut ext, 8, &test_code[..], "test_twox_256", &[]).unwrap(),
			hex!("99e9d85137db46ef4bbea33613baafd56f963c64b1f3685a4eb4abd67ff6203a"),
		);
		assert_eq!(
			call(&mut ext, 8, &test_code[..], "test_twox_256", b"Hello world!").unwrap(),
			hex!("b27dfd7f223f177f2a13647b533599af0c07f68bda23d96d059da2b451a35a74"),
		);
	}

	#[test]
	fn twox_128_should_work() {
		let mut ext = TestExternalities::default();
		let test_code = WASM_BINARY;
		assert_eq!(
			call(&mut ext, 8, &test_code[..], "test_twox_128", &[]).unwrap(),
			hex!("99e9d85137db46ef4bbea33613baafd5")
		);
		assert_eq!(
			call(&mut ext, 8, &test_code[..], "test_twox_128", b"Hello world!").unwrap(),
			hex!("b27dfd7f223f177f2a13647b533599af")
		);
	}

	#[test]
	fn ed25519_verify_should_work() {
		let mut ext = TestExternalities::<Blake2Hasher>::default();
		let test_code = WASM_BINARY;
		let key = ed25519::Pair::from_seed(&blake2_256(b"test"));
		let sig = key.sign(b"all ok!");
		let mut calldata = vec![];
		calldata.extend_from_slice(key.public().as_ref());
		calldata.extend_from_slice(sig.as_ref());

		assert_eq!(
			call(&mut ext, 8, &test_code[..], "test_ed25519_verify", &calldata).unwrap(),
			vec![1]
		);

		let other_sig = key.sign(b"all is not ok!");
		let mut calldata = vec![];
		calldata.extend_from_slice(key.public().as_ref());
		calldata.extend_from_slice(other_sig.as_ref());

		assert_eq!(
			call(&mut ext, 8, &test_code[..], "test_ed25519_verify", &calldata).unwrap(),
			vec![0]
		);
	}

	#[test]
	fn sr25519_verify_should_work() {
		let mut ext = TestExternalities::<Blake2Hasher>::default();
		let test_code = WASM_BINARY;
		let key = sr25519::Pair::from_seed(&blake2_256(b"test"));
		let sig = key.sign(b"all ok!");
		let mut calldata = vec![];
		calldata.extend_from_slice(key.public().as_ref());
		calldata.extend_from_slice(sig.as_ref());

		assert_eq!(
			call(&mut ext, 8, &test_code[..], "test_sr25519_verify", &calldata).unwrap(),
			vec![1]
		);

		let other_sig = key.sign(b"all is not ok!");
		let mut calldata = vec![];
		calldata.extend_from_slice(key.public().as_ref());
		calldata.extend_from_slice(other_sig.as_ref());

		assert_eq!(
			call(&mut ext, 8, &test_code[..], "test_sr25519_verify", &calldata).unwrap(),
			vec![0]
		);
	}

	#[test]
	fn ordered_trie_root_should_work() {
		let mut ext = TestExternalities::<Blake2Hasher>::default();
		let trie_input = vec![b"zero".to_vec(), b"one".to_vec(), b"two".to_vec()];
		let test_code = WASM_BINARY;
		assert_eq!(
			call(&mut ext, 8, &test_code[..], "test_ordered_trie_root", &[]).unwrap(),
			Layout::<Blake2Hasher>::ordered_trie_root(trie_input.iter()).as_fixed_bytes().encode()
		);
	}

	#[test]
	fn offchain_local_storage_should_work() {
		use substrate_client::backend::OffchainStorage;

		let mut ext = TestExternalities::<Blake2Hasher>::default();
		let (offchain, state) = testing::TestOffchainExt::new();
		ext.set_offchain_externalities(offchain);
		let test_code = WASM_BINARY;
		assert_eq!(
			call(&mut ext, 8, &test_code[..], "test_offchain_local_storage", &[]).unwrap(),
			vec![0]
		);
		assert_eq!(state.read().persistent_storage.get(b"", b"test"), Some(vec![]));
	}

	#[test]
	fn offchain_http_should_work() {
		let mut ext = TestExternalities::<Blake2Hasher>::default();
		let (offchain, state) = testing::TestOffchainExt::new();
		ext.set_offchain_externalities(offchain);
		state.write().expect_request(
			0,
			testing::PendingRequest {
				method: "POST".into(),
				uri: "http://localhost:12345".into(),
				body: vec![1, 2, 3, 4],
				headers: vec![("X-Auth".to_owned(), "test".to_owned())],
				sent: true,
				response: Some(vec![1, 2, 3]),
				response_headers: vec![("X-Auth".to_owned(), "hello".to_owned())],
				..Default::default()
			},
		);

		let test_code = WASM_BINARY;
		assert_eq!(
			call(&mut ext, 8, &test_code[..], "test_offchain_http", &[]).unwrap(),
			vec![0]
		);
	}
}
