// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Defines the compiled Wasm runtime that uses Wasmtime internally.

use crate::host::HostState;
use crate::imports::{Imports, resolve_imports};
use crate::instance_wrapper::{InstanceWrapper, EntryPoint};
use crate::state_holder;

use std::{path::PathBuf, rc::Rc};
use std::sync::Arc;
use std::path::Path;
use sc_executor_common::{
	error::{Result, WasmError},
	runtime_blob::{DataSegmentsSnapshot, ExposedMutableGlobalsSet, GlobalsSnapshot, RuntimeBlob},
	wasm_runtime::{WasmModule, WasmInstance, InvokeMethod},
};
use sp_allocator::FreeingBumpHeapAllocator;
use sp_runtime_interface::unpack_ptr_and_len;
use sp_wasm_interface::{Function, Pointer, WordSize, Value};
use wasmtime::{Engine, Store};

enum Strategy {
	FastInstanceReuse {
		instance_wrapper: Rc<InstanceWrapper>,
		globals_snapshot: GlobalsSnapshot<wasmtime::Global>,
		data_segments_snapshot: Arc<DataSegmentsSnapshot>,
		heap_base: u32,
	},
	RecreateInstance(InstanceCreator),
}

struct InstanceCreator {
	store: Store,
	module: Arc<wasmtime::Module>,
	imports: Arc<Imports>,
	heap_pages: u32,
}

impl InstanceCreator {
	fn instantiate(&self) -> Result<InstanceWrapper> {
		InstanceWrapper::new(&self.store, &*self.module, &*self.imports, self.heap_pages)
	}
}

/// Data required for creating instances with the fast instance reuse strategy.
struct InstanceSnapshotData {
	mutable_globals: ExposedMutableGlobalsSet,
	data_segments_snapshot: Arc<DataSegmentsSnapshot>,
}

/// A `WasmModule` implementation using wasmtime to compile the runtime module to machine code
/// and execute the compiled code.
pub struct WasmtimeRuntime {
	module: Arc<wasmtime::Module>,
	snapshot_data: Option<InstanceSnapshotData>,
	config: Config,
	host_functions: Vec<&'static dyn Function>,
	engine: Engine,
}

impl WasmModule for WasmtimeRuntime {
	fn new_instance(&self) -> Result<Box<dyn WasmInstance>> {
		let store = Store::new(&self.engine);

		// Scan all imports, find the matching host functions, and create stubs that adapt arguments
		// and results.
		//
		// NOTE: Attentive reader may notice that this could've been moved in `WasmModule` creation.
		//       However, I am not sure if that's a good idea since it would be pushing our luck further
		//       by assuming that `Store` not only `Send` but also `Sync`.
		let imports = resolve_imports(
			&store,
			&self.module,
			&self.host_functions,
			self.config.heap_pages,
			self.config.allow_missing_func_imports,
		)?;

		let strategy = if let Some(ref snapshot_data) = self.snapshot_data {
			let instance_wrapper =
				InstanceWrapper::new(&store, &self.module, &imports, self.config.heap_pages)?;
			let heap_base = instance_wrapper.extract_heap_base()?;

			// This function panics if the instance was created from a runtime blob different from which
			// the mutable globals were collected. Here, it is easy to see that there is only a single
			// runtime blob and thus it's the same that was used for both creating the instance and
			// collecting the mutable globals.
			let globals_snapshot = GlobalsSnapshot::take(&snapshot_data.mutable_globals, &instance_wrapper);

			Strategy::FastInstanceReuse {
				instance_wrapper: Rc::new(instance_wrapper),
				globals_snapshot,
				data_segments_snapshot: snapshot_data.data_segments_snapshot.clone(),
				heap_base,
			}
		} else {
			Strategy::RecreateInstance(InstanceCreator {
				imports: Arc::new(imports),
				module: self.module.clone(),
				store,
				heap_pages: self.config.heap_pages,
			})
		};

		Ok(Box::new(WasmtimeInstance { strategy }))
	}
}

/// A `WasmInstance` implementation that reuses compiled module and spawns instances
/// to execute the compiled code.
pub struct WasmtimeInstance {
	strategy: Strategy,
}

// This is safe because `WasmtimeInstance` does not leak reference to `self.imports`
// and all imports don't reference any anything, other than host functions and memory
unsafe impl Send for WasmtimeInstance {}

impl WasmInstance for WasmtimeInstance {
	fn call(&self, method: InvokeMethod, data: &[u8]) -> Result<Vec<u8>> {
		match &self.strategy {
			Strategy::FastInstanceReuse {
				instance_wrapper,
				globals_snapshot,
				data_segments_snapshot,
				heap_base,
			} => {
				let entrypoint = instance_wrapper.resolve_entrypoint(method)?;

				data_segments_snapshot.apply(|offset, contents| {
					instance_wrapper.write_memory_from(Pointer::new(offset), contents)
				})?;
				globals_snapshot.apply(&**instance_wrapper);
				let allocator = FreeingBumpHeapAllocator::new(*heap_base);

				perform_call(data, Rc::clone(&instance_wrapper), entrypoint, allocator)
			}
			Strategy::RecreateInstance(instance_creator) => {
				let instance_wrapper = instance_creator.instantiate()?;
				let heap_base = instance_wrapper.extract_heap_base()?;
				let entrypoint = instance_wrapper.resolve_entrypoint(method)?;

				let allocator = FreeingBumpHeapAllocator::new(heap_base);
				perform_call(data, Rc::new(instance_wrapper), entrypoint, allocator)
			}
		}
	}

	fn get_global_const(&self, name: &str) -> Result<Option<Value>> {
		match &self.strategy {
			Strategy::FastInstanceReuse {
				instance_wrapper, ..
			} => instance_wrapper.get_global_val(name),
			Strategy::RecreateInstance(instance_creator) => {
				instance_creator.instantiate()?.get_global_val(name)
			}
		}
	}
}

/// Prepare a directory structure and a config file to enable wasmtime caching.
///
/// In case of an error the caching will not be enabled.
fn setup_wasmtime_caching(
	cache_path: &Path,
	config: &mut wasmtime::Config,
) -> std::result::Result<(), String> {
	use std::fs;

	let wasmtime_cache_root = cache_path.join("wasmtime");
	fs::create_dir_all(&wasmtime_cache_root)
		.map_err(|err| format!("cannot create the dirs to cache: {:?}", err))?;

	// Canonicalize the path after creating the directories.
	let wasmtime_cache_root = wasmtime_cache_root
		.canonicalize()
		.map_err(|err| format!("failed to canonicalize the path: {:?}", err))?;

	// Write the cache config file
	let cache_config_path = wasmtime_cache_root.join("cache-config.toml");
	let config_content = format!(
		"\
[cache]
enabled = true
directory = \"{cache_dir}\"
",
		cache_dir = wasmtime_cache_root.display()
	);
	fs::write(&cache_config_path, config_content)
		.map_err(|err| format!("cannot write the cache config: {:?}", err))?;

	config
		.cache_config_load(cache_config_path)
		.map_err(|err| format!("failed to parse the config: {:?}", err))?;

	Ok(())
}

fn common_config() -> wasmtime::Config {
	let mut config = wasmtime::Config::new();
	config.cranelift_opt_level(wasmtime::OptLevel::SpeedAndSize);
	config
}

pub struct Semantics {
	/// Enabling this will lead to some optimization shenanigans that make calling [`WasmInstance`]
	/// extermely fast.
	///
	/// Primarily this is achieved by not recreating the instance for each call and performing a
	/// bare minimum clean up: reapplying the data segments and restoring the values for global
	/// variables. The vast majority of the linear memory is not restored, meaning that effects
	/// of previous executions on the same [`WasmInstance`] can be observed there.
	///
	/// This is not a problem for a standard substrate runtime execution because it's up to the
	/// runtime itself to make sure that it doesn't involve any non-determinism.
	///
	/// Since this feature depends on instrumentation, it can be set only if [`CodeSupplyMode::Verbatim`]
	/// is used.
	pub fast_instance_reuse: bool,

	/// The WebAssembly standard defines a call/value stack but it doesn't say anything about its
	/// size except that it has to be finite. The implementations are free to choose their own notion
	/// of limit: some may count the number of calls or values, others would rely on the host machine
	/// stack and trap on reaching a guard page.
	///
	/// This obviously is a source of non-determinism during execution. This feature can be used
	/// to instrument the code so that it will count the depth of execution in some deterministic
	/// way (the machine stack limit should be so high that the deterministic limit always triggers
	/// first).
	///
	/// See [here][stack_height] for more details of the instrumentation
	///
	/// Since this feature depends on instrumentation, it can be set only if [`CodeSupplyMode::Verbatim`]
	/// is used.
	///
	/// [stack_height]: https://github.com/paritytech/wasm-utils/blob/d9432baf/src/stack_height/mod.rs#L1-L50
	pub stack_depth_metering: bool,
	// Other things like nan canonicalization can be added here.
}

pub struct Config {
	/// The number of wasm pages to be mounted after instantiation.
	pub heap_pages: u32,

	/// The WebAssembly standard requires all imports of an instantiated module to be resolved,
	/// othewise, the instantiation fails. If this option is set to `true`, then this behavior is
	/// overriden and imports that are requested by the module and not provided by the host functions
	/// will be resolved using stubs. These stubs will trap upon a call.
	pub allow_missing_func_imports: bool,

	/// A directory in which wasmtime can store its compiled artifacts cache.
	pub cache_path: Option<PathBuf>,

	/// Tuning of various semantics of the wasmtime executor.
	pub semantics: Semantics,
}

enum CodeSupplyMode<'a> {
	/// The runtime is instantiated using the given runtime blob.
	Verbatim {
		// Rationale to take the `RuntimeBlob` here is so that the client will be able to reuse
		// the blob e.g. if they did a prevalidation. If they didn't they can pass a `RuntimeBlob`
		// instance and it will be used anyway in most cases, because we are going to do at least
		// some instrumentations for both anticipated paths: substrate execution and PVF execution.
		//
		// Should there raise a need in performing no instrumentation and the client doesn't need
		// to do any checks, then we can provide a `Cow` like semantics here: if we need the blob and
		//  the user got `RuntimeBlob` then extract it, or otherwise create it from the given
		// bytecode.
		blob: RuntimeBlob,
	},

	/// The code is supplied in a form of a compiled artifact.
	///
	/// This assumes that the code is already prepared for execution and the same `Config` was used.
	Artifact { compiled_artifact: &'a [u8] },
}

/// Create a new `WasmtimeRuntime` given the code. This function performs translation from Wasm to
/// machine code, which can be computationally heavy.
pub fn create_runtime(
	blob: RuntimeBlob,
	config: Config,
	host_functions: Vec<&'static dyn Function>,
) -> std::result::Result<WasmtimeRuntime, WasmError> {
	// SAFETY: this is safe because it doesn't use `CodeSupplyMode::Artifact`.
	unsafe { do_create_runtime(CodeSupplyMode::Verbatim { blob }, config, host_functions) }
}

/// The same as [`create_runtime`] but takes a precompiled artifact, which makes this function
/// considerably faster than [`create_runtime`].
///
/// # Safety
///
/// The caller must ensure that the compiled artifact passed here was produced by [`prepare_runtime_artifact`].
/// Otherwise, there is a risk of arbitrary code execution with all implications.
///
/// It is ok though if the `compiled_artifact` was created by code of another version or with different
/// configuration flags. In such case the caller will receive an `Err` deterministically.
pub unsafe fn create_runtime_from_artifact(
	compiled_artifact: &[u8],
	config: Config,
	host_functions: Vec<&'static dyn Function>,
) -> std::result::Result<WasmtimeRuntime, WasmError> {
	do_create_runtime(
		CodeSupplyMode::Artifact { compiled_artifact },
		config,
		host_functions,
	)
}

/// # Safety
///
/// This is only unsafe if called with [`CodeSupplyMode::Artifact`]. See [`create_runtime_from_artifact`]
/// to get more details.
unsafe fn do_create_runtime(
	code_supply_mode: CodeSupplyMode<'_>,
	config: Config,
	host_functions: Vec<&'static dyn Function>,
) -> std::result::Result<WasmtimeRuntime, WasmError> {
	// Create the engine, store and finally the module from the given code.
	let mut wasmtime_config = common_config();
	if let Some(ref cache_path) = config.cache_path {
		if let Err(reason) = setup_wasmtime_caching(cache_path, &mut wasmtime_config) {
			log::warn!(
				"failed to setup wasmtime cache. Performance may degrade significantly: {}.",
				reason,
			);
		}
	}

	let engine = Engine::new(&wasmtime_config)
		.map_err(|e| WasmError::Other(format!("cannot create the engine for runtime: {}", e)))?;

	let (module, snapshot_data) = match code_supply_mode {
		CodeSupplyMode::Verbatim { mut blob } => {
			instrument(&mut blob, &config.semantics);

			if config.semantics.fast_instance_reuse {
				let data_segments_snapshot = DataSegmentsSnapshot::take(&blob).map_err(|e| {
					WasmError::Other(format!("cannot take data segments snapshot: {}", e))
				})?;
				let data_segments_snapshot = Arc::new(data_segments_snapshot);

				let mutable_globals = ExposedMutableGlobalsSet::collect(&blob);

				let module = wasmtime::Module::new(&engine, &blob.serialize())
					.map_err(|e| WasmError::Other(format!("cannot create module: {}", e)))?;

				(module, Some(InstanceSnapshotData {
					data_segments_snapshot,
					mutable_globals,
				}))
			} else {
				let module = wasmtime::Module::new(&engine, &blob.serialize())
					.map_err(|e| WasmError::Other(format!("cannot create module: {}", e)))?;
				(module, None)
			}
		}
		CodeSupplyMode::Artifact { compiled_artifact } => {
			// SAFETY: The unsafity of `deserialize` is covered by this function. The
			//         responsibilities to maintain the invariants are passed to the caller.
			let module = wasmtime::Module::deserialize(&engine, compiled_artifact)
				.map_err(|e| WasmError::Other(format!("cannot deserialize module: {}", e)))?;

			(module, None)
		}
	};

	Ok(WasmtimeRuntime {
		module: Arc::new(module),
		snapshot_data,
		config,
		host_functions,
		engine,
	})
}

fn instrument(blob: &mut RuntimeBlob, semantics: &Semantics) {
	if semantics.fast_instance_reuse {
		blob.expose_mutable_globals();
	}

	if semantics.stack_depth_metering {
		// TODO: implement deterministic stack metering https://github.com/paritytech/substrate/issues/8393
	}
}

/// Takes a [`RuntimeBlob`] and precompiles it returning the serialized result of compilation. It
/// can then be used for calling [`create_runtime`] avoiding long compilation times.
pub fn prepare_runtime_artifact(
	mut blob: RuntimeBlob,
	semantics: &Semantics,
) -> std::result::Result<Vec<u8>, WasmError> {
	instrument(&mut blob, semantics);

	let engine = Engine::new(&common_config())
		.map_err(|e| WasmError::Other(format!("cannot create the engine: {}", e)))?;

	engine
		.precompile_module(&blob.serialize())
		.map_err(|e| WasmError::Other(format!("cannot precompile module: {}", e)))
}

fn perform_call(
	data: &[u8],
	instance_wrapper: Rc<InstanceWrapper>,
	entrypoint: EntryPoint,
	mut allocator: FreeingBumpHeapAllocator,
) -> Result<Vec<u8>> {
	let (data_ptr, data_len) = inject_input_data(&instance_wrapper, &mut allocator, data)?;

	let host_state = HostState::new(allocator, instance_wrapper.clone());
	let ret = state_holder::with_initialized_state(&host_state, || -> Result<_> {
		Ok(unpack_ptr_and_len(entrypoint.call(data_ptr, data_len)?))
	});
	let (output_ptr, output_len) = ret?;
	let output = extract_output_data(&instance_wrapper, output_ptr, output_len)?;

	Ok(output)
}

fn inject_input_data(
	instance: &InstanceWrapper,
	allocator: &mut FreeingBumpHeapAllocator,
	data: &[u8],
) -> Result<(Pointer<u8>, WordSize)> {
	let data_len = data.len() as WordSize;
	let data_ptr = instance.allocate(allocator, data_len)?;
	instance.write_memory_from(data_ptr, data)?;
	Ok((data_ptr, data_len))
}

fn extract_output_data(
	instance: &InstanceWrapper,
	output_ptr: u32,
	output_len: u32,
) -> Result<Vec<u8>> {
	let mut output = vec![0; output_len as usize];
	instance.read_memory_into(Pointer::new(output_ptr), &mut output)?;
	Ok(output)
}
