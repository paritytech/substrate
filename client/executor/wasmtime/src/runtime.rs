// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

use crate::{
	host::HostState,
	instance_wrapper::{EntryPoint, InstanceWrapper},
	util,
};
use core::marker::PhantomData;

use sc_allocator::FreeingBumpHeapAllocator;
use sc_executor_common::{
	error::{Result, WasmError},
	runtime_blob::{
		self, DataSegmentsSnapshot, ExposedMutableGlobalsSet, GlobalsSnapshot, RuntimeBlob,
	},
	wasm_runtime::{InvokeMethod, WasmInstance, WasmModule},
};
use sp_runtime_interface::unpack_ptr_and_len;
use sp_wasm_interface::{HostFunctions, Pointer, Value, WordSize};
use std::{
	path::{Path, PathBuf},
	sync::{
		atomic::{AtomicBool, Ordering},
		Arc,
	},
};
use wasmtime::{Engine, Memory, StoreLimits, Table};

pub(crate) struct StoreData {
	/// The limits we apply to the store. We need to store it here to return a reference to this
	/// object when we have the limits enabled.
	pub(crate) limits: StoreLimits,
	/// This will only be set when we call into the runtime.
	pub(crate) host_state: Option<HostState>,
	/// This will be always set once the store is initialized.
	pub(crate) memory: Option<Memory>,
	/// This will be set only if the runtime actually contains a table.
	pub(crate) table: Option<Table>,
}

impl StoreData {
	/// Returns a reference to the host state.
	pub fn host_state(&self) -> Option<&HostState> {
		self.host_state.as_ref()
	}

	/// Returns a mutable reference to the host state.
	pub fn host_state_mut(&mut self) -> Option<&mut HostState> {
		self.host_state.as_mut()
	}

	/// Returns the host memory.
	pub fn memory(&self) -> Memory {
		self.memory.expect("memory is always set; qed")
	}

	/// Returns the host table.
	pub fn table(&self) -> Option<Table> {
		self.table
	}
}

pub(crate) type Store = wasmtime::Store<StoreData>;

enum Strategy<H> {
	FastInstanceReuse {
		instance_wrapper: InstanceWrapper,
		globals_snapshot: GlobalsSnapshot<wasmtime::Global>,
		data_segments_snapshot: Arc<DataSegmentsSnapshot>,
		heap_base: u32,
	},
	RecreateInstance(InstanceCreator<H>),
}

struct InstanceCreator<H> {
	module: Arc<wasmtime::Module>,
	heap_pages: u64,
	allow_missing_func_imports: bool,
	max_memory_size: Option<usize>,
	phantom: PhantomData<H>,
}

impl<H> InstanceCreator<H>
where
	H: HostFunctions,
{
	fn instantiate(&mut self) -> Result<InstanceWrapper> {
		InstanceWrapper::new::<H>(
			&*self.module,
			self.heap_pages,
			self.allow_missing_func_imports,
			self.max_memory_size,
		)
	}
}

struct InstanceGlobals<'a> {
	instance: &'a mut InstanceWrapper,
}

impl<'a> runtime_blob::InstanceGlobals for InstanceGlobals<'a> {
	type Global = wasmtime::Global;

	fn get_global(&mut self, export_name: &str) -> Self::Global {
		self.instance
			.get_global(export_name)
			.expect("get_global is guaranteed to be called with an export name of a global; qed")
	}

	fn get_global_value(&mut self, global: &Self::Global) -> Value {
		util::from_wasmtime_val(global.get(&mut self.instance.store_mut()))
	}

	fn set_global_value(&mut self, global: &Self::Global, value: Value) {
		global.set(&mut self.instance.store_mut(), util::into_wasmtime_val(value)).expect(
			"the value is guaranteed to be of the same value; the global is guaranteed to be mutable; qed",
		);
	}
}

/// Data required for creating instances with the fast instance reuse strategy.
struct InstanceSnapshotData {
	mutable_globals: ExposedMutableGlobalsSet,
	data_segments_snapshot: Arc<DataSegmentsSnapshot>,
}

/// A `WasmModule` implementation using wasmtime to compile the runtime module to machine code
/// and execute the compiled code.
pub struct WasmtimeRuntime<H> {
	module: Arc<wasmtime::Module>,
	snapshot_data: Option<InstanceSnapshotData>,
	config: Config,
	phantom: PhantomData<H>,
}

impl<H> WasmModule for WasmtimeRuntime<H>
where
	H: HostFunctions,
{
	fn new_instance(&self) -> Result<Box<dyn WasmInstance>> {
		let strategy = if let Some(ref snapshot_data) = self.snapshot_data {
			let mut instance_wrapper = InstanceWrapper::new::<H>(
				&self.module,
				self.config.heap_pages,
				self.config.allow_missing_func_imports,
				self.config.max_memory_size,
			)?;
			let heap_base = instance_wrapper.extract_heap_base()?;

			// This function panics if the instance was created from a runtime blob different from
			// which the mutable globals were collected. Here, it is easy to see that there is only
			// a single runtime blob and thus it's the same that was used for both creating the
			// instance and collecting the mutable globals.
			let globals_snapshot = GlobalsSnapshot::take(
				&snapshot_data.mutable_globals,
				&mut InstanceGlobals { instance: &mut instance_wrapper },
			);

			Strategy::<H>::FastInstanceReuse {
				instance_wrapper,
				globals_snapshot,
				data_segments_snapshot: snapshot_data.data_segments_snapshot.clone(),
				heap_base,
			}
		} else {
			Strategy::<H>::RecreateInstance(InstanceCreator {
				module: self.module.clone(),
				heap_pages: self.config.heap_pages,
				allow_missing_func_imports: self.config.allow_missing_func_imports,
				max_memory_size: self.config.max_memory_size,
				phantom: PhantomData,
			})
		};

		Ok(Box::new(WasmtimeInstance { strategy }))
	}
}

/// A `WasmInstance` implementation that reuses compiled module and spawns instances
/// to execute the compiled code.
pub struct WasmtimeInstance<H> {
	strategy: Strategy<H>,
}

impl<H> WasmInstance for WasmtimeInstance<H>
where
	H: HostFunctions,
{
	fn call(&mut self, method: InvokeMethod, data: &[u8]) -> Result<Vec<u8>> {
		match &mut self.strategy {
			Strategy::FastInstanceReuse {
				ref mut instance_wrapper,
				globals_snapshot,
				data_segments_snapshot,
				heap_base,
			} => {
				let entrypoint = instance_wrapper.resolve_entrypoint(method)?;

				data_segments_snapshot.apply(|offset, contents| {
					util::write_memory_from(
						instance_wrapper.store_mut(),
						Pointer::new(offset),
						contents,
					)
				})?;
				globals_snapshot.apply(&mut InstanceGlobals { instance: instance_wrapper });
				let allocator = FreeingBumpHeapAllocator::new(*heap_base);

				let result = perform_call(data, instance_wrapper, entrypoint, allocator);

				// Signal to the OS that we are done with the linear memory and that it can be
				// reclaimed.
				instance_wrapper.decommit();

				result
			},
			Strategy::RecreateInstance(ref mut instance_creator) => {
				let mut instance_wrapper = instance_creator.instantiate()?;
				let heap_base = instance_wrapper.extract_heap_base()?;
				let entrypoint = instance_wrapper.resolve_entrypoint(method)?;

				let allocator = FreeingBumpHeapAllocator::new(heap_base);
				perform_call(data, &mut instance_wrapper, entrypoint, allocator)
			},
		}
	}

	fn get_global_const(&mut self, name: &str) -> Result<Option<Value>> {
		match &mut self.strategy {
			Strategy::FastInstanceReuse { instance_wrapper, .. } =>
				instance_wrapper.get_global_val(name),
			Strategy::RecreateInstance(ref mut instance_creator) =>
				instance_creator.instantiate()?.get_global_val(name),
		}
	}

	fn linear_memory_base_ptr(&self) -> Option<*const u8> {
		match &self.strategy {
			Strategy::RecreateInstance(_) => {
				// We do not keep the wasm instance around, therefore there is no linear memory
				// associated with it.
				None
			},
			Strategy::FastInstanceReuse { instance_wrapper, .. } =>
				Some(instance_wrapper.base_ptr()),
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

fn common_config(semantics: &Semantics) -> std::result::Result<wasmtime::Config, WasmError> {
	let mut config = wasmtime::Config::new();
	config.cranelift_opt_level(wasmtime::OptLevel::SpeedAndSize);
	config.cranelift_nan_canonicalization(semantics.canonicalize_nans);

	let profiler = match std::env::var_os("WASMTIME_PROFILING_STRATEGY") {
		Some(os_string) if os_string == "jitdump" => wasmtime::ProfilingStrategy::JitDump,
		None => wasmtime::ProfilingStrategy::None,
		Some(_) => {
			// Remember if we have already logged a warning due to an unknown profiling strategy.
			static UNKNOWN_PROFILING_STRATEGY: AtomicBool = AtomicBool::new(false);
			// Make sure that the warning will not be relogged regularly.
			if !UNKNOWN_PROFILING_STRATEGY.swap(true, Ordering::Relaxed) {
				log::warn!("WASMTIME_PROFILING_STRATEGY is set to unknown value, ignored.");
			}
			wasmtime::ProfilingStrategy::None
		},
	};
	config
		.profiler(profiler)
		.map_err(|e| WasmError::Instantiation(format!("fail to set profiler: {}", e)))?;

	if let Some(DeterministicStackLimit { native_stack_max, .. }) =
		semantics.deterministic_stack_limit
	{
		config
			.max_wasm_stack(native_stack_max as usize)
			.map_err(|e| WasmError::Other(format!("cannot set max wasm stack: {}", e)))?;
	}

	config.parallel_compilation(semantics.parallel_compilation);

	// Be clear and specific about the extensions we support. If an update brings new features
	// they should be introduced here as well.
	config.wasm_reference_types(false);
	config.wasm_simd(false);
	config.wasm_bulk_memory(false);
	config.wasm_multi_value(false);
	config.wasm_multi_memory(false);
	config.wasm_module_linking(false);
	config.wasm_threads(false);

	Ok(config)
}

/// Knobs for deterministic stack height limiting.
///
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
/// The deterministic stack height limiting feature allows to instrument the code so that it will
/// count the number of items that may be on the stack. This counting will only act as an rough
/// estimate of the actual stack limit in wasmtime. This is because wasmtime measures it's stack
/// usage in bytes.
///
/// The actual number of bytes consumed by a function is not trivial to compute  without going
/// through full compilation. Therefore, it's expected that `native_stack_max` is greatly
/// overestimated and thus never reached in practice. The stack overflow check introduced by the
/// instrumentation and that relies on the logical item count should be reached first.
///
/// See [here][stack_height] for more details of the instrumentation
///
/// [stack_height]: https://github.com/paritytech/wasm-utils/blob/d9432baf/src/stack_height/mod.rs#L1-L50
pub struct DeterministicStackLimit {
	/// A number of logical "values" that can be pushed on the wasm stack. A trap will be triggered
	/// if exceeded.
	///
	/// A logical value is a local, an argument or a value pushed on operand stack.
	pub logical_max: u32,
	/// The maximum number of bytes for stack used by wasmtime JITed code.
	///
	/// It's not specified how much bytes will be consumed by a stack frame for a given wasm
	/// function after translation into machine code. It is also not quite trivial.
	///
	/// Therefore, this number should be chosen conservatively. It must be so large so that it can
	/// fit the [`logical_max`](Self::logical_max) logical values on the stack, according to the
	/// current instrumentation algorithm.
	///
	/// This value cannot be 0.
	pub native_stack_max: u32,
}

pub struct Semantics {
	/// Enabling this will lead to some optimization shenanigans that make calling [`WasmInstance`]
	/// extremely fast.
	///
	/// Primarily this is achieved by not recreating the instance for each call and performing a
	/// bare minimum clean up: reapplying the data segments and restoring the values for global
	/// variables.
	///
	/// Since this feature depends on instrumentation, it can be set only if runtime is
	/// instantiated using the runtime blob, e.g. using [`create_runtime`].
	// I.e. if [`CodeSupplyMode::Verbatim`] is used.
	pub fast_instance_reuse: bool,

	/// Specifiying `Some` will enable deterministic stack height. That is, all executor
	/// invocations will reach stack overflow at the exactly same point across different wasmtime
	/// versions and architectures.
	///
	/// This is achieved by a combination of running an instrumentation pass on input code and
	/// configuring wasmtime accordingly.
	///
	/// Since this feature depends on instrumentation, it can be set only if runtime is
	/// instantiated using the runtime blob, e.g. using [`create_runtime`].
	// I.e. if [`CodeSupplyMode::Verbatim`] is used.
	pub deterministic_stack_limit: Option<DeterministicStackLimit>,

	/// Controls whether wasmtime should compile floating point in a way that doesn't allow for
	/// non-determinism.
	///
	/// By default, the wasm spec allows some local non-determinism wrt. certain floating point
	/// operations. Specifically, those operations that are not defined to operate on bits (e.g.
	/// fneg) can produce NaN values. The exact bit pattern for those is not specified and may
	/// depend on the particular machine that executes wasmtime generated JITed machine code. That
	/// is a source of non-deterministic values.
	///
	/// The classical runtime environment for Substrate allowed it and punted this on the runtime
	/// developers. For PVFs, we want to ensure that execution is deterministic though. Therefore,
	/// for PVF execution this flag is meant to be turned on.
	pub canonicalize_nans: bool,

	/// Configures wasmtime to use multiple threads for compiling.
	pub parallel_compilation: bool,
}

pub struct Config {
	/// The number of wasm pages to be mounted after instantiation.
	pub heap_pages: u64,

	/// The total amount of memory in bytes an instance can request.
	///
	/// If specified, the runtime will be able to allocate only that much of wasm memory.
	/// This is the total number and therefore the [`Config::heap_pages`] is accounted for.
	///
	/// That means that the initial number of pages of a linear memory plus the
	/// [`Config::heap_pages`] multiplied by the wasm page size (64KiB) should be less than or
	/// equal to `max_memory_size`, otherwise the instance won't be created.
	///
	/// Moreover, `memory.grow` will fail (return -1) if the sum of sizes of currently mounted
	/// and additional pages exceeds `max_memory_size`.
	///
	/// The default is `None`.
	pub max_memory_size: Option<usize>,

	/// The WebAssembly standard requires all imports of an instantiated module to be resolved,
	/// otherwise, the instantiation fails. If this option is set to `true`, then this behavior is
	/// overriden and imports that are requested by the module and not provided by the host
	/// functions will be resolved using stubs. These stubs will trap upon a call.
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
		// to do any checks, then we can provide a `Cow` like semantics here: if we need the blob
		// and  the user got `RuntimeBlob` then extract it, or otherwise create it from the given
		// bytecode.
		blob: RuntimeBlob,
	},

	/// The code is supplied in a form of a compiled artifact.
	///
	/// This assumes that the code is already prepared for execution and the same `Config` was
	/// used.
	Artifact { compiled_artifact: &'a [u8] },
}

/// Create a new `WasmtimeRuntime` given the code. This function performs translation from Wasm to
/// machine code, which can be computationally heavy.
///
/// The `H` generic parameter is used to statically pass a set of host functions which are exposed
/// to the runtime.
pub fn create_runtime<H>(
	blob: RuntimeBlob,
	config: Config,
) -> std::result::Result<WasmtimeRuntime<H>, WasmError>
where
	H: HostFunctions,
{
	// SAFETY: this is safe because it doesn't use `CodeSupplyMode::Artifact`.
	unsafe { do_create_runtime::<H>(CodeSupplyMode::Verbatim { blob }, config) }
}

/// The same as [`create_runtime`] but takes a precompiled artifact, which makes this function
/// considerably faster than [`create_runtime`].
///
/// # Safety
///
/// The caller must ensure that the compiled artifact passed here was produced by
/// [`prepare_runtime_artifact`]. Otherwise, there is a risk of arbitrary code execution with all
/// implications.
///
/// It is ok though if the `compiled_artifact` was created by code of another version or with
/// different configuration flags. In such case the caller will receive an `Err` deterministically.
pub unsafe fn create_runtime_from_artifact<H>(
	compiled_artifact: &[u8],
	config: Config,
) -> std::result::Result<WasmtimeRuntime<H>, WasmError>
where
	H: HostFunctions,
{
	do_create_runtime::<H>(CodeSupplyMode::Artifact { compiled_artifact }, config)
}

/// # Safety
///
/// This is only unsafe if called with [`CodeSupplyMode::Artifact`]. See
/// [`create_runtime_from_artifact`] to get more details.
unsafe fn do_create_runtime<H>(
	code_supply_mode: CodeSupplyMode<'_>,
	config: Config,
) -> std::result::Result<WasmtimeRuntime<H>, WasmError>
where
	H: HostFunctions,
{
	// Create the engine, store and finally the module from the given code.
	let mut wasmtime_config = common_config(&config.semantics)?;
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
		CodeSupplyMode::Verbatim { blob } => {
			let blob = instrument(blob, &config.semantics)?;

			if config.semantics.fast_instance_reuse {
				let data_segments_snapshot = DataSegmentsSnapshot::take(&blob).map_err(|e| {
					WasmError::Other(format!("cannot take data segments snapshot: {}", e))
				})?;
				let data_segments_snapshot = Arc::new(data_segments_snapshot);

				let mutable_globals = ExposedMutableGlobalsSet::collect(&blob);

				let module = wasmtime::Module::new(&engine, &blob.serialize())
					.map_err(|e| WasmError::Other(format!("cannot create module: {}", e)))?;

				(module, Some(InstanceSnapshotData { data_segments_snapshot, mutable_globals }))
			} else {
				let module = wasmtime::Module::new(&engine, &blob.serialize())
					.map_err(|e| WasmError::Other(format!("cannot create module: {}", e)))?;
				(module, None)
			}
		},
		CodeSupplyMode::Artifact { compiled_artifact } => {
			// SAFETY: The unsafity of `deserialize` is covered by this function. The
			//         responsibilities to maintain the invariants are passed to the caller.
			let module = wasmtime::Module::deserialize(&engine, compiled_artifact)
				.map_err(|e| WasmError::Other(format!("cannot deserialize module: {}", e)))?;

			(module, None)
		},
	};

	Ok(WasmtimeRuntime { module: Arc::new(module), snapshot_data, config, phantom: PhantomData })
}

fn instrument(
	mut blob: RuntimeBlob,
	semantics: &Semantics,
) -> std::result::Result<RuntimeBlob, WasmError> {
	if let Some(DeterministicStackLimit { logical_max, .. }) = semantics.deterministic_stack_limit {
		blob = blob.inject_stack_depth_metering(logical_max)?;
	}

	// If enabled, this should happen after all other passes that may introduce global variables.
	if semantics.fast_instance_reuse {
		blob.expose_mutable_globals();
	}

	Ok(blob)
}

/// Takes a [`RuntimeBlob`] and precompiles it returning the serialized result of compilation. It
/// can then be used for calling [`create_runtime`] avoiding long compilation times.
pub fn prepare_runtime_artifact(
	blob: RuntimeBlob,
	semantics: &Semantics,
) -> std::result::Result<Vec<u8>, WasmError> {
	let blob = instrument(blob, semantics)?;

	let engine = Engine::new(&common_config(semantics)?)
		.map_err(|e| WasmError::Other(format!("cannot create the engine: {}", e)))?;

	engine
		.precompile_module(&blob.serialize())
		.map_err(|e| WasmError::Other(format!("cannot precompile module: {}", e)))
}

fn perform_call(
	data: &[u8],
	instance_wrapper: &mut InstanceWrapper,
	entrypoint: EntryPoint,
	mut allocator: FreeingBumpHeapAllocator,
) -> Result<Vec<u8>> {
	let (data_ptr, data_len) = inject_input_data(instance_wrapper, &mut allocator, data)?;

	let host_state = HostState::new(allocator);

	// Set the host state before calling into wasm.
	instance_wrapper.store_mut().data_mut().host_state = Some(host_state);

	let ret = entrypoint
		.call(instance_wrapper.store_mut(), data_ptr, data_len)
		.map(unpack_ptr_and_len);

	// Reset the host state
	instance_wrapper.store_mut().data_mut().host_state = None;

	let (output_ptr, output_len) = ret?;
	let output = extract_output_data(instance_wrapper, output_ptr, output_len)?;

	Ok(output)
}

fn inject_input_data(
	instance: &mut InstanceWrapper,
	allocator: &mut FreeingBumpHeapAllocator,
	data: &[u8],
) -> Result<(Pointer<u8>, WordSize)> {
	let mut ctx = instance.store_mut();
	let memory = ctx.data().memory();
	let memory = memory.data_mut(&mut ctx);
	let data_len = data.len() as WordSize;
	let data_ptr = allocator.allocate(memory, data_len)?;
	util::write_memory_from(instance.store_mut(), data_ptr, data)?;
	Ok((data_ptr, data_len))
}

fn extract_output_data(
	instance: &InstanceWrapper,
	output_ptr: u32,
	output_len: u32,
) -> Result<Vec<u8>> {
	let mut output = vec![0; output_len as usize];
	util::read_memory_into(instance.store(), Pointer::new(output_ptr), &mut output)?;
	Ok(output)
}
