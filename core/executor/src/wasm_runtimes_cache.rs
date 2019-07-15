// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Implements a cache for pre-created Wasm runtime module instances.

use crate::error::Error;
use crate::wasm_executor::WasmExecutor;
use log::{trace, warn};
use parity_codec::Decode;
use parity_wasm::elements::{deserialize_buffer, DataSegment, Instruction, Module as RawModule};
use primitives::storage::well_known_keys;
use primitives::Blake2Hasher;
use runtime_version::RuntimeVersion;
use state_machine::Externalities;
use std::collections::hash_map::{Entry, HashMap};
use std::mem;
use std::rc::Rc;
use std::fs::{File, OpenOptions};
use std::io::{Write, Seek, SeekFrom};
use std::os::unix::io::AsRawFd;
use std::ptr;
use std::iter;
use std::slice;
use tempdir::TempDir;
use wasmi::{Module as WasmModule, ModuleRef as WasmModuleInstanceRef, RuntimeValue, MemoryBackend, ByteBuf};

#[derive(Debug)]
enum CacheError {
	CodeNotFound,
	ApplySnapshotFailed,
	InvalidModule,
	CantDeserializeWasm,
	Instantiation,
}

/// A runtime along with its version and initial state snapshot.
pub struct CachedRuntime {
	/// A wasm module instance.
	instance: WasmModuleInstanceRef,
	/// Runtime version according to `Core_version`.
	///
	/// Can be `None` if the runtime doesn't expose this function.
	version: Option<RuntimeVersion>,
	/// The snapshot of the instance's state taken just after the instantiation.
	state_snapshot: StateSnapshot,
}

impl CachedRuntime {
	/// Perform an operation with the clean version of the runtime wasm instance.
	pub fn with<R, F>(&self, f: F) -> R
	where
		F: FnOnce(&WasmModuleInstanceRef) -> R,
	{
		self.state_snapshot.apply(&self.instance).expect(
			"applying the snapshot can only fail if the passed instance is different
			from the one that was used for creation of the snapshot;
			we use the snapshot that is directly associated with the instance;
			thus the snapshot was created using the instance;
			qed",
		);
		let mem_instance = WasmExecutor::get_mem_instance(&self.instance).unwrap();
		let slave = self.state_snapshot.mem.slave_memory();

		unsafe {
			mem_instance.set_backend(Box::new(slave));
		}

		f(&self.instance)
	}

	/// Returns the version of this cached runtime.
	///
	/// Returns `None` if the runtime doesn't provide the information or there was an error
	/// while fetching it.
	pub fn version(&self) -> Option<RuntimeVersion> {
		self.version.clone()
	}
}

struct MmapLinearMemory {
	/// A temporary directory that has the file with the wasm runtime heap.
	///
	/// We need to retain it for the lifetime of the heap.
	temp_dir: TempDir,
	/// The file that will be used for mapping the linear memory.
	memory_file: File,
	len: usize,
}

impl MmapLinearMemory {
	fn create(len: usize) -> Self {
		let temp_dir = TempDir::new("substrate_heap").unwrap();
		let path = dbg!(temp_dir.path().join("heap"));

		let mut f = OpenOptions::new()
			.read(true)
			.create(true)
			.write(true)
			.truncate(true)
			.open(path)
			.unwrap(); // TODO:

		unsafe {
			libc::ftruncate(f.as_raw_fd(), len as i64);
		}

		Self {
			temp_dir,
			memory_file: f,
			len,
		}
	}

	fn set(&mut self, offset: usize, contents: &[u8]) {
		self.memory_file.seek(SeekFrom::Start(offset as u64)).unwrap();
		self.memory_file.write_all(contents).unwrap();
	}

	fn slave_memory(&self) -> SlaveMemory {
		unsafe {
            let ptr = libc::mmap(
                ptr::null_mut(),
                self.len,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE,
                self.memory_file.as_raw_fd(),
                0,
            ) as *mut u8;

            if ptr as isize == -1 {
                panic!();
            }

            SlaveMemory { ptr, len: self.len }
        }
	}
}

struct SlaveMemory {
	ptr: *mut u8,
	len: usize,
}

impl MemoryBackend for SlaveMemory {
	fn alloc(&mut self, initial: usize, _maximum: Option<usize>) -> Result<ByteBuf, &'static str> {
		Ok(ByteBuf {
			ptr: self.ptr,
			len: self.len,
		})
	}
    fn realloc(&mut self, new_len: usize) -> Result<ByteBuf, &'static str> {
		panic!()
	}
    fn erase(&mut self) -> Result<(), &'static str> {
		let data = unsafe {
			slice::from_raw_parts_mut(self.ptr, self.len)
		};
		for v in data {
            *v = 0;
        }
        Ok(())
	}
}

impl Drop for SlaveMemory {
	fn drop(&mut self) {
		let ret_val = unsafe {
            // Safety proof:
            // - `self.ptr` was allocated by a call to `mmap`.
            // - `self.len` was saved at the same time and it doesn't change throughout the lifetime
            //   of `self`.
            libc::munmap(self.ptr as *mut libc::c_void, self.len)
        };
        assert_eq!(ret_val, 0, "munmap failed");
	}
}

/// A state snapshot of an instance taken just after instantiation.
///
/// It is used for restoring the state of the module after execution.
struct StateSnapshot {
	/// The offset and the content of the memory segments that should be used to restore the snapshot
	data_segments: Vec<(u32, Vec<u8>)>,
	/// The list of all global mutable variables of the module in their sequential order.
	global_mut_values: Vec<RuntimeValue>,
	mem: MmapLinearMemory,
	heap_pages: u32,
}

impl StateSnapshot {
	// Returns `None` if instance is not valid.
	fn take(
		module_instance: &WasmModuleInstanceRef,
		mut mem: MmapLinearMemory,
		data_segments: Vec<DataSegment>,
		heap_pages: u32,
	) -> Option<Self> {
		let mut prepared_segments = Vec::with_capacity(data_segments.len());
		for mut segment in data_segments {
			// Just replace contents of the segment since the segments will be discarded later
			// anyway.
			let contents = mem::replace(segment.value_mut(), vec![]);

			let init_expr = segment.offset().code();
			// [op, End]
			if init_expr.len() != 2 {
				return None;
			}
			let offset = match init_expr[0] {
				Instruction::I32Const(v) => v as u32,
				Instruction::GetGlobal(idx) => {
					let global_val = module_instance.globals().get(idx as usize)?.get();
					match global_val {
						RuntimeValue::I32(v) => v as u32,
						_ => return None,
					}
				}
				_ => return None,
			};
			prepared_segments.push((offset, contents))
		}

		for (offset, contents) in &prepared_segments {
			mem.set(*offset as usize, contents);
		}

		// Collect all values of mutable globals.
		let global_mut_values = module_instance
			.globals()
			.iter()
			.filter(|g| g.is_mutable())
			.map(|g| g.get())
			.collect();

		Some(Self {
			data_segments: prepared_segments,
			global_mut_values,
			heap_pages,
			mem,
		})
	}

	/// Reset the runtime instance to the initial version by restoring
	/// the preserved memory and globals.
	///
	/// Returns `Err` if applying the snapshot is failed.
	fn apply(&self, instance: &WasmModuleInstanceRef) -> Result<(), CacheError> {
		// Second, restore the values of mutable globals.
		for (global_ref, global_val) in instance
			.globals()
			.iter()
			.filter(|g| g.is_mutable())
			.zip(self.global_mut_values.iter())
		{
			// the instance should be the same as used for preserving and
			// we iterate the same way it as we do it for preserving values that means that the
			// types should be the same and all the values are mutable. So no error is expected/
			global_ref
				.set(*global_val)
				.map_err(|_| CacheError::ApplySnapshotFailed)?;
		}
		Ok(())
	}
}

/// Default num of pages for the heap
const DEFAULT_HEAP_PAGES: u64 = 1024;

/// Cache for the runtimes.
///
/// When an instance is requested for the first time it is added to this
/// cache. Furthermore its initial memory and values of mutable globals are preserved here. Follow-up
/// requests to fetch a runtime return this one instance with the memory
/// reset to the initial memory. So, one runtime instance is reused for
/// every fetch request.
///
/// For now the cache grows indefinitely, but that should be fine for now since runtimes can only be
/// upgraded rarely and there are no other ways to make the node to execute some other runtime.
pub struct RuntimesCache {
	/// A cache of runtime instances along with metadata, ready to be reused.
	///
	/// Instances are keyed by the hash of their code.
	instances: HashMap<[u8; 32], Result<Rc<CachedRuntime>, CacheError>>,
}

impl RuntimesCache {
	/// Creates a new instance of a runtimes cache.
	pub fn new() -> RuntimesCache {
		RuntimesCache {
			instances: HashMap::new(),
		}
	}

	/// Fetches an instance of the runtime.
	///
	/// On first use we create a new runtime instance, save it to the cache
	/// and persist its initial memory.
	///
	/// Each subsequent request will return this instance, with its memory restored
	/// to the persisted initial memory. Thus, we reuse one single runtime instance
	/// for every `fetch_runtime` invocation.
	///
	/// # Parameters
	///
	/// `wasm_executor`- Rust wasm executor. Executes the provided code in a
	/// sandboxed Wasm runtime.
	///
	/// `ext` - Externalities to use for the runtime. This is used for setting
	/// up an initial runtime instance. The parameter is only needed for calling
	/// into the Wasm module to find out the `Core_version`.
	///
	/// `default_heap_pages` - Number of 64KB pages to allocate for Wasm execution.
	/// Defaults to `DEFAULT_HEAP_PAGES` if `None` is provided.
	///
	/// # Return value
	///
	/// If no error occurred a tuple `(wasmi::ModuleRef, Option<RuntimeVersion>)` is
	/// returned. `RuntimeVersion` is contained if the call to `Core_version` returned
	/// a version.
	///
	/// In case of failure one of two errors can be returned:
	///
	/// `Err::InvalidCode` is returned for runtime code issues.
	///
	/// `Error::InvalidMemoryReference` is returned if no memory export with the
	/// identifier `memory` can be found in the runtime.
	pub fn fetch_runtime<E: Externalities<Blake2Hasher>>(
		&mut self,
		wasm_executor: &WasmExecutor,
		ext: &mut E,
		default_heap_pages: Option<u64>,
	) -> Result<Rc<CachedRuntime>, Error> {
		let code_hash = ext
			.original_storage_hash(well_known_keys::CODE)
			.ok_or(Error::InvalidCode)?;

		// This is direct result from fighting with borrowck.
		let handle_result =
			|cached_result: &Result<Rc<CachedRuntime>, CacheError>| match *cached_result {
				Err(_) => Err(Error::InvalidCode),
				Ok(ref cached_runtime) => Ok(Rc::clone(cached_runtime)),
			};

		match self.instances.entry(code_hash.into()) {
			Entry::Occupied(o) => handle_result(o.get()),
			Entry::Vacant(v) => {
				trace!(target: "runtimes_cache", "no instance found in cache, creating now.");
				let result = Self::create_wasm_instance(wasm_executor, ext, default_heap_pages);
				if let Err(ref err) = result {
					warn!(target: "runtimes_cachce", "cannot create a runtime: {:?}", err);
				}
				handle_result(v.insert(result))
			}
		}
	}

	fn create_wasm_instance<E: Externalities<Blake2Hasher>>(
		wasm_executor: &WasmExecutor,
		ext: &mut E,
		default_heap_pages: Option<u64>,
	) -> Result<Rc<CachedRuntime>, CacheError> {
		let code = ext
			.original_storage(well_known_keys::CODE)
			.ok_or(CacheError::CodeNotFound)?;
		let module = WasmModule::from_buffer(&code).map_err(|_| CacheError::InvalidModule)?;

		// Extract the data segments from the wasm code.
		//
		// A return of this error actually indicates that there is a problem in logic, since
		// we just loaded and validated the `module` above.
		let data_segments = extract_data_segments(&code).ok_or(CacheError::CantDeserializeWasm)?;

		let heap_pages = ext
			.storage(well_known_keys::HEAP_PAGES)
			.and_then(|pages| u64::decode(&mut &pages[..]))
			.or(default_heap_pages)
			.unwrap_or(DEFAULT_HEAP_PAGES);

		// Instantiate this module.
		let instance = WasmExecutor::instantiate_module::<E>(heap_pages as usize, &module)
			.map_err(|_| CacheError::Instantiation)?;

		let mem_instance = WasmExecutor::get_mem_instance(&instance).unwrap(); // TODO:
		let mmap_linear_memory = MmapLinearMemory::create(mem_instance.current_size().0 * 65536);

		// Take state snapshot before executing anything.
		let state_snapshot = StateSnapshot::take(
			&instance,
			mmap_linear_memory,
			data_segments,
			heap_pages as u32
		)
		.expect(
			"`take` returns `Err` if the module is not valid;
			we already loaded module above, thus the `Module` is proven to be valid at this point;
			qed
			",
		);

		let version = wasm_executor
			.call_in_wasm_module(ext, &instance, "Core_version", &[])
			.ok()
			.and_then(|v| RuntimeVersion::decode(&mut v.as_slice()));
		Ok(Rc::new(CachedRuntime {
			instance,
			version,
			state_snapshot,
		}))
	}
}

/// Extract the data segments from the given wasm code.
///
/// Returns `Err` if the given wasm code cannot be deserialized.
fn extract_data_segments(wasm_code: &[u8]) -> Option<Vec<DataSegment>> {
	let raw_module: RawModule = deserialize_buffer(wasm_code).ok()?;
	let segments = raw_module
		.data_section()
		.map(|ds| ds.entries())
		.unwrap_or(&[])
		.to_vec();
	Some(segments)
}
