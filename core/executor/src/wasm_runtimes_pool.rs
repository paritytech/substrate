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

//! Implements a pool of pre-created runtime module instances.
//!
//! A background thread adds instances back to the pool and ensures
//! a specified capacity is maintained.

use crate::error::{Error, Result};
use crate::wasm_executor::WasmExecutor;
use log::trace;
use parity_codec::Decode;
use parking_lot::RwLock;
use primitives::Blake2Hasher;
use primitives::storage::well_known_keys;
use runtime_version::RuntimeVersion;
use state_machine::Externalities;
use std::{
	sync::Arc, sync::mpsc::{channel, Sender}, thread,
};
use wasmi::{Module as WasmModule, ModuleRef as WasmModuleInstanceRef};

#[derive(Clone)]
enum RuntimePreproc {
	InvalidCode,
	ValidCode(WasmModuleInstanceRef, Option<RuntimeVersion>),
}

/// Default wasm module instances kept in pool.
const INSTANCES_IN_POOL: usize = 40;

/// Add new instances to the pool if less than this are in pool.
const ADD_WHEN_LESS_THAN: usize = 20;

/// Default num of pages for the heap
const DEFAULT_HEAP_PAGES: u64 = 1024;

#[derive(Debug)]
enum Msg {
	Ping,

	#[allow(dead_code)] // it's only used in tests
	Shutdown,
}

#[derive(Debug)]
enum Action {
	Pop,
	Reset,
	Invalid
}

type PoolSender = Sender<Msg>;

/// Pool of runtime instances. When an instance is taken out,
/// the pool is refilled by a background thread.
pub struct RuntimesPool {
	pool: Arc<RwLock<Vec<RuntimePreproc>>>,
	template_instance: Arc<RwLock<Option<RuntimePreproc>>>,
	observer: Arc<RwLock<Option<PoolSender>>>,
	observer_thread: Arc<RwLock<Option<thread::JoinHandle<()>>>>,
}

impl RuntimesPool {
	/// Creates a new instance of a runtime pool.
	pub fn new() -> RuntimesPool {
		RuntimesPool {
			pool: Arc::new(RwLock::new(Vec::new())),
			template_instance: Arc::new(RwLock::new(None)),
			observer: Arc::new(RwLock::new(None)),
			observer_thread: Arc::new(RwLock::new(None)),
		}
	}

	/// Fetch a runtime instance from the pool. If there is no instance yet in pool,
	/// or no pool exists yet initialization happens automatically.
	///
	/// # Parameters
	///
	/// `wasm_executor`- Rust wasm executor. Executes the provided code in a
	/// sandboxed Wasm runtime.
	///
	/// `ext` - Externalities to use for the runtime. This is used for setting
	/// up an initial "template instance", which will be cloned when adding
	/// new instances to the pool. The parameter is only needed to call into
	/// the wasm module to find out the `Core_version`.
	///
	/// `default_heap_pages` - Default number of 64KB pages to allocate for
	/// Wasm execution. Defaults to `DEFAULT_HEAP_PAGES` if `None` is provided.
	///
	/// `maybe_requested_version` - If `Some(RuntimeVersion)` is provided the
	/// instances in the pool will be checked for compatibility. In case of
	/// incompatibility the pool will be reset and new compatible instances
	/// will be spawned.
	///
	/// # Return value
	///
	/// If no error occurred a `RuntimePreproc::ValidCode` is returned, containing
	/// a wasmi `ModuleRef` with an optional `RuntimeVersion` (if the call
	/// `Core_version` returned a version).
	///
	/// In case an error occurred `RuntimePreproc::InvalidCode` is returned with an
	/// appropriate description.
	pub fn fetch_runtime_from_pool<E: Externalities<Blake2Hasher>>(
		&self,
		wasm_executor: &WasmExecutor,
		ext: &mut E,
		default_heap_pages: Option<u64>,
		maybe_requested_version: Option<&RuntimeVersion>,
	) -> Result<(WasmModuleInstanceRef, Option<RuntimeVersion>)> {
		{
			// if there is no template instance yet, build one lazily
			let mut template_instance = self.template_instance.write();
			if let None = *template_instance {
				let template =
					self.create_wasm_instance(wasm_executor, ext, default_heap_pages);
				*template_instance = Some(template);
			}
		}

		let action = match maybe_requested_version {
			None => Action::Pop,
			Some(ref version) => {
				match *self.template_instance.read() {
					None => Action::Pop,
					Some(RuntimePreproc::InvalidCode) => Action::Invalid,
					Some(RuntimePreproc::ValidCode(_, None)) => Action::Reset,
					Some(RuntimePreproc::ValidCode(_, Some(ref template_version))) => {
						if template_version.can_call_with(&version) {
							Action::Pop
						} else {
							trace!(target: "runtimes_pool",
								   "resetting pool because new version received");
							Action::Reset
						}
					},
				}
			},
		};

		let runtime_preproc = match action {
			Action::Pop => {
				let instance = self.template_instance.read();
				let template = instance.as_ref()
					.expect("template was created at function start; qed");
				let ret = self.pop_from_pool(template);
				self.ping_pool_observer();
				ret
			},
			Action::Reset => {
				let new_template = self.create_wasm_instance(wasm_executor, ext, default_heap_pages);
				let clone = new_template.clone();
				self.reset_pool(new_template);
				clone
			},
			Action::Invalid => {
				RuntimePreproc::InvalidCode
			}
		};

		match runtime_preproc {
			RuntimePreproc::InvalidCode => {
				let code = ext.original_storage(well_known_keys::CODE).unwrap_or(vec![]);
				Err(Error::InvalidCode(code))
			},
			RuntimePreproc::ValidCode(r, v) => {
				Ok((r, v))
			}
		}
	}

	fn reset_pool(&self, new_template: RuntimePreproc) {
		// it's important to set instance before truncating. otherwise
		// the bg thread will start spawning instance into the truncated
		// vec, before instance is also set to the new value.
		let mut template_instance = self.template_instance.write();
		*template_instance = Some(new_template);
		self.pool.write().truncate(0);
		self.ping_pool_observer();
	}

	/// Removes one instance from pool. If there is no instance in the pool
	/// one is created synchronously.
	/// template_instance is a parameter here to ensure that it always
	/// exists as a fallback at the place where this method is invoked.
	fn pop_from_pool(&self, template_instance: &RuntimePreproc) -> RuntimePreproc {
		let mut pool = self.pool.write();

		trace!(target: "runtimes_pool",
			   "about to pop one instance from pool with len {:?}",
			   pool.len());
		let maybe_instance = pool.pop();

		match maybe_instance  {
			Some(i) => i,
			None => {
				trace!(target: "runtimes_pool",
					   "no instance found in pool. creating synchronously");
				let ret = template_instance.clone();
				ret
			}
		}
	}

	fn create_pool_observer(&self) {
		trace!(target: "runtimes_pool", "creating new pool observer");
		let (tx, rx) = channel();
		*self.observer.write() = Some(tx);

		let template_instance = self.template_instance.clone();
		let runtime_pool = self.pool.clone();
		let thread = thread::spawn(move || {
			let mut instance_start = true;

			loop {
				trace!(target: "runtimes_pool", "observer waiting for message");
				if instance_start == false {
					match rx.recv() {
						Err(_)	=> {
							// The sender(s) are gone. This could mean that the main
							// program thread exited or e.g. tests exited.
							// Breaking here closes this thread, which is fine since
							// `get_pool_observer` creates an observer if none is found.
							break;
						},
						Ok(msg) => {
							trace!(target: "runtimes_pool", "observer received msg {:?}", msg);
							if let Msg::Shutdown = msg {
								trace!(target: "runtimes_pool", "observer received shutdown");
								break;
							}
						}
					}
				} else {
					instance_start = false;
				}
				trace!(target: "runtimes_pool", "observer received ping");

				{
					let pool = runtime_pool.read();
					if pool.len() > ADD_WHEN_LESS_THAN {
						continue;
					}
				}

				while {
					let pool = runtime_pool.read();
					pool.len() < INSTANCES_IN_POOL
				} {
					trace!(target: "runtimes_pool", "observer waiting for message");
					let mut pool = runtime_pool.write();
					trace!(target: "runtimes_pool",
						   "spawning new runtime to pool. len before: {:?}", pool.len());
					let instance_copy = template_instance.read().clone();
					pool.push(
						instance_copy
							.expect("template instance is created on first call into this module; qed")
					);
				}
			}
			()
		});
		*self.observer_thread.write() = Some(thread);
	}

	/// Get pool observer. If non-existent one will be created.
	fn get_pool_observer(&self) -> PoolSender {
		let has_observer = { (*self.observer.read()).is_some() };
		if !has_observer {
			self.create_pool_observer();
		}

		let observer = self.observer.write();
		observer.clone().expect("observer is created at function start, if missing; qed")
	}

	fn ping_pool_observer(&self) {
		trace!(target: "runtimes_pool", "pinging pool observer");
		let tx = self.get_pool_observer();
		tx.send(Msg::Ping)
			.expect("runtime pool observer is created if non-existent in getter; qed");
	}

	fn create_wasm_instance<E: Externalities<Blake2Hasher>>(
		&self,
		wasm_executor: &WasmExecutor,
		ext: &mut E,
		default_heap_pages: Option<u64>,
	) -> RuntimePreproc {
		let code = match ext.original_storage(well_known_keys::CODE) {
			Some(code) => code,
			None => return RuntimePreproc::InvalidCode,
		};

		let heap_pages = ext.storage(well_known_keys::HEAP_PAGES)
			.and_then(|pages| u64::decode(&mut &pages[..]))
			.or(default_heap_pages)
			.unwrap_or(DEFAULT_HEAP_PAGES);

		match WasmModule::from_buffer(code)
			.map_err(|_| Error::InvalidCode(vec![]))
			.and_then(|module| wasm_executor.prepare_module(ext, heap_pages as usize, &module))
			{
				Ok(module) => {
					let version = wasm_executor.call_in_wasm_module(ext, &module, "Core_version", &[])
						.ok()
						.and_then(|v| {
							RuntimeVersion::decode(&mut v.as_slice())//  as RuntimeVersion
						});
					RuntimePreproc::ValidCode(module, version)
				}
				Err(e) => {
					trace!(target: "runtimes_pool", "Invalid code presented to executor ({:?})", e);
					RuntimePreproc::InvalidCode
				}
			}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use super::Msg;
	use state_machine::TestExternalities;
	use std::{collections::HashMap, time};
	use substrate_test_runtime;

	/// Waits for either `f` to return true or a timeout. `f` is polled in a short interval.
	fn wait_for(f: fn(&RuntimesPool) -> bool, val: &RuntimesPool, timeout: time::Duration) -> bool {
		let started = time::Instant::now();
		loop {
			let poll_interval = time::Duration::from_millis(10);
			thread::sleep(poll_interval);

			let timed_out = started.elapsed() > timeout;
			if timed_out {
				return false;
			}
			if f(val) {
				return true;
			}
		}
	}

	/// Blocks until either the pool is full or a timeout is reached.
	fn wait_until_pool_filled(pool: &RuntimesPool) -> bool {
		let timeout = time::Duration::from_millis(2000);
		wait_for(|pool: &RuntimesPool| {
			let p = pool.pool.read();
			p.len() >= INSTANCES_IN_POOL
		}, pool, timeout)
	}

	fn shutdown_observer(pool: &RuntimesPool) {
		let mut observer = pool.observer.write();
		observer.take().expect("no observer available")
			.send(Msg::Shutdown).expect("Unable to send shutdown");

		let mut thread = pool.observer_thread.write();
		thread.take().expect("no observer thread available")
			.join().expect("Failed joining with observer thread");

		*observer = None;
	}

	fn count_compatible_instances(pool: &RuntimesPool, version: &RuntimeVersion) -> usize {
		let pool = pool.pool.read();
		pool
			.iter()
			.map(|maybe_runtime_preproc: &RuntimePreproc| -> bool {
				let ret = match maybe_runtime_preproc {
					RuntimePreproc::ValidCode(_, ref maybe_version) => {
						match maybe_version {
							Some(v) => {
								v.can_call_with(version)
							},
							None => panic!("found no version for pool instance"),
						}
					},
					RuntimePreproc::InvalidCode => panic!("found invalid code for pool instance"),
				};
				ret
			})
			.filter(|i| *i == true)
			.count()
	}

	#[test]
	fn should_fill_pool_lazily() {
		let pool = RuntimesPool::new();
		let len = pool.pool.read().len();
		assert_eq!(len, 0);

		let test_code = include_bytes!("../../test-runtime/wasm/target/wasm32-unknown-unknown/release/substrate_test_runtime.compact.wasm");
		let mut ext = TestExternalities::<Blake2Hasher, u64>::new_with_code(test_code, HashMap::new());

		// fill only when requested for the first time
		pool.fetch_runtime_from_pool(
			&WasmExecutor::new(),
			&mut ext,
			None,
			None,
		).expect("must have runtime now");

		assert_eq!(wait_until_pool_filled(&pool), true);

		shutdown_observer(&pool);

		let p = pool.pool.read();
		assert_eq!(p.len(), INSTANCES_IN_POOL);
	}

	#[test]
	fn should_reset_cache_when_incompatible_version_requested() {
		let pool = RuntimesPool::new();

		let test_code = include_bytes!("../../../node-template/runtime/wasm/target/wasm32-unknown-unknown/release/node_template_runtime_wasm.wasm");
		let mut ext = TestExternalities::<Blake2Hasher, u64>::new_with_code(test_code, HashMap::new());

		let inst = pool.fetch_runtime_from_pool(
			&WasmExecutor::new(),
			&mut ext,
			None,
			None,
		).expect("must have runtime now");

		let first_version = match inst {
			(_, Some(version)) => version,
			_ => panic!("unable to extract version"),
		};

		assert_eq!(wait_until_pool_filled(&pool), true);

		let test_code = include_bytes!("../../test-runtime/wasm/target/wasm32-unknown-unknown/release/substrate_test_runtime.compact.wasm");
		let mut ext = TestExternalities::<Blake2Hasher, u64>::new_with_code(test_code, HashMap::new());

		let inst = pool.fetch_runtime_from_pool(
			&WasmExecutor::new(),
			&mut ext,
			None,
			Some(&substrate_test_runtime::VERSION),
		).expect("must have runtime now");

		let second_version = match inst {
			(_, Some(version)) => version,
			_ => panic!("unable to extract version"),
		};

		assert_eq!(wait_until_pool_filled(&pool), true);

		// shutdown observer so that it doesn't continue filling the pool
		shutdown_observer(&pool);

		assert_eq!(count_compatible_instances(&pool, &first_version), 0);
		assert_eq!(count_compatible_instances(&pool, &second_version), INSTANCES_IN_POOL);
	}
}
