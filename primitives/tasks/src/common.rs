// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Common utilities and types for implementing `RuntimeSpawn` trait.

use sp_externalities::{WorkerResult, Externalities, AsyncExternalities};
use sp_std::sync::Arc;
use sp_std::boxed::Box;
use sp_std::vec::Vec;
#[cfg(feature = "std")]
use crate::wasm_runtime::{WasmInstance, WasmModule, InvokeMethod};
#[cfg(feature = "std")]
use crate::error::Error;
#[cfg(feature = "std")]
use std::panic::{AssertUnwindSafe, UnwindSafe};
#[cfg(feature = "std")]
pub use log::error as log_error;

/// Set up the externalities and safe calling environment to execute runtime calls.
///
/// If the inner closure panics, it will be caught and return an error.
#[cfg(feature = "std")]
pub fn with_externalities_safe<F, U>(ext: &mut dyn Externalities, f: F) -> Result<U, Error>
	where F: UnwindSafe + FnOnce() -> U
{
	sp_externalities::set_and_run_with_externalities(
		ext,
		move || {
			// Substrate uses custom panic hook that terminates process on panic. Disable
			// termination for the native call.
			let _guard = sp_panic_handler::AbortGuard::force_unwind();
			std::panic::catch_unwind(f).map_err(|e| {
				if let Some(err) = e.downcast_ref::<String>() {
					Error::RuntimePanicked(err.clone())
				} else if let Some(err) = e.downcast_ref::<&'static str>() {
					Error::RuntimePanicked(err.to_string())
				} else {
					Error::RuntimePanicked("Unknown panic".into())
				}
			})
		},
	)
}

/// Not std `with_externalities_safe` is only for use with environment
/// where no threads are use.
/// This will NOT catch panic.
///
/// This means that any panic from a worker (using thread and std) have
/// to panic on 'join' (dismissed case work because inline processing
/// only run on 'join').
#[cfg(not(feature = "std"))]
fn with_externalities_safe<F, U>(ext: &mut dyn Externalities, f: F) -> Result<U, ()>
	where F: FnOnce() -> U
{
	Ok(sp_externalities::set_and_run_with_externalities(
		ext,
		f,
	))
}

/// A call for wasm context.
pub struct WasmTask {
	/// Pointer to its dispatcher function:
	/// a wasm function that redirect the calls.
	pub dispatcher_ref: u32,
	/// Input data for this task call.
	pub data: Vec<u8>,
	/// Pointer to the actual wasm function.
	pub func: u32,
}

/// A native call, it directly access the function
/// to call.
pub struct NativeTask {
	/// Function to call with this task.
	pub func: fn(Vec<u8>) -> Vec<u8>,
	/// Input data for this task call.
	pub data: Vec<u8>,
}

/// A worker task, this is a callable function.
pub enum Task {
	/// See `NativeTask`.
	Native(NativeTask),
	/// See `WasmTask`.
	Wasm(WasmTask),
}

/// A task and its context that is waiting
/// to be processed or dismissed.
pub struct PendingTask {
	/// The actual `Task`.
	pub task: Task,
	/// The associated `Externalities`
	/// this task will get access to.
	pub ext: Box<dyn AsyncExternalities>,
}

/// Technical only trait to factor code.
/// It accesses module instance lazily.
#[cfg(feature = "std")]
pub trait LazyInstanciate<'a> {
	/// Calling this function consume the lazy instantiate struct (similar
	/// semantic as `FnOnce`, and return a pointer to the existing or instantiated
	/// wasm instance.
	///
	/// Can return `None` when no module was defined or an error occurs, this should
	/// be considered as a panicking situation.
	fn instantiate(self) -> Option<&'a AssertUnwindSafe<Box<dyn WasmInstance>>>;
}

/// Lazy instantiate for non owned wasm instance.
#[cfg(feature = "std")]
pub struct InlineInstantiateRef<'a> {
	/// Thread safe reference counted to the module.
	pub module: &'a Option<Arc<dyn WasmModule>>,
	/// Thread safe reference to the instance.
	pub instance: &'a mut Option<AssertUnwindSafe<Box<dyn WasmInstance>>>,
}

#[cfg(feature = "std")]
impl<'a> LazyInstanciate<'a> for InlineInstantiateRef<'a> {
	fn instantiate(self) -> Option<&'a AssertUnwindSafe<Box<dyn WasmInstance>>> {
		if self.instance.is_none() {
			*self.instance = if let Some(instance) = instantiate_inline(self.module) {
				Some(instance)
			} else {
				return None
			}
		};
		self.instance.as_ref()
	}
}

#[cfg(feature = "std")]
/// Instantiate a wasm module.
/// This function is rather unsafe and should only be
/// use when `AssertUwindSafe` assertion stands.
pub fn instantiate(
	module: Option<&dyn WasmModule>,
) -> Option<AssertUnwindSafe<Box<dyn WasmInstance>>> {
	Some(match module.map(|m| m.new_instance()) {
		Some(Ok(val)) => AssertUnwindSafe(val),
		Some(Err(e)) => {
			log_error!(
				target: "executor",
				"Failed to create new instance for module for async context: {}",
				e,
			);
			return None;
		}
		None => {
			log_error!(target: "executor", "No module for a wasm task.");
			return None;
		},
	})
}

/// Helper method for `instantiate` function using a module arc reference.
#[cfg(feature = "std")]
pub fn instantiate_inline(
	module: &Option<Arc<dyn WasmModule>>,
) -> Option<AssertUnwindSafe<Box<dyn WasmInstance>>> {
	instantiate(module.as_ref().map(AsRef::as_ref))
}

/// Run a given task.
pub fn process_task<
	'a,
	#[cfg(feature = "std")]
	I: LazyInstanciate<'a> + 'a,
>(
	task: Task,
	async_ext: crate::AsyncExternalities,
	#[cfg(feature = "std")]
	instance_ref: I,
) -> WorkerResult {
	#[cfg(feature = "std")] {
		process_task_inner::<(),_>(
			task,
			async_ext,
			instance_ref,
		)
	}
	#[cfg(not(feature = "std"))] {
		process_task_inner::<()>(
			task,
			async_ext,
		)
	}
}

pub(crate) fn process_task_inner<
	'a,
	HostLocal: HostLocalFunction,
	#[cfg(feature = "std")]
	I: LazyInstanciate<'a> + 'a,
>(
	task: Task,
	mut async_ext: crate::AsyncExternalities,
	#[cfg(feature = "std")]
	instance_ref: I,
) -> WorkerResult {
	let result = match task {
		Task::Wasm(WasmTask { dispatcher_ref, func, data }) => {

			#[cfg(feature = "std")]
			if HostLocal::HOST_LOCAL {
				panic!("HOST_LOCAL is only expected for a wasm no_std call");
			} else {
				let instance = if let Some(instance) = instance_ref.instantiate() {
					instance
				} else {
					return WorkerResult::HardPanic;
				};
				match with_externalities_safe(
					&mut async_ext,
					|| instance.call(
						InvokeMethod::TableWithWrapper { dispatcher_ref, func },
						&data[..],
					)
				) {
					Ok(Ok(result)) => result,
					Ok(Err(error)) | Err(error) => {
						log_error!("Runtime panic error in wasm task: {:?}", error);
						return WorkerResult::RuntimePanic;
					},
				}
			}
			#[cfg(not(feature = "std"))]
			if HostLocal::HOST_LOCAL {
				let f: fn(Vec<u8>) -> Vec<u8> = unsafe { sp_std::mem::transmute(func) };
				match with_externalities_safe(
					&mut async_ext,
					|| f(data),
				) {
					Ok(result) => result,
					Err(error) => {
						log_error!("Runtime panic error in wasm task: {:?}", error);
						return WorkerResult::RuntimePanic;
					},
				}
			} else {
				panic!("No no_std wasm runner");
			}
		},
		Task::Native(NativeTask { func, data }) => {
			match with_externalities_safe(
				&mut async_ext,
				|| func(data),
			) {
				Ok(result) => result,
				#[cfg(not(feature = "std"))]
				Err(error) => {
					log_error!("Runtime panic error in wasm task: {:?}", error);
					return WorkerResult::RuntimePanic;
				},
				#[cfg(feature = "std")]
				Err(Error::RuntimePanicked(error)) => {
					log_error!("Runtime panic error in wasm task: {:?}", error);
					return WorkerResult::RuntimePanic;
				},
				#[cfg(feature = "std")]
				Err(error) => {
					log_error!("Wasm instance error in : {:?}", error);
					return WorkerResult::HardPanic;
				},
			}
		},
	};
	WorkerResult::Valid(result)
}

/// Technical trait to use instead of boolean parameter.
///
/// Indicate if this run as a local
/// function without runtime boundaries.
/// If it does, it is safe to assume
/// that a wasm pointer can be call directly.
pub trait HostLocalFunction: Copy + 'static {
	/// Associated boolean constant indicating if
	/// a struct is being use in the hosting context.
	///
	/// It defaults to false.
	const HOST_LOCAL: bool = false;
}

impl HostLocalFunction for () { }
