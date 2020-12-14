// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Runtime tasks.
//!
//! Contains runtime-usable functions for spawning parallel purely computational tasks.
//!
//! NOTE: This is experimental API.
//! NOTE: When using in actual runtime, make sure you don't produce unbounded parallelism.
//! So this is bad example to use it:
//! ```rust
//!    use sp_tasks::WorkerType;
//!    fn my_parallel_computator(data: Vec<u8>) -> Vec<u8> {
//!        unimplemented!()
//!    }
//!    fn test(dynamic_variable: i32) {
//!       for _ in 0..dynamic_variable {
//!					sp_tasks::spawn(my_parallel_computator, vec![], WorkerType::Stateless);
//!				}
//!    }
//! ```
//!
//! While this is a good example:
//! ```rust
//!    use codec::Encode;
//!    use sp_tasks::WorkerType;
//!    static STATIC_VARIABLE: i32 = 4;
//!
//!    fn my_parallel_computator(data: Vec<u8>) -> Vec<u8> {
//!        unimplemented!()
//!    }
//!
//!    fn test(computation_payload: Vec<u8>) {
//!        let parallel_tasks = (0..STATIC_VARIABLE).map(|idx| sp_tasks::spawn(
//!            my_parallel_computator,
//!            computation_payload.chunks(10).nth(idx as _).encode(),
//!            WorkerType::Stateless,
//!        ));
//!    }
//! ```
//!
//! When allowing unbounded parallelism, malicious transactions can exploit it and partition
//! network consensus based on how much resources nodes have.
//!

#![cfg_attr(not(feature = "std"), no_std)]

mod async_externalities;

#[cfg(feature = "std")]
pub use async_externalities::new_async_externalities;
pub use async_externalities::{new_inline_only_externalities, AsyncExternalities, AsyncExt};
pub use sp_externalities::{WorkerResult, WorkerDeclaration};
pub use sp_io::Crossing;
use sp_std::vec::Vec;

/// Differents workers execution mode `AsyncState`, it results
/// in differents `AsyncExt externality.
#[derive(Debug)]
#[repr(u8)]
pub enum WorkerType {
	/// Externalities do not access state, so we join
	Stateless = 0,

	/// Externalities access read only the backend unmodified state.
	ReadLastBlock = 1,

	/// Externalities access read only the backend unmodified state,
	/// and the change at the time of spawn.
	/// In this case when joining we return an identifier of the
	/// state at launch.
	ReadAtSpawn = 2,

	/// State between main thread and child workers must be the same.
	/// We return `None` on join if some state access break this asumption:
	/// Any access to a variable that was modified in parent worker.
	ReadOptimistic = 3,

	/// State between main thread and child workers must be the same.
	/// When starting a child worker we declare exclusive write access
	/// over the keyspace for both worker.
	/// Writing in undeclared location or reading a location declared as writable
	/// in another worker will result in a panic.
	ReadDeclarative = 4,
}

impl Default for WorkerType {
	fn default() -> Self {
		WorkerType::Stateless
	}
}

impl WorkerType {
	/// Similar purpose as `TryFrom<u8>`.
	pub fn from_u8(kind: u8) -> Option<WorkerType> {
		Some(match kind {
			0 => WorkerType::Stateless,
			1 => WorkerType::ReadLastBlock,
			2 => WorkerType::ReadAtSpawn,
			_ => return None,
		})
	}

	/// Depending on concurrency management strategy
	/// we may need to resolve the result against
	/// parent externalities.
	pub fn need_resolve(&self) -> bool {
		match *self {
			WorkerType::Stateless => false,
			WorkerType::ReadLastBlock => false,
			WorkerType::ReadAtSpawn => true,
			WorkerType::ReadDeclarative => true,
			WorkerType::ReadOptimistic => true,
		}
	}
}

/// Task handle.
///
/// This can be `join`-ed to get (blocking) the result of
/// the spawned task execution.
#[must_use]
pub struct DataJoinHandle {
	handle: u64,
}

impl DataJoinHandle {
	/// Join handle returned by `spawn` function
	pub fn join(self) -> Option<Vec<u8>> {
		sp_io::runtime_tasks::join(self.handle)
	}

	/// Indicate that handle result will not be needed.
	pub fn dismiss(self) {
		sp_io::runtime_tasks::dismiss(self.handle)
	}
}

/// Change maximum number of parallel workers capacity
/// for the current runtime.
pub fn set_capacity(capacity: u32) {
	sp_io::runtime_tasks::set_capacity(capacity)
}

#[cfg(feature = "std")]
mod inner {
	use sp_externalities::{Externalities, ExternalitiesExt as _};
	use sp_core::traits::RuntimeSpawnExt;
	use crate::{WorkerType, WorkerDeclaration};
	use super::DataJoinHandle;

	/// Spawn new runtime task (native).
	pub fn spawn(
		entry_point: fn(Vec<u8>) -> Vec<u8>,
		data: Vec<u8>,
		kind: WorkerType,
		declaration: WorkerDeclaration, // TODO consider splitting spawn
	) -> DataJoinHandle {
		let handle = sp_externalities::with_externalities(|mut ext|{
			let ext_unsafe = ext as *mut dyn Externalities;
			let runtime_spawn = ext.extension::<RuntimeSpawnExt>()
				.expect("Cannot spawn without dynamic runtime dispatcher (RuntimeSpawnExt)");
			// Unsafe usage here means that `spawn_call` shall never attempt to access
			// or deregister this `RuntimeSpawnExt` from the unchecked ext2.
			let ext_unsafe: &mut _  = unsafe { &mut *ext_unsafe };
			// TODO could wrap ext_unsafe in a ext struct that filter calls to extension of
			// a given id, to make this safer.
			let result = runtime_spawn.spawn_call_native(entry_point, data, kind as u8, declaration, ext_unsafe);
			std::sync::atomic::compiler_fence(std::sync::atomic::Ordering::AcqRel);
			// Not necessary (same lifetime as runtime_spawn), but shows intent to keep
			// ext alive as long as ext_unsafe is in scope.
			drop(ext);
			result
		}).expect("`RuntimeTasks::spawn`: called outside of externalities context");

		DataJoinHandle { handle }
	}
}

#[cfg(not(feature = "std"))]
mod inner {
	use core::mem;
	use sp_std::prelude::*;
	use crate::{WorkerType, WorkerDeclaration};
	use super::DataJoinHandle;

	/// Dispatch wrapper for wasm blob.
	///
	/// Serves as trampoline to call any rust function with (Vec<u8>) -> Vec<u8> compiled
	/// into the runtime.
	///
	/// Function item should be provided with `func_ref`. Argument for the call
	/// will be generated from bytes at `payload_ptr` with `payload_len`.
	///
	/// NOTE: Since this dynamic dispatch function and the invoked function are compiled with
	/// the same compiler, there should be no problem with ABI incompatibility.
	extern "C" fn dispatch_wrapper(func_ref: *const u8, payload_ptr: *mut u8, payload_len: u32) -> u64 {
		let payload_len = payload_len as usize;
		let output = unsafe {
			let payload = Vec::from_raw_parts(payload_ptr, payload_len, payload_len);
			let ptr: fn(Vec<u8>) -> Vec<u8> = mem::transmute(func_ref);
			(ptr)(payload)
		};
		sp_runtime_interface::pack_ptr_and_len(output.as_ptr() as usize as _, output.len() as _)
	}

	/// Spawn new runtime task (wasm).
	pub fn spawn(
		entry_point: fn(Vec<u8>) -> Vec<u8>,
		payload: Vec<u8>,
		kind: WorkerType,
		declaration: WorkerDeclaration, // TODO consider splitting spawn
	) -> DataJoinHandle {
		let func_ptr: usize = unsafe { mem::transmute(entry_point) };

		let handle = sp_io::runtime_tasks::spawn(
			dispatch_wrapper as usize as _,
			func_ptr as u32,
			payload,
			kind as u8,
			sp_io::task_declaration(declaration),
		);
		DataJoinHandle { handle }
	}
}

pub use inner::spawn;
