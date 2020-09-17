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

#[cfg(feature = "std")]
mod inner {
	use std::sync::mpsc;
	use sp_externalities::ExternalitiesExt as _;
	use crate::TaskExecutorExt;

	/// Task handle (wasm).
	///
	/// This can be `join`-ed to get (blocking) the result of
	/// the spawned task execution.
	#[must_use]
	pub struct DataJoinHandle {
		receiver: mpsc::Receiver<Vec<u8>>,
	}

	impl DataJoinHandle {
		/// Join handle returned by `spawn` function
		pub fn join(self) -> Vec<u8> {
			self.receiver.recv().expect("Essential task failure: spawned runtime terminated before sending result.")
		}
	}

	/// Spawn new runtime task (native).
	pub fn spawn(entry_point: fn(Vec<u8>) -> Vec<u8>, data: Vec<u8>) -> Result<DataJoinHandle, &'static str> {
		let scheduler = sp_externalities::with_externalities(|mut ext| ext.extension::<TaskExecutorExt>()
			.expect("No task executor associated with the current context!")
			.clone()
		).ok_or("Spawn called outside of externalities context!")?;

		let (sender, receiver) = mpsc::channel();
		let extra_scheduler = scheduler.clone();
		scheduler.spawn("parallel-runtime-spawn", Box::pin(async move {
			let result = match crate::new_async_externalities(extra_scheduler) {
				Ok(mut ext) => {
					sp_externalities::set_and_run_with_externalities(
						&mut ext,
						move || entry_point(data),
					)
				},
				Err(e) => {
					log::warn!(
						target: "runtime",
						"Unable to run async task: {}",
						e,
					);

					return;
				},
			};

			let _ = sender.send(result);
		}));

		Ok(DataJoinHandle { receiver })
	}
}

#[cfg(not(feature = "std"))]
mod inner {

	use core::mem;
	use sp_std::{vec::Vec, prelude::Box};

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
	extern "C" fn dispatch_wrapper(func_ref: u32, payload_ptr: u32, payload_len: u32) -> u64 {
		let payload_len = payload_len as usize;
		let output = unsafe {
			let payload = Vec::from_raw_parts(payload_ptr as usize as *mut _, payload_len, payload_len);
			let ptr: fn(Vec<u8>) -> Vec<u8> = core::mem::transmute(func_ref);
			(ptr)(payload)
		};
		sp_runtime_interface::pack_ptr_and_len(output.as_ptr() as usize as _, output.len() as _)
	}

	/// Spawn new runtime task (wasm).
	pub fn spawn(entry_point: fn(Vec<u8>) -> Vec<u8>, payload: Vec<u8>) -> DataJoinHandle {
		let func_ptr: usize = unsafe { core::mem::transmute(entry_point) };

		let handle = crate::runtime_tasks::spawn(
			dispatch_wrapper as usize as _,
			func_ptr as u32,
			payload,
		);
		DataJoinHandle { handle }
	}

	/// Task handle (wasm).
	///
	/// This can be `join`-ed to get (blocking) the result of
	/// the spawned task execution.
	#[must_use]
	pub struct DataJoinHandle {
		handle: u64,
	}

	impl DataJoinHandle {
		/// Join handle returned by `spawn` function
		pub fn join(self) -> Vec<u8> {
			crate::runtime_tasks::join(self.handle)
		}
	}
}

pub use inner::{DataJoinHandle, spawn};
