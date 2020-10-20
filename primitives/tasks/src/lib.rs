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
//!    fn my_parallel_computator(data: Vec<u8>) -> Vec<u8> {
//!        unimplemented!()
//!    }
//!    fn test(dynamic_variable: i32) {
//!        for _ in 0..dynamic_variable { sp_tasks::spawn(my_parallel_computator, vec![]); }
//!    }
//! ```
//!
//! While this is a good example:
//! ```rust
//!    use codec::Encode;
//!    static STATIC_VARIABLE: i32 = 4;
//!
//!    fn my_parallel_computator(data: Vec<u8>) -> Vec<u8> {
//!        unimplemented!()
//!    }
//!
//!    fn test(computation_payload: Vec<u8>) {
//!        let parallel_tasks = (0..STATIC_VARIABLE).map(|idx|
//!            sp_tasks::spawn(my_parallel_computator, computation_payload.chunks(10).nth(idx as _).encode())
//!        );
//!    }
//! ```
//!
//! When allowing unbounded parallelism, malicious transactions can exploit it and partition
//! network consensus based on how much resources nodes have.
//!

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
mod async_externalities;

#[cfg(feature = "std")]
pub use async_externalities::{new_async_externalities, AsyncExternalities};

#[cfg(feature = "std")]
mod inner {
	use std::{panic::AssertUnwindSafe, sync::mpsc};
	use sp_externalities::ExternalitiesExt as _;
	use sp_core::traits::TaskExecutorExt;

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
			self.receiver.recv().expect("Spawned runtime task terminated before sending result.")
		}
	}

	/// Spawn new runtime task (native).
	pub fn spawn(entry_point: fn(Vec<u8>) -> Vec<u8>, data: Vec<u8>) -> DataJoinHandle {
		let scheduler = sp_externalities::with_externalities(|mut ext| ext.extension::<TaskExecutorExt>()
			.expect("No task executor associated with the current context!")
			.clone()
		).expect("Spawn called outside of externalities context!");

		let (sender, receiver) = mpsc::channel();
		let extra_scheduler = scheduler.clone();
		scheduler.spawn("parallel-runtime-spawn", Box::pin(async move {
			let result = match crate::new_async_externalities(extra_scheduler) {
				Ok(mut ext) => {
					let mut ext = AssertUnwindSafe(&mut ext);
					match std::panic::catch_unwind(move || {
						sp_externalities::set_and_run_with_externalities(
							&mut **ext,
							move || entry_point(data),
						)
					}) {
						Ok(result) => result,
						Err(panic) => {
							log::error!(
								target: "runtime",
								"Spawned task panicked: {:?}",
								panic,
							);

							// This will drop sender without sending anything.
							return;
						}
					}
				},
				Err(e) => {
					log::error!(
						target: "runtime",
						"Unable to run async task: {}",
						e,
					);

					return;
				},
			};

			let _ = sender.send(result);
		}));

		DataJoinHandle { receiver }
	}
}

#[cfg(not(feature = "std"))]
mod inner {
	use core::mem;
	use sp_std::prelude::*;

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
	pub fn spawn(entry_point: fn(Vec<u8>) -> Vec<u8>, payload: Vec<u8>) -> DataJoinHandle {
		let func_ptr: usize = unsafe { mem::transmute(entry_point) };

		let handle = sp_io::runtime_tasks::spawn(
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
			sp_io::runtime_tasks::join(self.handle)
		}
	}
}

pub use inner::{DataJoinHandle, spawn};

#[cfg(test)]
mod tests {

	use super::*;

	fn async_runner(mut data: Vec<u8>) -> Vec<u8> {
		data.sort();
		data
	}

	fn async_panicker(_data: Vec<u8>) -> Vec<u8> {
		panic!("panic in async panicker!")
	}

	#[test]
	fn basic() {
		sp_io::TestExternalities::default().execute_with(|| {
			let a1 = spawn(async_runner, vec![5, 2, 1]).join();
			assert_eq!(a1, vec![1, 2, 5]);
		})
	}

	#[test]
	fn panicking() {
		let res = sp_io::TestExternalities::default().execute_with_safe(||{
			spawn(async_panicker, vec![5, 2, 1]).join();
		});

		assert!(res.unwrap_err().contains("Closure panicked"));
	}

	#[test]
	fn many_joins() {
		sp_io::TestExternalities::default().execute_with_safe(|| {
			// converges to 1 only after 1000+ steps
			let mut running_val = 9780657630u64;
			let mut data = vec![];
			let handles = (0..1024).map(
				|_| {
					running_val = if running_val % 2 == 0 {
						running_val / 2
					} else {
						3 * running_val + 1
					};
					data.push(running_val as u8);
					(spawn(async_runner, data.clone()), data.clone())
				}
			).collect::<Vec<_>>();

			for (handle, mut data) in handles {
				let result = handle.join();
				data.sort();

				assert_eq!(result, data);
			}
		}).expect("Failed to run with externalities");
	}
}
