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
//! Contains runtime-usable interface for spawning parallel purely computational tasks.

#[cfg(feature = "std")]
mod inner {
	use std::sync::mpsc;
	use sp_externalities::ExternalitiesExt as _;
	use crate::TaskExecutorExt;

	/// Task handle (wasm).
	///
	/// This can be `join`-ed to get (blocking) the result of
	/// the spawned task execution.
	pub struct DataJoinHandle {
		receiver: mpsc::Receiver<Vec<u8>>,
	}

	impl DataJoinHandle {
		/// Join handle returned by `spawn` function
		pub fn join(self) -> Vec<u8> {
			self.receiver.recv().expect("Essntial task failure: forked runtime terminated before sending result.")
		}
	}

	/// Spawn new runtime task (native).
	pub fn spawn(entry_point: fn(Vec<u8>) -> Vec<u8>, data: Vec<u8>) -> Result<DataJoinHandle, &'static str> {
		let scheduler = sp_externalities::with_externalities(|mut ext| ext.extension::<TaskExecutorExt>()
			.expect("No task executor associated with the current context!")
			.clone()
		).ok_or("Spawn called outside of externalities context!")?;

		let (sender, receiver) = mpsc::channel();
		scheduler.spawn("parallel-runtime-spawn", Box::pin(async move {
			let result = entry_point(data);
			let _ = sender.send(result);
		}));

		Ok(DataJoinHandle { receiver })
	}
}

#[cfg(not(feature = "std"))]
mod inner {

	use sp_std::vec::Vec;

	/// Spawn new runtime task (wasm).
	pub fn spawn(entry_point: fn(Vec<u8>) -> Vec<u8>, payload: Vec<u8>) -> DataJoinHandle {

		/// Dynamic dispatch of wasm blob.
		///
		/// Arguments are expected to be scale encoded in vector at address `payload_ptr` with length of
		/// `payload_len`.
		///
		/// Arguments: function pointer (u32), input (Vec<u8>).
		///
		/// Function at pointer is expected to have signature of `(Vec<u8>) -> Vec<u8>`. Since this dynamic dispatch
		/// function and the invoked function are compiled with the same compiler, there should be no problem with
		/// ABI incompatibility.
		#[no_mangle]
		unsafe extern "C" fn dyn_dispatch(payload_ptr: u32, payload_len: u32) -> u64 {

			use codec::Decode as _;

			let mut data: &[u8] = core::slice::from_raw_parts(payload_ptr as usize as *const u8, payload_len as usize);
			let entry = u32::decode(&mut data).expect("Failed to decode input") as usize;
			let ptr: fn(Vec<u8>) -> Vec<u8> = core::mem::transmute(entry);
			let payload = Vec::<u8>::decode(&mut data).expect("Failed to decode input");

			let output = (ptr)(payload);

			let mut output_encode = (output.len() as u64) << 32;
			output_encode | (output.as_ptr() as usize as u64)
		}

		let func_ptr: usize = unsafe { core::mem::transmute(entry_point) };

		let handle = unsafe { crate::runtime_tasks::spawn(func_ptr as u32, payload) };
		DataJoinHandle { handle }
	}

	/// Task handle (wasm).
	///
	/// This can be `join`-ed to get (blocking) the result of
	/// the spawned task execution.
	pub struct DataJoinHandle {
		handle: u32,
	}

	impl DataJoinHandle {
		/// Join handle returned by `spawn` function
		pub fn join(self) -> Vec<u8> {
			crate::runtime_tasks::join(self.handle)
		}
	}
}

pub use inner::{DataJoinHandle, spawn};
