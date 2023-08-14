// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Types that should only be used for testing!

use crate::crypto::KeyTypeId;

/// Key type for generic Ed25519 key.
pub const ED25519: KeyTypeId = KeyTypeId(*b"ed25");
/// Key type for generic Sr25519 key.
pub const SR25519: KeyTypeId = KeyTypeId(*b"sr25");
/// Key type for generic ECDSA key.
pub const ECDSA: KeyTypeId = KeyTypeId(*b"ecds");
/// Key type for generic Bandersnatch key.
pub const BANDERSNATCH: KeyTypeId = KeyTypeId(*b"band");
/// Key type for generic BLS12-377 key.
pub const BLS377: KeyTypeId = KeyTypeId(*b"bls7");
/// Key type for generic BLS12-381 key.
pub const BLS381: KeyTypeId = KeyTypeId(*b"bls8");

/// Macro for exporting functions from wasm in with the expected signature for using it with the
/// wasm executor. This is useful for tests where you need to call a function in wasm.
///
/// The input parameters are expected to be SCALE encoded and will be automatically decoded for you.
/// The output value is also SCALE encoded when returned back to the host.
///
/// The functions are feature-gated with `#[cfg(not(feature = "std"))]`, so they are only available
/// from within wasm.
///
/// # Example
///
/// ```
/// # use sp_core::wasm_export_functions;
///
/// wasm_export_functions! {
///     fn test_in_wasm(value: bool, another_value: Vec<u8>) -> bool {
///         value && another_value.is_empty()
///     }
///
///     fn without_return_value() {
///         // do something
///     }
/// }
/// ```
#[macro_export]
macro_rules! wasm_export_functions {
	(
		$(
			fn $name:ident (
				$( $arg_name:ident: $arg_ty:ty ),* $(,)?
			) $( -> $ret_ty:ty )? { $( $fn_impl:tt )* }
		)*
	) => {
		$(
			$crate::wasm_export_functions! {
				@IMPL
				fn $name (
					$( $arg_name: $arg_ty ),*
				) $( -> $ret_ty )? { $( $fn_impl )* }
			}
		)*
	};
	(@IMPL
		fn $name:ident (
				$( $arg_name:ident: $arg_ty:ty ),*
		) { $( $fn_impl:tt )* }
	) => {
		#[no_mangle]
		#[allow(unreachable_code)]
		#[cfg(not(feature = "std"))]
		pub fn $name(input_data: *mut u8, input_len: usize) -> u64 {
			let input: &[u8] = if input_len == 0 {
				&[0u8; 0]
			} else {
				unsafe {
					$crate::sp_std::slice::from_raw_parts(input_data, input_len)
				}
			};

			{
				let ($( $arg_name ),*) : ($( $arg_ty ),*) = $crate::Decode::decode(
					&mut &input[..],
				).expect("Input data is correctly encoded");

				(|| { $( $fn_impl )* })()
			}

			$crate::to_substrate_wasm_fn_return_value(&())
		}
	};
	(@IMPL
		fn $name:ident (
				$( $arg_name:ident: $arg_ty:ty ),*
		) $( -> $ret_ty:ty )? { $( $fn_impl:tt )* }
	) => {
		#[no_mangle]
		#[allow(unreachable_code)]
		#[cfg(not(feature = "std"))]
		pub fn $name(input_data: *mut u8, input_len: usize) -> u64 {
			let input: &[u8] = if input_len == 0 {
				&[0u8; 0]
			} else {
				unsafe {
					$crate::sp_std::slice::from_raw_parts(input_data, input_len)
				}
			};

			let output $( : $ret_ty )? = {
				let ($( $arg_name ),*) : ($( $arg_ty ),*) = $crate::Decode::decode(
					&mut &input[..],
				).expect("Input data is correctly encoded");

				(|| { $( $fn_impl )* })()
			};

			$crate::to_substrate_wasm_fn_return_value(&output)
		}
	};
}

/// A task executor that can be used in tests.
///
/// Internally this just wraps a `ThreadPool` with a pool size of `8`. This
/// should ensure that we have enough threads in tests for spawning blocking futures.
#[cfg(feature = "std")]
#[derive(Clone)]
pub struct TaskExecutor(futures::executor::ThreadPool);

#[cfg(feature = "std")]
impl TaskExecutor {
	/// Create a new instance of `Self`.
	pub fn new() -> Self {
		let mut builder = futures::executor::ThreadPoolBuilder::new();
		Self(builder.pool_size(8).create().expect("Failed to create thread pool"))
	}
}

#[cfg(feature = "std")]
impl Default for TaskExecutor {
	fn default() -> Self {
		Self::new()
	}
}

#[cfg(feature = "std")]
impl crate::traits::SpawnNamed for TaskExecutor {
	fn spawn_blocking(
		&self,
		_name: &'static str,
		_group: Option<&'static str>,
		future: futures::future::BoxFuture<'static, ()>,
	) {
		self.0.spawn_ok(future);
	}
	fn spawn(
		&self,
		_name: &'static str,
		_group: Option<&'static str>,
		future: futures::future::BoxFuture<'static, ()>,
	) {
		self.0.spawn_ok(future);
	}
}

#[cfg(feature = "std")]
impl crate::traits::SpawnEssentialNamed for TaskExecutor {
	fn spawn_essential_blocking(
		&self,
		_: &'static str,
		_: Option<&'static str>,
		future: futures::future::BoxFuture<'static, ()>,
	) {
		self.0.spawn_ok(future);
	}
	fn spawn_essential(
		&self,
		_: &'static str,
		_: Option<&'static str>,
		future: futures::future::BoxFuture<'static, ()>,
	) {
		self.0.spawn_ok(future);
	}
}
