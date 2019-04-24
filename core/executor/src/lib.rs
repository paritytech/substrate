// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//! Temporary crate for contracts implementations.
//!
//! This will be replaced with WASM contracts stored on-chain.
//! ** NOTE ***
//! This is entirely deprecated with the idea of a single-module Wasm module for state transition.
//! The dispatch table should be replaced with the specific functions needed:
//! - execute_block(bytes)
//! - init_block(PrevBlock?) -> InProgressBlock
//! - add_transaction(InProgressBlock) -> InProgressBlock
//! It is left as is for now as it might be removed before this is ever done.

#![warn(missing_docs)]
#![recursion_limit="128"]

#[macro_use]
mod wasm_utils;
mod wasm_executor;
#[macro_use]
mod native_executor;
mod sandbox;
mod allocator;

pub mod error;
pub use wasmi;
pub use wasm_executor::WasmExecutor;
pub use native_executor::{with_native_environment, NativeExecutor, NativeExecutionDispatch};
pub use state_machine::Externalities;
pub use runtime_version::{RuntimeVersion, NativeVersion};
pub use parity_codec::Codec;
#[doc(hidden)]
pub use primitives::Blake2Hasher;

/// Provides runtime information.
pub trait RuntimeInfo {
	/// Native runtime information.
	fn native_version(&self) -> &NativeVersion;

	/// Extract RuntimeVersion of given :code block
	fn runtime_version<E: Externalities<Blake2Hasher>> (
		&self,
		ext: &mut E,
	) -> Option<RuntimeVersion>;
}
