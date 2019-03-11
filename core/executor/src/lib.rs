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
