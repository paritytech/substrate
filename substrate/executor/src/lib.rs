// Copyright 2017 Parity Technologies (UK) Ltd.
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
//! I leave it as is for now as it might be removed before this is ever done.

#![warn(missing_docs)]
#![recursion_limit="128"]

extern crate substrate_codec as codec;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_primitives as primitives;
extern crate substrate_serializer as serializer;
extern crate substrate_state_machine as state_machine;
extern crate substrate_runtime_version as runtime_version;
extern crate ed25519;

extern crate serde;
extern crate wasmi;
extern crate byteorder;
extern crate triehash;
extern crate parking_lot;
extern crate twox_hash;
#[macro_use] extern crate log;

#[macro_use]
extern crate lazy_static;

#[macro_use]
extern crate error_chain;

#[cfg(test)]
extern crate assert_matches;

#[cfg(test)]
extern crate wabt;

#[cfg(test)]
#[macro_use]
extern crate hex_literal;

#[macro_use]
mod wasm_utils;
mod wasm_executor;
#[macro_use]
mod native_executor;
mod sandbox;

pub mod error;
pub use wasm_executor::WasmExecutor;
pub use native_executor::{with_native_environment, NativeExecutor, NativeExecutionDispatch};
pub use state_machine::Externalities;
pub use runtime_version::RuntimeVersion;
pub use codec::Codec;

/// Provides runtime information.
pub trait RuntimeInfo {
	/// Native runtime information if any.
	const NATIVE_VERSION: Option<RuntimeVersion>;

	/// Extract RuntimeVersion of given :code block
	fn runtime_version<E: Externalities> (
		&self,
		ext: &mut E,
		code: &[u8]
	) -> Option<RuntimeVersion>;
}
