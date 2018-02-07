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

extern crate substrate_codec as codec;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_primitives as primitives;
extern crate substrate_serializer as serializer;
extern crate substrate_state_machine as state_machine;
extern crate ed25519;

extern crate serde;
extern crate parity_wasm;
extern crate byteorder;
extern crate rustc_hex;
extern crate triehash;
#[macro_use] extern crate log;

#[cfg(test)]
#[macro_use]
extern crate hex_literal;

#[macro_use]
extern crate error_chain;

#[cfg(test)]
extern crate assert_matches;

// TODO: move into own crate
macro_rules! map {
	($( $name:expr => $value:expr ),*) => (
		vec![ $( ( $name, $value ) ),* ].into_iter().collect()
	)
}

#[macro_use]
mod wasm_utils;
mod wasm_executor;
mod native_executor;

pub mod error;
pub use wasm_executor::WasmExecutor;
pub use native_executor::{NativeExecutionDispatch, NativeExecutor};
