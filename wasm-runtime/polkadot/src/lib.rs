// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! The Polkadot runtime. This can be compiled with #[no_std], ready for Wasm.

#![cfg_attr(not(feature = "std"), no_std)]

#[macro_use]
extern crate polkadot_runtime_std as runtime_std;

#[cfg(feature = "std")]
extern crate rustc_hex;

extern crate polkadot_runtime_codec as codec;

#[cfg(test)]
#[macro_use]
extern crate hex_literal;

#[macro_use]
pub mod support;
pub mod primitives;
pub mod runtime;

use runtime_std::prelude::*;
use codec::Slicable;
use primitives::{Block, UncheckedTransaction};

/// Execute a block, with `input` being the canonical serialisation of the block. Returns the
/// empty vector.
pub fn execute_block(input: &[u8]) -> Vec<u8> {
	runtime::system::internal::execute_block(Block::from_slice(input).unwrap());
	Vec::new()
}

/// Execute a given, serialised, transaction. Returns the empty vector.
pub fn execute_transaction(input: &[u8]) -> Vec<u8> {
	let utx = UncheckedTransaction::from_slice(input).unwrap();
	runtime::system::internal::execute_transaction(&utx);
	Vec::new()
}

impl_stubs!(execute_block, execute_transaction);
