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

#![cfg_attr(feature = "without-std", no_std)]
#![cfg_attr(feature = "strict", deny(warnings))]

#[macro_use]
extern crate runtime_support;

#[cfg(test)]
extern crate rustc_hex;

mod codec;
#[macro_use]
mod support;
mod runtime;
pub use codec::{endiansensitive, streamreader, joiner, slicable, keyedvec};
pub use support::{primitives, function, proposal, environment, storable};
#[cfg(test)]
pub use support::{testing, statichex};

use runtime_support::Vec;
use slicable::Slicable;
use primitives::{Block, UncheckedTransaction};

/// Execute a block, with `input` being the canonical serialisation of the block. Returns the
/// empty vector.
pub fn execute_block(input: &[u8]) -> Vec<u8> {
	runtime::system::execute_block(Block::from_slice(input).unwrap());
	Vec::new()
}

/// Execute a given, serialised, transaction. Returns the empty vector.
pub fn execute_transaction(input: &[u8]) -> Vec<u8> {
	runtime::system::execute_transaction(&UncheckedTransaction::from_slice(input).unwrap());
	Vec::new()
}

impl_stubs!(execute_block, execute_transaction);
