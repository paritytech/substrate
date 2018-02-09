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

//! The Substrate runtime. This can be compiled with #[no_std], ready for Wasm.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate substrate_runtime_std as rstd;
#[macro_use]
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_runtime_support as runtime_support;
extern crate substrate_codec as codec;
#[cfg(test)] #[macro_use] extern crate hex_literal;
#[cfg_attr(test, macro_use)] extern crate substrate_primitives as primitives;

#[cfg(feature = "std")]
pub mod genesismap;
pub mod system;
mod transaction;
mod unchecked_transaction;
mod block;

use rstd::prelude::*;
use codec::Slicable;

use primitives::AuthorityId;
use primitives::hash::H512;
pub use primitives::hash::H256;
pub use primitives::block::{Header, Number as BlockNumber, Digest};
pub use transaction::Transaction;
pub use unchecked_transaction::UncheckedTransaction;
pub use block::Block;

/// An identifier for an account on this system.
pub type AccountId = AuthorityId;
/// Signature for our transactions.
pub type Signature = H512;
/// A simple hash type for all our hashing.
pub type Hash = H256;

/// Run whatever tests we have.
pub fn run_tests(mut input: &[u8]) -> Vec<u8> {
	use runtime_io::print;

	print("run_tests...");
	let block = Block::decode(&mut input).unwrap();
	print("deserialised block.");
	let stxs = block.transactions.iter().map(Slicable::encode).collect::<Vec<_>>();
	print("reserialised transactions.");
	[stxs.len() as u8].encode()
}

pub mod apis {
	use system;

	impl_stubs!(
		execute_block => |block| system::execute_block(block),
		execute_transaction => |(header, utx)| system::execute_transaction(utx, header),
		finalise_block => |header| system::finalise_block(header)
	);
}
