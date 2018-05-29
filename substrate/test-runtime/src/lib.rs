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
extern crate substrate_runtime_support as runtime_support;
extern crate substrate_codec as codec;
extern crate substrate_runtime_primitives as runtime_primitives;

#[cfg(feature = "std")]
extern crate serde;

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

#[cfg(test)]
#[macro_use]
extern crate hex_literal;
#[cfg(test)]
extern crate ed25519;
#[cfg(test)]
extern crate substrate_keyring as keyring;
#[cfg_attr(test, macro_use)]
extern crate substrate_primitives as primitives;
#[macro_use]
extern crate substrate_runtime_io as runtime_io;


#[cfg(feature = "std")] pub mod genesismap;
pub mod system;
mod transaction;
mod unchecked_transaction;

use rstd::prelude::*;
use codec::Slicable;

use primitives::AuthorityId;
use primitives::hash::H512;
pub use primitives::hash::H256;
pub use transaction::Transaction;
pub use unchecked_transaction::UncheckedTransaction;

/// A test block.
pub type Block = runtime_primitives::testing::Block<UncheckedTransaction>;
/// A test block's header.
pub type Header = runtime_primitives::testing::Header;
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
	let stxs = block.extrinsics.iter().map(Slicable::encode).collect::<Vec<_>>();
	print("reserialised transactions.");
	[stxs.len() as u8].encode()
}

pub mod api {
	use system;

	impl_stubs!(
		execute_block => |block| system::execute_block(block),
		apply_extrinsic => |(header, utx)| system::execute_transaction(utx, header),
		finalise_block => |header| system::finalise_block(header)
	);
}
