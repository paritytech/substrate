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

use rstd::prelude::*;
use codec::Slicable;

use runtime_primitives::traits::BlakeTwo256;
use runtime_primitives::Ed25519Signature;
pub use primitives::hash::H256;

/// Calls in transactions.
#[derive(Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct Call {
	pub to: AccountId,
	pub amount: u64,
}

impl Slicable for Call {
	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();
		self.to.using_encoded(|s| v.extend(s));
		self.amount.using_encoded(|s| v.extend(s));
		v
	}

	fn decode<I: ::codec::Input>(input: &mut I) -> Option<Self> {
		Slicable::decode(input).map(|(to, amount)| Call { to, amount })
	}
}

/// An identifier for an account on this system.
pub type AccountId = H256;
/// A simple hash type for all our hashing.
pub type Hash = H256;
/// The block number type used in this runtime.
pub type BlockNumber = u64;
/// Index of a transaction.
pub type Index = u64;
/// The digest of a block.
pub type Digest = runtime_primitives::generic::Digest<Vec<u8>>;
/// A test block.
pub type Block = runtime_primitives::generic::Block<BlockNumber, BlakeTwo256, Vec<u8>, AccountId, Index, Call, Ed25519Signature>;
/// A test block's header.
pub type Header = runtime_primitives::generic::Header<BlockNumber, BlakeTwo256, Vec<u8>>;
/// Extrinsic
pub type Extrinsic = runtime_primitives::generic::Extrinsic<AccountId, Index, Call>;
/// Signed extrinsic.
pub type UncheckedExtrinsic = runtime_primitives::generic::UncheckedExtrinsic<AccountId, Index, Call, Ed25519Signature>;

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
		authorities => |()| system::authorities(),
		execute_block => |block| system::execute_block(block),
		apply_extrinsic => |(header, utx)| system::execute_transaction(utx, header),
		finalise_block => |header| system::finalise_block(header)
	);
}
