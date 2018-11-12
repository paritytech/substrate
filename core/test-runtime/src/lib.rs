// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

extern crate sr_std as rstd;
extern crate parity_codec as codec;
extern crate sr_primitives as runtime_primitives;

#[macro_use]
extern crate srml_support as runtime_support;
#[macro_use]
extern crate parity_codec_derive;
#[macro_use]
extern crate sr_api as runtime_api;
extern crate sr_io as runtime_io;
#[macro_use]
extern crate sr_version as runtime_version;


#[cfg(test)]
#[macro_use]
extern crate hex_literal;
#[cfg(test)]
extern crate substrate_keyring as keyring;
#[cfg_attr(any(feature = "std", test), macro_use)]
extern crate substrate_primitives as primitives;

#[cfg(feature = "std")] pub mod genesismap;
pub mod system;

use rstd::prelude::*;
use codec::{Encode, Decode};

use runtime_api::runtime::*;
use runtime_primitives::traits::{BlindCheckable, BlakeTwo256, Block as BlockT, Extrinsic as ExtrinsicT};
use runtime_primitives::{ApplyResult, Ed25519Signature, transaction_validity::TransactionValidity};
use runtime_version::RuntimeVersion;
pub use primitives::hash::H256;
use primitives::AuthorityId;
#[cfg(any(feature = "std", test))]
use runtime_version::NativeVersion;

/// Test runtime version.
pub const VERSION: RuntimeVersion = RuntimeVersion {
	spec_name: ver_str!("test"),
	impl_name: ver_str!("parity-test"),
	authoring_version: 1,
	spec_version: 1,
	impl_version: 1,
	apis: apis_vec!([]),
};

fn version() -> RuntimeVersion {
	VERSION
}

/// Native version.
#[cfg(any(feature = "std", test))]
pub fn native_version() -> NativeVersion {
	NativeVersion {
		runtime_version: VERSION,
		can_author_with: Default::default(),
	}
}

/// Calls in transactions.
#[derive(Clone, PartialEq, Eq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct Transfer {
	pub from: AccountId,
	pub to: AccountId,
	pub amount: u64,
	pub nonce: u64,
}

/// Extrinsic for test-runtime.
#[derive(Clone, PartialEq, Eq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct Extrinsic {
	pub transfer: Transfer,
	pub signature: Ed25519Signature,
}

impl BlindCheckable for Extrinsic {
	type Checked = Self;

	fn check(self) -> Result<Self, &'static str> {
		if ::runtime_primitives::verify_encoded_lazy(&self.signature, &self.transfer, &self.transfer.from) {
			Ok(self)
		} else {
			Err("bad signature")
		}
	}
}

impl ExtrinsicT for Extrinsic {
	fn is_signed(&self) -> Option<bool> {
		Some(true)
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
/// The item of a block digest.
pub type DigestItem = runtime_primitives::generic::DigestItem<H256, u64>;
/// The digest of a block.
pub type Digest = runtime_primitives::generic::Digest<DigestItem>;
/// A test block.
pub type Block = runtime_primitives::generic::Block<Header, Extrinsic>;
/// A test block's header.
pub type Header = runtime_primitives::generic::Header<BlockNumber, BlakeTwo256, DigestItem>;

/// Run whatever tests we have.
pub fn run_tests(mut input: &[u8]) -> Vec<u8> {
	use runtime_io::print;

	print("run_tests...");
	let block = Block::decode(&mut input).unwrap();
	print("deserialised block.");
	let stxs = block.extrinsics.iter().map(Encode::encode).collect::<Vec<_>>();
	print("reserialised transactions.");
	[stxs.len() as u8].encode()
}

/// Changes trie configuration (optionally) used in tests.
pub fn changes_trie_config() -> primitives::ChangesTrieConfiguration {
	primitives::ChangesTrieConfiguration {
		digest_interval: 4,
		digest_levels: 2,
	}
}

mod test_api {
	decl_apis! {
		pub trait TestAPI {
			fn balance_of<AccountId>(id: AccountId) -> u64;
		}
	}
}

use test_api::runtime::TestAPI;

struct Runtime;

impl_apis! {
	impl Core<Block, AuthorityId> for Runtime {
		fn version() -> RuntimeVersion {
			version()
		}

		fn authorities() -> Vec<AuthorityId> {
			system::authorities()
		}

		fn execute_block(block: Block) {
			system::execute_block(block)
		}
	}

	impl TaggedTransactionQueue<Block, TransactionValidity> for Runtime {
		fn validate_transaction(utx: <Block as BlockT>::Extrinsic) -> TransactionValidity {
			system::validate_transaction(utx)
		}
	}

	impl BlockBuilder<Block, u32, u32, u32, u32> for Runtime {
		fn initialise_block(header: <Block as BlockT>::Header) {
			system::initialise_block(header)
		}

		fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic) -> ApplyResult {
			system::execute_transaction(extrinsic)
		}

		fn finalise_block() -> <Block as BlockT>::Header {
			system::finalise_block()
		}

		fn inherent_extrinsics(_data: u32) -> Vec<u32> {
			unimplemented!()
		}

		fn check_inherents(_block: Block, _data: u32) -> Result<(), u32> {
			unimplemented!()
		}

		fn random_seed() -> <Block as BlockT>::Hash {
			unimplemented!()
		}
	}

	impl TestAPI<AccountId> for Runtime {
		fn balance_of(id: AccountId) -> u64 {
			system::balance_of(id)
		}
	}
}
