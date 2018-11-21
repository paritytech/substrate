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

#[cfg(feature = "std")]
extern crate serde;

extern crate sr_std as rstd;
extern crate parity_codec as codec;
extern crate sr_primitives as runtime_primitives;

#[macro_use]
extern crate substrate_client as client;

#[macro_use]
extern crate srml_support as runtime_support;
#[macro_use]
extern crate parity_codec_derive;
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

use client::{runtime_api as client_api, block_builder::api as block_builder_api};
use runtime_primitives::traits::{
	BlindCheckable, BlakeTwo256, Block as BlockT, Extrinsic as ExtrinsicT, GetNodeBlockType,
	GetRuntimeBlockType
};
use runtime_primitives::{ApplyResult, Ed25519Signature, transaction_validity::TransactionValidity};
#[cfg(feature = "std")]
use runtime_primitives::generic::BlockId;
use runtime_version::RuntimeVersion;
pub use primitives::hash::H256;
use primitives::AuthorityId;
#[cfg(feature = "std")]
use primitives::OpaqueMetadata;
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
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Transfer {
	pub from: AccountId,
	pub to: AccountId,
	pub amount: u64,
	pub nonce: u64,
}

/// Extrinsic for test-runtime.
#[derive(Clone, PartialEq, Eq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Extrinsic {
	pub transfer: Transfer,
	pub signature: Ed25519Signature,
}

#[cfg(feature = "std")]
impl serde::Serialize for Extrinsic
{
	fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error> where S: ::serde::Serializer {
		self.using_encoded(|bytes| seq.serialize_bytes(bytes))
	}
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

pub mod test_api {
	decl_runtime_apis! {
		pub trait TestAPI {
			fn balance_of<AccountId>(id: AccountId) -> u64;
		}
	}
}

#[cfg(feature = "std")]
impl client::runtime_api::Core<Block> for RuntimeApi {
	fn version(&self, at: &BlockId<Block>) -> Result<RuntimeVersion, client::error::Error> {
		self.call_api_at(at, "version", &())
	}

	fn authorities(&self, at: &BlockId<Block>) -> Result<Vec<AuthorityId>, client::error::Error> {
		self.call_api_at(at, "authorities", &())
	}

	fn execute_block(&self, at: &BlockId<Block>, block: &Block) -> Result<(), client::error::Error> {
		self.call_api_at(at, "execute_block", block)
	}

	fn initialise_block(&self, at: &BlockId<Block>, header: &<Block as BlockT>::Header) -> Result<(), client::error::Error> {
		self.call_api_at(at, "initialise_block", header)
	}
}

#[cfg(feature = "std")]
impl client::block_builder::api::BlockBuilder<Block> for RuntimeApi {
	fn apply_extrinsic(&self, at: &BlockId<Block>, extrinsic: &<Block as BlockT>::Extrinsic) -> Result<ApplyResult, client::error::Error> {
		self.call_api_at(at, "apply_extrinsic", extrinsic)
	}

	fn finalise_block(&self, at: &BlockId<Block>) -> Result<<Block as BlockT>::Header, client::error::Error> {
		self.call_api_at(at, "finalise_block", &())
	}

	fn inherent_extrinsics<Inherent: Decode + Encode, Unchecked: Decode + Encode>(
		&self, at: &BlockId<Block>, inherent: &Inherent
	) -> Result<Vec<Unchecked>, client::error::Error> {
		self.call_api_at(at, "inherent_extrinsics", inherent)
	}

	fn check_inherents<Inherent: Decode + Encode, Error: Decode + Encode>(&self, at: &BlockId<Block>, block: &Block, inherent: &Inherent) -> Result<Result<(), Error>, client::error::Error> {
		self.call_api_at(at, "check_inherents", &(block, inherent))
	}

	fn random_seed(&self, at: &BlockId<Block>) -> Result<<Block as BlockT>::Hash, client::error::Error> {
		self.call_api_at(at, "random_seed", &())
	}
}

#[cfg(feature = "std")]
impl client::runtime_api::TaggedTransactionQueue<Block> for RuntimeApi {
	fn validate_transaction(
		&self,
		at: &BlockId<Block>,
		utx: &<Block as BlockT>::Extrinsic
	) -> Result<TransactionValidity, client::error::Error> {
		self.call_api_at(at, "validate_transaction", utx)
	}
}

#[cfg(feature = "std")]
impl client::runtime_api::Metadata<Block> for RuntimeApi {
	fn metadata(&self, at: &BlockId<Block>) -> Result<OpaqueMetadata, client::error::Error> {
		self.call_api_at(at, "metadata", &())
	}
}

#[cfg(feature = "std")]
impl test_api::TestAPI<Block> for RuntimeApi {
	fn balance_of<AccountId: Encode + Decode>(&self, at: &BlockId<Block>, id: &AccountId) -> Result<u64, client::error::Error> {
		self.call_api_at(at, "balance_of", id)
	}
}

pub struct Runtime;

impl GetNodeBlockType for Runtime {
	type NodeBlock = Block;
}

impl GetRuntimeBlockType for Runtime {
	type RuntimeBlock = Block;
}

impl_runtime_apis! {
	impl client_api::Core for Runtime {
		fn version() -> RuntimeVersion {
			version()
		}

		fn authorities() -> Vec<AuthorityId> {
			system::authorities()
		}

		fn execute_block(block: Block) {
			system::execute_block(block)
		}

		fn initialise_block(header: <Block as BlockT>::Header) {
			system::initialise_block(header)
		}
	}

	impl client_api::TaggedTransactionQueue for Runtime {
		fn validate_transaction(utx: <Block as BlockT>::Extrinsic) -> TransactionValidity {
			system::validate_transaction(utx)
		}
	}

	impl block_builder_api::BlockBuilder<u32, u32, u32, u32> for Runtime {
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

	impl self::test_api::TestAPI<AccountId> for Runtime {
		fn balance_of(id: AccountId) -> u64 {
			system::balance_of(id)
		}
	}
}
