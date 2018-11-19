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

use client::{runtime_api::runtime as client_api, block_builder::api::runtime as block_builder_api};
#[cfg(feature = "std")]
use client::runtime_api::ApiExt;
use runtime_primitives::traits::{BlindCheckable, BlakeTwo256, Block as BlockT, Extrinsic as ExtrinsicT};
#[cfg(feature = "std")]
use runtime_primitives::traits::ApiRef;
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
pub struct ClientWithApi {
	call: ::std::ptr::NonNull<client::runtime_api::CallApiAt<Block>>,
	commit_on_success: ::std::cell::RefCell<bool>,
	initialised_block: ::std::cell::RefCell<Option<BlockId<Block>>>,
	changes: ::std::cell::RefCell<client::runtime_api::OverlayedChanges>,
}

#[cfg(feature = "std")]
unsafe impl Send for ClientWithApi {}
#[cfg(feature = "std")]
unsafe impl Sync for ClientWithApi {}

#[cfg(feature = "std")]
impl ApiExt for ClientWithApi {
	fn map_api_result<F: FnOnce(&Self) -> Result<R, E>, R, E>(&self, map_call: F) -> Result<R, E> {
		*self.commit_on_success.borrow_mut() = false;
		let res = map_call(self);
		*self.commit_on_success.borrow_mut() = true;

		self.commit_on_ok(&res);

		res
	}
}

#[cfg(feature = "std")]
impl client::runtime_api::ConstructRuntimeApi<Block> for ClientWithApi {
	fn construct_runtime_api<'a, T: client::runtime_api::CallApiAt<Block>>(call: &'a T) -> ApiRef<'a, Self> {
		ClientWithApi {
			call: unsafe {
				::std::ptr::NonNull::new_unchecked(
					::std::mem::transmute(
						call as &client::runtime_api::CallApiAt<Block>
					)
				)
			},
			commit_on_success: true.into(),
			initialised_block: None.into(),
			changes: Default::default(),
		}.into()
	}
}

#[cfg(feature = "std")]
impl ClientWithApi {
	fn call_api_at<A: Encode, R: Decode>(
		&self,
		at: &BlockId<Block>,
		function: &'static str,
		args: &A
	) -> client::error::Result<R> {
		let res = unsafe {
			self.call.as_ref().call_api_at(
				at,
				function,
				args.encode(),
				&mut *self.changes.borrow_mut(),
				&mut *self.initialised_block.borrow_mut()
			).and_then(|r|
				R::decode(&mut &r[..])
					.ok_or_else(||
						client::error::ErrorKind::CallResultDecode(function).into()
					)
			)
		};

		self.commit_on_ok(&res);
		res
	}

	fn commit_on_ok<R, E>(&self, res: &Result<R, E>) {
		if *self.commit_on_success.borrow() {
			if res.is_err() {
				self.changes.borrow_mut().discard_prospective();
			} else {
				self.changes.borrow_mut().commit_prospective();
			}
		}
	}
}

#[cfg(feature = "std")]
impl client::runtime_api::Core<Block> for ClientWithApi {
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
impl client::block_builder::api::BlockBuilder<Block> for ClientWithApi {
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
impl client::runtime_api::TaggedTransactionQueue<Block> for ClientWithApi {
	fn validate_transaction(
		&self,
		at: &BlockId<Block>,
		utx: &<Block as BlockT>::Extrinsic
	) -> Result<TransactionValidity, client::error::Error> {
		self.call_api_at(at, "validate_transaction", utx)
	}
}

#[cfg(feature = "std")]
impl client::runtime_api::Metadata<Block> for ClientWithApi {
	fn metadata(&self, at: &BlockId<Block>) -> Result<OpaqueMetadata, client::error::Error> {
		self.call_api_at(at, "metadata", &())
	}
}

#[cfg(feature = "std")]
impl test_api::TestAPI<Block> for ClientWithApi {
	fn balance_of<AccountId: Encode + Decode>(&self, at: &BlockId<Block>, id: &AccountId) -> Result<u64, client::error::Error> {
		self.call_api_at(at, "balance_of", id)
	}
}

struct Runtime;

impl_runtime_apis! {
	impl client_api::Core<Block> for Runtime {
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

	impl client_api::TaggedTransactionQueue<Block> for Runtime {
		fn validate_transaction(utx: <Block as BlockT>::Extrinsic) -> TransactionValidity {
			system::validate_transaction(utx)
		}
	}

	impl block_builder_api::BlockBuilder<Block, u32, u32, u32, u32> for Runtime {
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

	impl self::test_api::runtime::TestAPI<AccountId> for Runtime {
		fn balance_of(id: AccountId) -> u64 {
			system::balance_of(id)
		}
	}
}
