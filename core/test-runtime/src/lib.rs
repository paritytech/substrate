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

#[cfg(feature = "std")] pub mod genesismap;
pub mod system;

use rstd::{prelude::*, marker::PhantomData};
use parity_codec::{Encode, Decode, Input};
use parity_codec_derive::{Encode, Decode};

use substrate_client::{
	runtime_api as client_api, block_builder::api as block_builder_api, decl_runtime_apis,
	impl_runtime_apis,
};
use runtime_primitives::{
	ApplyResult, Ed25519Signature, transaction_validity::TransactionValidity,
	create_runtime_str,
	traits::{
		BlindCheckable, BlakeTwo256, Block as BlockT, Extrinsic as ExtrinsicT,
		GetNodeBlockType, GetRuntimeBlockType,
	},
};
use runtime_version::RuntimeVersion;
pub use primitives::hash::H256;
use primitives::{Ed25519AuthorityId, OpaqueMetadata};
#[cfg(any(feature = "std", test))]
use runtime_version::NativeVersion;
use inherents::{CheckInherentsResult, InherentData};
use cfg_if::cfg_if;

/// Test runtime version.
pub const VERSION: RuntimeVersion = RuntimeVersion {
	spec_name: create_runtime_str!("test"),
	impl_name: create_runtime_str!("parity-test"),
	authoring_version: 1,
	spec_version: 1,
	impl_version: 1,
	apis: RUNTIME_API_VERSIONS,
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
pub enum Extrinsic {
	AuthoritiesChange(Vec<Ed25519AuthorityId>),
	Transfer(Transfer, Ed25519Signature),
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
		match self {
			Extrinsic::AuthoritiesChange(new_auth) => Ok(Extrinsic::AuthoritiesChange(new_auth)),
			Extrinsic::Transfer(transfer, signature) => {
				if runtime_primitives::verify_encoded_lazy(&signature, &transfer, &transfer.from) {
					Ok(Extrinsic::Transfer(transfer, signature))
				} else {
					Err(runtime_primitives::BAD_SIGNATURE)
				}
			},
		}
	}
}

impl ExtrinsicT for Extrinsic {
	fn is_signed(&self) -> Option<bool> {
		Some(true)
	}
}

impl Extrinsic {
	pub fn transfer(&self) -> &Transfer {
		match self {
			Extrinsic::Transfer(ref transfer, _) => transfer,
			_ => panic!("cannot convert to transfer ref"),
		}
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
pub type DigestItem = runtime_primitives::generic::DigestItem<H256, Ed25519AuthorityId>;
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

/// A type that can not be decoded.
#[derive(PartialEq)]
pub struct DecodeFails<B: BlockT> {
	_phantom: PhantomData<B>,
}

impl<B: BlockT> Encode for DecodeFails<B> {
	fn encode(&self) -> Vec<u8> {
		Vec::new()
	}
}

impl<B: BlockT> DecodeFails<B> {
	/// Create a new instance.
	pub fn new() -> DecodeFails<B> {
		DecodeFails {
			_phantom: Default::default(),
		}
	}
}

impl<B: BlockT> Decode for DecodeFails<B> {
	fn decode<I: Input>(_: &mut I) -> Option<Self> {
		// decoding always fails
		None
	}
}

cfg_if! {
	if #[cfg(feature = "std")] {
		decl_runtime_apis! {
			#[api_version(2)]
			pub trait TestAPI {
				/// Return the balance of the given account id.
				fn balance_of(id: AccountId) -> u64;
				/// A benchmkark function that adds one to the given value and returns the result.
				fn benchmark_add_one(val: &u64) -> u64;
				/// A benchmark function that adds one to each value in the given vector and returns the
				/// result.
				fn benchmark_vector_add_one(vec: &Vec<u64>) -> Vec<u64>;
				/// A function that always fails to convert a parameter between runtime and node.
				fn fail_convert_parameter(param: DecodeFails<Block>);
				/// A function that always fails to convert its return value between runtime and node.
				fn fail_convert_return_value() -> DecodeFails<Block>;
				/// A function for that the signature changed in version `2`.
				#[changed_in(2)]
				fn function_signature_changed() -> Vec<u64>;
				/// The new signature.
				fn function_signature_changed() -> u64;
				fn fail_on_native() -> u64;
				fn fail_on_wasm() -> u64;
				fn benchmark_indirect_call() -> u64;
				fn benchmark_direct_call() -> u64;
			}
		}
	} else {
		decl_runtime_apis! {
			pub trait TestAPI {
				/// Return the balance of the given account id.
				fn balance_of(id: AccountId) -> u64;
				/// A benchmkark function that adds one to the given value and returns the result.
				fn benchmark_add_one(val: &u64) -> u64;
				/// A benchmark function that adds one to each value in the given vector and returns the
				/// result.
				fn benchmark_vector_add_one(vec: &Vec<u64>) -> Vec<u64>;
				/// A function that always fails to convert a parameter between runtime and node.
				fn fail_convert_parameter(param: DecodeFails<Block>);
				/// A function that always fails to convert its return value between runtime and node.
				fn fail_convert_return_value() -> DecodeFails<Block>;
				/// In wasm we just emulate the old behavior.
				fn function_signature_changed() -> Vec<u64>;
				fn fail_on_native() -> u64;
				fn fail_on_wasm() -> u64;
				fn benchmark_indirect_call() -> u64;
				fn benchmark_direct_call() -> u64;
			}
		}
	}
}

pub struct Runtime;

impl GetNodeBlockType for Runtime {
	type NodeBlock = Block;
}

impl GetRuntimeBlockType for Runtime {
	type RuntimeBlock = Block;
}

/// Adds one to the given input and returns the final result.
#[inline(never)]
fn benchmark_add_one(i: u64) -> u64 {
	i + 1
}

/// A `Cell` that is tagged as sync, as we know that it is not modified by multiple threads.
#[cfg(not(feature = "std"))]
struct SyncCell<T>(rstd::cell::Cell<T>);
#[cfg(not(feature = "std"))]
unsafe impl<T> Sync for SyncCell<T> {}

/// The `benchmark_add_one` function as function pointer.
#[cfg(not(feature = "std"))]
static BENCHMARK_ADD_ONE: SyncCell<fn(u64) -> u64> = SyncCell(rstd::cell::Cell::new(benchmark_add_one));

cfg_if! {
	if #[cfg(feature = "std")] {
		impl_runtime_apis! {
			impl client_api::Core<Block> for Runtime {
				fn version() -> RuntimeVersion {
					version()
				}

				fn authorities() -> Vec<Ed25519AuthorityId> {
					system::authorities()
				}

				fn execute_block(block: Block) {
					system::execute_block(block)
				}

				fn initialise_block(header: &<Block as BlockT>::Header) {
					system::initialise_block(header)
				}
			}

			impl client_api::Metadata<Block> for Runtime {
				fn metadata() -> OpaqueMetadata {
					unimplemented!()
				}
			}

			impl client_api::TaggedTransactionQueue<Block> for Runtime {
				fn validate_transaction(utx: <Block as BlockT>::Extrinsic) -> TransactionValidity {
					system::validate_transaction(utx)
				}
			}

			impl block_builder_api::BlockBuilder<Block> for Runtime {
				fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic) -> ApplyResult {
					system::execute_transaction(extrinsic)
				}

				fn finalise_block() -> <Block as BlockT>::Header {
					system::finalise_block()
				}

				fn inherent_extrinsics(_data: InherentData) -> Vec<<Block as BlockT>::Extrinsic> {
					vec![]
				}

				fn check_inherents(_block: Block, _data: InherentData) -> CheckInherentsResult {
					CheckInherentsResult::new()
				}

				fn random_seed() -> <Block as BlockT>::Hash {
					unimplemented!()
				}
			}

			impl self::TestAPI<Block> for Runtime {
				fn balance_of(id: AccountId) -> u64 {
					system::balance_of(id)
				}

				fn benchmark_add_one(val: &u64) -> u64 {
					val + 1
				}

				fn benchmark_vector_add_one(vec: &Vec<u64>) -> Vec<u64> {
					let mut vec = vec.clone();
					vec.iter_mut().for_each(|v| *v += 1);
					vec
				}

				fn fail_convert_parameter(_: DecodeFails<Block>) {}

				fn fail_convert_return_value() -> DecodeFails<Block> {
					DecodeFails::new()
				}

				fn function_signature_changed() -> u64 {
					1
				}

				fn fail_on_native() -> u64 {
					panic!("Failing because we are on native")
				}
				fn fail_on_wasm() -> u64 {
					1
				}
				fn benchmark_indirect_call() -> u64 {
					let function = benchmark_add_one;
					(0..1000).fold(0, |p, i| p + function(i))
				}
				fn benchmark_direct_call() -> u64 {
					(0..1000).fold(0, |p, i| p + benchmark_add_one(i))
				}
			}

			impl consensus_aura::AuraApi<Block> for Runtime {
				fn slot_duration() -> u64 { 1 }
			}
		}
	} else {
		impl_runtime_apis! {
			impl client_api::Core<Block> for Runtime {
				fn version() -> RuntimeVersion {
					version()
				}

				fn authorities() -> Vec<Ed25519AuthorityId> {
					system::authorities()
				}

				fn execute_block(block: Block) {
					system::execute_block(block)
				}

				fn initialise_block(header: &<Block as BlockT>::Header) {
					system::initialise_block(header)
				}
			}

			impl client_api::Metadata<Block> for Runtime {
				fn metadata() -> OpaqueMetadata {
					unimplemented!()
				}
			}

			impl client_api::TaggedTransactionQueue<Block> for Runtime {
				fn validate_transaction(utx: <Block as BlockT>::Extrinsic) -> TransactionValidity {
					system::validate_transaction(utx)
				}
			}

			impl block_builder_api::BlockBuilder<Block> for Runtime {
				fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic) -> ApplyResult {
					system::execute_transaction(extrinsic)
				}

				fn finalise_block() -> <Block as BlockT>::Header {
					system::finalise_block()
				}

				fn inherent_extrinsics(_data: InherentData) -> Vec<<Block as BlockT>::Extrinsic> {
					vec![]
				}

				fn check_inherents(_block: Block, _data: InherentData) -> CheckInherentsResult {
					CheckInherentsResult::new()
				}

				fn random_seed() -> <Block as BlockT>::Hash {
					unimplemented!()
				}
			}

			impl self::TestAPI<Block> for Runtime {
				fn balance_of(id: AccountId) -> u64 {
					system::balance_of(id)
				}

				fn benchmark_add_one(val: &u64) -> u64 {
					val + 1
				}

				fn benchmark_vector_add_one(vec: &Vec<u64>) -> Vec<u64> {
					let mut vec = vec.clone();
					vec.iter_mut().for_each(|v| *v += 1);
					vec
				}

				fn fail_convert_parameter(_: DecodeFails<Block>) {}

				fn fail_convert_return_value() -> DecodeFails<Block> {
					DecodeFails::new()
				}

				fn function_signature_changed() -> Vec<u64> {
					let mut vec = Vec::new();
					vec.push(1);
					vec.push(2);
					vec
				}

				fn fail_on_native() -> u64 {
					1
				}

				fn fail_on_wasm() -> u64 {
					panic!("Failing because we are on wasm")
				}

				fn benchmark_indirect_call() -> u64 {
					(0..10000).fold(0, |p, i| p + BENCHMARK_ADD_ONE.0.get()(i))
				}

				fn benchmark_direct_call() -> u64 {
					(0..10000).fold(0, |p, i| p + benchmark_add_one(i))
				}
			}

			impl consensus_aura::AuraApi<Block> for Runtime {
				fn slot_duration() -> u64 { 1 }
			}
		}
	}
}
