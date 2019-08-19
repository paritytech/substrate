// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
pub mod genesismap;
pub mod system;

use rstd::{prelude::*, marker::PhantomData};
use codec::{Encode, Decode, Input, Error};

use primitives::{Blake2Hasher, OpaqueMetadata};
use app_crypto::{ed25519, sr25519, RuntimeAppPublic};
pub use app_crypto;
use trie_db::{TrieMut, Trie};
use substrate_trie::PrefixedMemoryDB;
use substrate_trie::trie_types::{TrieDB, TrieDBMut};

use substrate_client::{
	runtime_api as client_api, block_builder::api as block_builder_api, decl_runtime_apis,
	impl_runtime_apis,
};
use sr_primitives::{
	ApplyResult, create_runtime_str, Perbill, impl_opaque_keys,
	transaction_validity::{TransactionValidity, ValidTransaction},
	traits::{
		BlindCheckable, BlakeTwo256, Block as BlockT, Extrinsic as ExtrinsicT,
		GetNodeBlockType, GetRuntimeBlockType, Verify, IdentityLookup,
	},
};
use runtime_version::RuntimeVersion;
pub use primitives::{hash::H256, crypto::key_types};
#[cfg(any(feature = "std", test))]
use runtime_version::NativeVersion;
use runtime_support::{impl_outer_origin, parameter_types};
use inherents::{CheckInherentsResult, InherentData};
use cfg_if::cfg_if;

// Ensure Babe and Aura use the same crypto to simplify things a bit.
pub use babe_primitives::AuthorityId;
pub type AuraId = aura_primitives::sr25519::AuthorityId;

// Inlucde the WASM binary
#[cfg(feature = "std")]
include!(concat!(env!("OUT_DIR"), "/wasm_binary.rs"));

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

impl Transfer {
	/// Convert into a signed extrinsic.
	#[cfg(feature = "std")]
	pub fn into_signed_tx(self) -> Extrinsic {
		let signature = keyring::AccountKeyring::from_public(&self.from)
			.expect("Creates keyring from public key.").sign(&self.encode()).into();
		Extrinsic::Transfer(self, signature)
	}
}

/// Extrinsic for test-runtime.
#[derive(Clone, PartialEq, Eq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum Extrinsic {
	AuthoritiesChange(Vec<AuthorityId>),
	Transfer(Transfer, AccountSignature),
	IncludeData(Vec<u8>),
	StorageChange(Vec<u8>, Option<Vec<u8>>),
}

#[cfg(feature = "std")]
impl serde::Serialize for Extrinsic {
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
				if sr_primitives::verify_encoded_lazy(&signature, &transfer, &transfer.from) {
					Ok(Extrinsic::Transfer(transfer, signature))
				} else {
					Err(sr_primitives::BAD_SIGNATURE)
				}
			},
			Extrinsic::IncludeData(_) => Err(sr_primitives::BAD_SIGNATURE),
			Extrinsic::StorageChange(key, value) => Ok(Extrinsic::StorageChange(key, value)),
		}
	}
}

impl ExtrinsicT for Extrinsic {
	type Call = Extrinsic;

	fn is_signed(&self) -> Option<bool> {
		if let Extrinsic::IncludeData(_) = *self {
			Some(false)
		} else {
			Some(true)
		}
	}

	fn new_unsigned(call: Self::Call) -> Option<Self> {
		Some(call)
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

/// The signature type used by accounts/transactions.
pub type AccountSignature = sr25519::Signature;
/// An identifier for an account on this system.
pub type AccountId = <AccountSignature as Verify>::Signer;
/// A simple hash type for all our hashing.
pub type Hash = H256;
/// The block number type used in this runtime.
pub type BlockNumber = u64;
/// Index of a transaction.
pub type Index = u64;
/// The item of a block digest.
pub type DigestItem = sr_primitives::generic::DigestItem<H256>;
/// The digest of a block.
pub type Digest = sr_primitives::generic::Digest<H256>;
/// A test block.
pub type Block = sr_primitives::generic::Block<Header, Extrinsic>;
/// A test block's header.
pub type Header = sr_primitives::generic::Header<BlockNumber, BlakeTwo256>;

/// Run whatever tests we have.
pub fn run_tests(mut input: &[u8]) -> Vec<u8> {
	use runtime_io::print;

	print("run_tests...");
	let block = Block::decode(&mut input).unwrap();
	print("deserialized block.");
	let stxs = block.extrinsics.iter().map(Encode::encode).collect::<Vec<_>>();
	print("reserialized transactions.");
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

impl<B: BlockT> codec::EncodeLike for DecodeFails<B> {}

impl<B: BlockT> DecodeFails<B> {
	/// Create a new instance.
	pub fn new() -> DecodeFails<B> {
		DecodeFails {
			_phantom: Default::default(),
		}
	}
}

impl<B: BlockT> Decode for DecodeFails<B> {
	fn decode<I: Input>(_: &mut I) -> Result<Self, Error> {
		Err("DecodeFails always fails".into())
	}
}

cfg_if! {
	if #[cfg(feature = "std")] {
		decl_runtime_apis! {
			#[api_version(2)]
			pub trait TestAPI {
				/// Return the balance of the given account id.
				fn balance_of(id: AccountId) -> u64;
				/// A benchmark function that adds one to the given value and returns the result.
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
				/// trie no_std testing
				fn use_trie() -> u64;
				fn benchmark_indirect_call() -> u64;
				fn benchmark_direct_call() -> u64;
				fn returns_mutable_static() -> u64;
				fn allocates_huge_stack_array(trap: bool) -> Vec<u8>;
				fn vec_with_capacity(size: u32) -> Vec<u8>;
				/// Returns the initialized block number.
				fn get_block_number() -> u64;
				/// Takes and returns the initialized block number.
				fn take_block_number() -> Option<u64>;
				/// Returns if no block was initialized.
				#[skip_initialize_block]
				fn without_initialize_block() -> bool;
				/// Test that `ed25519` crypto works in the runtime.
				///
				/// Returns the signature generated for the message `ed25519` and the public key.
				fn test_ed25519_crypto() -> (ed25519::AppSignature, ed25519::AppPublic);
				/// Test that `sr25519` crypto works in the runtime.
				///
				/// Returns the signature generated for the message `sr25519`.
				fn test_sr25519_crypto() -> (sr25519::AppSignature, sr25519::AppPublic);
			}
		}
	} else {
		decl_runtime_apis! {
			pub trait TestAPI {
				/// Return the balance of the given account id.
				fn balance_of(id: AccountId) -> u64;
				/// A benchmark function that adds one to the given value and returns the result.
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
				/// trie no_std testing
				fn use_trie() -> u64;
				fn benchmark_indirect_call() -> u64;
				fn benchmark_direct_call() -> u64;
				fn returns_mutable_static() -> u64;
				fn allocates_huge_stack_array(trap: bool) -> Vec<u8>;
				fn vec_with_capacity(size: u32) -> Vec<u8>;
				/// Returns the initialized block number.
				fn get_block_number() -> u64;
				/// Takes and returns the initialized block number.
				fn take_block_number() -> Option<u64>;
				/// Returns if no block was initialized.
				#[skip_initialize_block]
				fn without_initialize_block() -> bool;
				/// Test that `ed25519` crypto works in the runtime.
				///
				/// Returns the signature generated for the message `ed25519` and the public key.
				fn test_ed25519_crypto() -> (ed25519::AppSignature, ed25519::AppPublic);
				/// Test that `sr25519` crypto works in the runtime.
				///
				/// Returns the signature generated for the message `sr25519`.
				fn test_sr25519_crypto() -> (sr25519::AppSignature, sr25519::AppPublic);
			}
		}
	}
}

#[derive(Clone, Eq, PartialEq)]
pub struct Runtime;

impl GetNodeBlockType for Runtime {
	type NodeBlock = Block;
}

impl GetRuntimeBlockType for Runtime {
	type RuntimeBlock = Block;
}

impl_outer_origin!{
	pub enum Origin for Runtime where system = srml_system {}
}

#[derive(Clone, Encode, Decode, Eq, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Event;

impl From<srml_system::Event> for Event {
	fn from(_evt: srml_system::Event) -> Self {
		unimplemented!("Not required in tests!")
	}
}

parameter_types! {
	pub const BlockHashCount: BlockNumber = 250;
	pub const MinimumPeriod: u64 = 5;
	pub const MaximumBlockWeight: u32 = 4 * 1024 * 1024;
	pub const MaximumBlockLength: u32 = 4 * 1024 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::from_percent(75);
}

impl srml_system::Trait for Runtime {
	type Origin = Origin;
	type Call = Extrinsic;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type WeightMultiplierUpdate = ();
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
}

impl srml_timestamp::Trait for Runtime {
	/// A timestamp: milliseconds since the unix epoch.
	type Moment = u64;
	type OnTimestampSet = ();
	type MinimumPeriod = MinimumPeriod;
}

parameter_types! {
	pub const EpochDuration: u64 = 6;
	pub const ExpectedBlockTime: u64 = 10_000;
}

impl srml_babe::Trait for Runtime {
	type EpochDuration = EpochDuration;
	type ExpectedBlockTime = ExpectedBlockTime;
}

/// Adds one to the given input and returns the final result.
#[inline(never)]
fn benchmark_add_one(i: u64) -> u64 {
	i + 1
}

/// The `benchmark_add_one` function as function pointer.
#[cfg(not(feature = "std"))]
static BENCHMARK_ADD_ONE: runtime_io::ExchangeableFunction<fn(u64) -> u64> = runtime_io::ExchangeableFunction::new(benchmark_add_one);

fn code_using_trie() -> u64 {
	let pairs = [
		(b"0103000000000000000464".to_vec(), b"0400000000".to_vec()),
		(b"0103000000000000000469".to_vec(), b"0401000000".to_vec()),
	].to_vec();

	let mut mdb = PrefixedMemoryDB::default();
	let mut root = rstd::default::Default::default();
	let _ = {
		let v = &pairs;
		let mut t = TrieDBMut::<Blake2Hasher>::new(&mut mdb, &mut root);
		for i in 0..v.len() {
			let key: &[u8]= &v[i].0;
			let val: &[u8] = &v[i].1;
			if !t.insert(key, val).is_ok() {
				return 101;
			}
		}
		t
	};

	if let Ok(trie) = TrieDB::<Blake2Hasher>::new(&mdb, &root) {
		if let Ok(iter) = trie.iter() {
			let mut iter_pairs = Vec::new();
			for pair in iter {
				if let Ok((key, value)) = pair {
					iter_pairs.push((key, value.to_vec()));
				}
			}
			iter_pairs.len() as u64
		} else { 102 }
	} else { 103 }
}

impl_opaque_keys! {
	pub struct SessionKeys {
		#[id(key_types::ED25519)]
		pub ed25519: ed25519::AppPublic,
		#[id(key_types::SR25519)]
		pub sr25519: sr25519::AppPublic,
	}
}

#[cfg(not(feature = "std"))]
/// Mutable static variables should be always observed to have
/// the initialized value at the start of a runtime call.
static mut MUTABLE_STATIC: u64 = 32;

cfg_if! {
	if #[cfg(feature = "std")] {
		impl_runtime_apis! {
			impl client_api::Core<Block> for Runtime {
				fn version() -> RuntimeVersion {
					version()
				}

				fn execute_block(block: Block) {
					system::execute_block(block)
				}

				fn initialize_block(header: &<Block as BlockT>::Header) {
					system::initialize_block(header)
				}
			}

			impl client_api::Metadata<Block> for Runtime {
				fn metadata() -> OpaqueMetadata {
					unimplemented!()
				}
			}

			impl client_api::TaggedTransactionQueue<Block> for Runtime {
				fn validate_transaction(utx: <Block as BlockT>::Extrinsic) -> TransactionValidity {
					if let Extrinsic::IncludeData(data) = utx {
						return TransactionValidity::Valid(ValidTransaction {
							priority: data.len() as u64,
							requires: vec![],
							provides: vec![data],
							longevity: 1,
							propagate: false,
						});
					}

					system::validate_transaction(utx)
				}
			}

			impl block_builder_api::BlockBuilder<Block> for Runtime {
				fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic) -> ApplyResult {
					system::execute_transaction(extrinsic)
				}

				fn finalize_block() -> <Block as BlockT>::Header {
					system::finalize_block()
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

				fn use_trie() -> u64 {
					code_using_trie()
				}

				fn benchmark_indirect_call() -> u64 {
					let function = benchmark_add_one;
					(0..1000).fold(0, |p, i| p + function(i))
				}
				fn benchmark_direct_call() -> u64 {
					(0..1000).fold(0, |p, i| p + benchmark_add_one(i))
				}

				fn returns_mutable_static() -> u64 {
					unimplemented!("is not expected to be invoked from non-wasm builds");
				}

				fn allocates_huge_stack_array(_trap: bool) -> Vec<u8> {
					unimplemented!("is not expected to be invoked from non-wasm builds");
				}

				fn vec_with_capacity(_size: u32) -> Vec<u8> {
					unimplemented!("is not expected to be invoked from non-wasm builds");
				}

				fn get_block_number() -> u64 {
					system::get_block_number().expect("Block number is initialized")
				}

				fn without_initialize_block() -> bool {
					system::get_block_number().is_none()
				}

				fn take_block_number() -> Option<u64> {
					system::take_block_number()
				}

				fn test_ed25519_crypto() -> (ed25519::AppSignature, ed25519::AppPublic) {
					test_ed25519_crypto()
				}

				fn test_sr25519_crypto() -> (sr25519::AppSignature, sr25519::AppPublic) {
					test_sr25519_crypto()
				}
			}

			impl aura_primitives::AuraApi<Block, AuraId> for Runtime {
				fn slot_duration() -> u64 { 1000 }
				fn authorities() -> Vec<AuraId> {
					system::authorities().into_iter().map(|a| {
						let authority: sr25519::Public = a.into();
						AuraId::from(authority)
					}).collect()
				}
			}

			impl babe_primitives::BabeApi<Block> for Runtime {
				fn startup_data() -> babe_primitives::BabeConfiguration {
					babe_primitives::BabeConfiguration {
						median_required_blocks: 0,
						slot_duration: 3000,
						c: (3, 10),
					}
				}

				fn epoch() -> babe_primitives::Epoch {
					let authorities = system::authorities();
					let authorities: Vec<_> = authorities.into_iter().map(|x|(x, 1)).collect();

					babe_primitives::Epoch {
						start_slot: <srml_babe::Module<Runtime>>::epoch_start_slot(),
						authorities,
						randomness: <srml_babe::Module<Runtime>>::randomness(),
						epoch_index: <srml_babe::Module<Runtime>>::epoch_index(),
						duration: EpochDuration::get(),
						secondary_slots: <srml_babe::Module<Runtime>>::secondary_slots().0,
					}
				}
			}

			impl offchain_primitives::OffchainWorkerApi<Block> for Runtime {
				fn offchain_worker(block: u64) {
					let ex = Extrinsic::IncludeData(block.encode());
					runtime_io::submit_transaction(&ex).unwrap();
				}
			}

			impl session::SessionKeys<Block> for Runtime {
				fn generate_session_keys(_: Option<Vec<u8>>) -> Vec<u8> {
					SessionKeys::generate(None)
				}
			}
		}
	} else {
		impl_runtime_apis! {
			impl client_api::Core<Block> for Runtime {
				fn version() -> RuntimeVersion {
					version()
				}

				fn execute_block(block: Block) {
					system::execute_block(block)
				}

				fn initialize_block(header: &<Block as BlockT>::Header) {
					system::initialize_block(header)
				}
			}

			impl client_api::Metadata<Block> for Runtime {
				fn metadata() -> OpaqueMetadata {
					unimplemented!()
				}
			}

			impl client_api::TaggedTransactionQueue<Block> for Runtime {
				fn validate_transaction(utx: <Block as BlockT>::Extrinsic) -> TransactionValidity {
					if let Extrinsic::IncludeData(data) = utx {
						return TransactionValidity::Valid(ValidTransaction{
							priority: data.len() as u64,
							requires: vec![],
							provides: vec![data],
							longevity: 1,
							propagate: false,
						});
					}

					system::validate_transaction(utx)
				}
			}

			impl block_builder_api::BlockBuilder<Block> for Runtime {
				fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic) -> ApplyResult {
					system::execute_transaction(extrinsic)
				}

				fn finalize_block() -> <Block as BlockT>::Header {
					system::finalize_block()
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

				fn use_trie() -> u64 {
					code_using_trie()
				}

				fn benchmark_indirect_call() -> u64 {
					(0..10000).fold(0, |p, i| p + BENCHMARK_ADD_ONE.get()(i))
				}

				fn benchmark_direct_call() -> u64 {
					(0..10000).fold(0, |p, i| p + benchmark_add_one(i))
				}

				fn returns_mutable_static() -> u64 {
					unsafe {
						MUTABLE_STATIC += 1;
						MUTABLE_STATIC
					}
				}

				fn allocates_huge_stack_array(trap: bool) -> Vec<u8> {
					// Allocate a stack frame that is approx. 75% of the stack (assuming it is 1MB).
					// This will just decrease (stacks in wasm32-u-u grow downwards) the stack
					// pointer. This won't trap on the current compilers.
					let mut data = [0u8; 1024 * 768];

					// Then make sure we actually write something to it.
					//
					// If:
					// 1. the stack area is placed at the beginning of the linear memory space, and
					// 2. the stack pointer points to out-of-bounds area, and
					// 3. a write is performed around the current stack pointer.
					//
					// then a trap should happen.
					//
					for (i, v) in data.iter_mut().enumerate() {
						*v = i as u8; // deliberate truncation
					}

					if trap {
						// There is a small chance of this to be pulled up in theory. In practice
						// the probability of that is rather low.
						panic!()
					}

					data.to_vec()
				}

				fn vec_with_capacity(size: u32) -> Vec<u8> {
					Vec::with_capacity(size as usize)
				}

				fn get_block_number() -> u64 {
					system::get_block_number().expect("Block number is initialized")
				}

				fn without_initialize_block() -> bool {
					system::get_block_number().is_none()
				}

				fn take_block_number() -> Option<u64> {
					system::take_block_number()
				}

				fn test_ed25519_crypto() -> (ed25519::AppSignature, ed25519::AppPublic) {
					test_ed25519_crypto()
				}

				fn test_sr25519_crypto() -> (sr25519::AppSignature, sr25519::AppPublic) {
					test_sr25519_crypto()
				}
			}

			impl aura_primitives::AuraApi<Block, AuraId> for Runtime {
				fn slot_duration() -> u64 { 1000 }
				fn authorities() -> Vec<AuraId> {
					system::authorities().into_iter().map(|a| {
						let authority: sr25519::Public = a.into();
						AuraId::from(authority)
					}).collect()
				}
			}

			impl babe_primitives::BabeApi<Block> for Runtime {
				fn startup_data() -> babe_primitives::BabeConfiguration {
					babe_primitives::BabeConfiguration {
						median_required_blocks: 0,
						slot_duration: 1000,
						c: (3, 10),
					}
				}

				fn epoch() -> babe_primitives::Epoch {
					let authorities = system::authorities();
					let authorities: Vec<_> = authorities.into_iter().map(|x|(x, 1)).collect();

					babe_primitives::Epoch {
						start_slot: <srml_babe::Module<Runtime>>::epoch_start_slot(),
						authorities,
						randomness: <srml_babe::Module<Runtime>>::randomness(),
						epoch_index: <srml_babe::Module<Runtime>>::epoch_index(),
						duration: EpochDuration::get(),
						secondary_slots: <srml_babe::Module<Runtime>>::secondary_slots().0,
					}
				}
			}

			impl offchain_primitives::OffchainWorkerApi<Block> for Runtime {
				fn offchain_worker(block: u64) {
					let ex = Extrinsic::IncludeData(block.encode());
					runtime_io::submit_transaction(&ex).unwrap()
				}
			}

			impl session::SessionKeys<Block> for Runtime {
				fn generate_session_keys(_: Option<Vec<u8>>) -> Vec<u8> {
					SessionKeys::generate(None)
				}
			}
		}
	}
}

fn test_ed25519_crypto() -> (ed25519::AppSignature, ed25519::AppPublic) {
	let public0 = ed25519::AppPublic::generate_pair(None);
	let public1 = ed25519::AppPublic::generate_pair(None);
	let public2 = ed25519::AppPublic::generate_pair(None);

	let all = ed25519::AppPublic::all();
	assert!(all.contains(&public0));
	assert!(all.contains(&public1));
	assert!(all.contains(&public2));

	let signature = public0.sign(&"ed25519").expect("Generates a valid `ed25519` signature.");
	assert!(public0.verify(&"ed25519", &signature));
	(signature, public0)
}

fn test_sr25519_crypto() -> (sr25519::AppSignature, sr25519::AppPublic) {
	let public0 = sr25519::AppPublic::generate_pair(None);
	let public1 = sr25519::AppPublic::generate_pair(None);
	let public2 = sr25519::AppPublic::generate_pair(None);

	let all = sr25519::AppPublic::all();
	assert!(all.contains(&public0));
	assert!(all.contains(&public1));
	assert!(all.contains(&public2));

	let signature = public0.sign(&"sr25519").expect("Generates a valid `sr25519` signature.");
	assert!(public0.verify(&"sr25519", &signature));
	(signature, public0)
}

#[cfg(test)]
mod tests {
	use substrate_test_runtime_client::{
		prelude::*,
		consensus::BlockOrigin,
		DefaultTestClientBuilderExt, TestClientBuilder,
		runtime::TestAPI,
	};
	use sr_primitives::{
		generic::BlockId,
		traits::ProvideRuntimeApi,
	};
	use primitives::storage::well_known_keys::HEAP_PAGES;
	use state_machine::ExecutionStrategy;
	use codec::Encode;

	#[test]
	fn returns_mutable_static() {
		let client = TestClientBuilder::new().set_execution_strategy(ExecutionStrategy::AlwaysWasm).build();
		let runtime_api = client.runtime_api();
		let block_id = BlockId::Number(client.info().chain.best_number);

		let ret = runtime_api.returns_mutable_static(&block_id).unwrap();
		assert_eq!(ret, 33);

		// We expect that every invocation will need to return the initial
		// value plus one. If the value increases more than that then it is
		// a sign that the wasm runtime preserves the memory content.
		let ret = runtime_api.returns_mutable_static(&block_id).unwrap();
		assert_eq!(ret, 33);
	}

	// If we didn't restore the wasm instance properly, on a trap the stack pointer would not be
	// returned to its initial value and thus the stack space is going to be leaked.
	//
	// See https://github.com/paritytech/substrate/issues/2967 for details
	#[test]
	fn restoration_of_globals() {
		// Allocate 32 pages (of 65536 bytes) which gives the runtime 2048KB of heap to operate on
		// (plus some additional space unused from the initial pages requested by the wasm runtime
		// module).
		//
		// The fixture performs 2 allocations of 768KB and this theoretically gives 1536KB, however, due
		// to our allocator algorithm there are inefficiencies.
		const REQUIRED_MEMORY_PAGES: u64 = 32;

		let client = TestClientBuilder::new()
			.set_execution_strategy(ExecutionStrategy::AlwaysWasm)
			.set_heap_pages(REQUIRED_MEMORY_PAGES)
			.build();
		let runtime_api = client.runtime_api();
		let block_id = BlockId::Number(client.info().chain.best_number);

		// On the first invocation we allocate approx. 768KB (75%) of stack and then trap.
		let ret = runtime_api.allocates_huge_stack_array(&block_id, true);
		assert!(ret.is_err());

		// On the second invocation we allocate yet another 768KB (75%) of stack
		let ret = runtime_api.allocates_huge_stack_array(&block_id, false);
		assert!(ret.is_ok());
	}

	#[test]
	fn heap_pages_is_respected() {
		// This tests that the on-chain HEAP_PAGES parameter is respected.

		// Create a client devoting only 8 pages of wasm memory. This gives us ~512k of heap memory.
		let client = TestClientBuilder::new()
			.set_execution_strategy(ExecutionStrategy::AlwaysWasm)
			.set_heap_pages(8)
			.build();
		let runtime_api = client.runtime_api();
		let block_id = BlockId::Number(client.info().chain.best_number);

		// Try to allocate 1024k of memory on heap. This is going to fail since it is twice larger
		// than the heap.
		let ret = runtime_api.vec_with_capacity(&block_id, 1048576);
		assert!(ret.is_err());

		// Create a block that sets the `:heap_pages` to 32 pages of memory which corresponds to
		// ~2048k of heap memory.
		let new_block_id = {
			let mut builder = client.new_block(Default::default()).unwrap();
			builder.push_storage_change(HEAP_PAGES.to_vec(), Some(32u64.encode())).unwrap();
			let block = builder.bake().unwrap();
			let hash = block.header.hash();
			client.import(BlockOrigin::Own, block).unwrap();
			BlockId::Hash(hash)
		};

		// Allocation of 1024k while having ~2048k should succeed.
		let ret = runtime_api.vec_with_capacity(&new_block_id, 1048576);
		assert!(ret.is_ok());
	}
}
