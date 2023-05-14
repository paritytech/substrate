// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! The Substrate runtime. This can be compiled with `#[no_std]`, ready for Wasm.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
pub mod extrinsic;
#[cfg(feature = "std")]
pub mod genesismap;
pub mod substrate_test_pallet;

use codec::{Decode, Encode};
use frame_support::{
	construct_runtime,
	dispatch::DispatchClass,
	parameter_types,
	traits::{ConstU32, ConstU64},
	weights::{
		constants::{BlockExecutionWeight, ExtrinsicBaseWeight, WEIGHT_REF_TIME_PER_SECOND},
		Weight,
	},
};
use frame_system::{
	limits::{BlockLength, BlockWeights},
	CheckNonce, CheckWeight,
};
use scale_info::TypeInfo;
use sp_std::prelude::*;

use sp_application_crypto::{ecdsa, ed25519, sr25519, RuntimeAppPublic};
use sp_core::{OpaqueMetadata, RuntimeDebug};
use sp_trie::{
	trie_types::{TrieDBBuilder, TrieDBMutBuilderV1},
	PrefixedMemoryDB, StorageProof,
};
use trie_db::{Trie, TrieMut};

use sp_api::{decl_runtime_apis, impl_runtime_apis};
pub use sp_core::hash::H256;
use sp_inherents::{CheckInherentsResult, InherentData};
use sp_runtime::{
	create_runtime_str, impl_opaque_keys,
	traits::{BlakeTwo256, Block as BlockT, DispatchInfoOf, NumberFor, Verify},
	transaction_validity::{TransactionSource, TransactionValidity, TransactionValidityError},
	ApplyExtrinsicResult, Perbill,
};
#[cfg(any(feature = "std", test))]
use sp_version::NativeVersion;
use sp_version::RuntimeVersion;

// Ensure Babe and Aura use the same crypto to simplify things a bit.
pub use sp_consensus_babe::{AllowedSlots, AuthorityId, BabeEpochConfiguration, Slot};

pub use pallet_balances::Call as BalancesCall;

pub type AuraId = sp_consensus_aura::sr25519::AuthorityId;

#[cfg(feature = "std")]
pub use extrinsic::{ExtrinsicBuilder, Transfer};

const LOG_TARGET: &str = "substrate-test-runtime";

// Include the WASM binary
#[cfg(feature = "std")]
include!(concat!(env!("OUT_DIR"), "/wasm_binary.rs"));

#[cfg(feature = "std")]
pub mod wasm_binary_logging_disabled {
	include!(concat!(env!("OUT_DIR"), "/wasm_binary_logging_disabled.rs"));
}

/// Wasm binary unwrapped. If built with `SKIP_WASM_BUILD`, the function panics.
#[cfg(feature = "std")]
pub fn wasm_binary_unwrap() -> &'static [u8] {
	WASM_BINARY.expect(
		"Development wasm binary is not available. Testing is only supported with the flag \
		 disabled.",
	)
}

/// Wasm binary unwrapped. If built with `SKIP_WASM_BUILD`, the function panics.
#[cfg(feature = "std")]
pub fn wasm_binary_logging_disabled_unwrap() -> &'static [u8] {
	wasm_binary_logging_disabled::WASM_BINARY.expect(
		"Development wasm binary is not available. Testing is only supported with the flag \
		 disabled.",
	)
}

/// Test runtime version.
#[sp_version::runtime_version]
pub const VERSION: RuntimeVersion = RuntimeVersion {
	spec_name: create_runtime_str!("test"),
	impl_name: create_runtime_str!("parity-test"),
	authoring_version: 1,
	spec_version: 2,
	impl_version: 2,
	apis: RUNTIME_API_VERSIONS,
	transaction_version: 1,
	state_version: 1,
};

fn version() -> RuntimeVersion {
	VERSION
}

/// Native version.
#[cfg(any(feature = "std", test))]
pub fn native_version() -> NativeVersion {
	NativeVersion { runtime_version: VERSION, can_author_with: Default::default() }
}

/// Transfer data extracted from Extrinsic containing `Balances::transfer_allow_death`.
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, TypeInfo)]
pub struct TransferData {
	pub from: AccountId,
	pub to: AccountId,
	pub amount: Balance,
	pub nonce: Index,
}

/// The address format for describing accounts.
pub type Address = sp_core::sr25519::Public;
pub type Signature = sr25519::Signature;
#[cfg(feature = "std")]
pub type Pair = sp_core::sr25519::Pair;

/// The SignedExtension to the basic transaction logic.
pub type SignedExtra = (CheckNonce<Runtime>, CheckWeight<Runtime>, CheckSubstrateCall);
/// The payload being signed in transactions.
pub type SignedPayload = sp_runtime::generic::SignedPayload<RuntimeCall, SignedExtra>;
/// Unchecked extrinsic type as expected by this runtime.
pub type Extrinsic =
	sp_runtime::generic::UncheckedExtrinsic<Address, RuntimeCall, Signature, SignedExtra>;

/// An identifier for an account on this system.
pub type AccountId = <Signature as Verify>::Signer;
/// A simple hash type for all our hashing.
pub type Hash = H256;
/// The hashing algorithm used.
pub type Hashing = BlakeTwo256;
/// The block number type used in this runtime.
pub type BlockNumber = u64;
/// Index of a transaction.
pub type Index = u64;
/// The item of a block digest.
pub type DigestItem = sp_runtime::generic::DigestItem;
/// The digest of a block.
pub type Digest = sp_runtime::generic::Digest;
/// A test block.
pub type Block = sp_runtime::generic::Block<Header, Extrinsic>;
/// A test block's header.
pub type Header = sp_runtime::generic::Header<BlockNumber, Hashing>;
/// Balance of an account.
pub type Balance = u64;

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
		/// A function for that the signature changed in version `2`.
		#[changed_in(2)]
		fn function_signature_changed() -> Vec<u64>;
		/// The new signature.
		fn function_signature_changed() -> u64;
		/// trie no_std testing
		fn use_trie() -> u64;
		/// Calls function in the loop using never-inlined function pointer
		fn benchmark_indirect_call() -> u64;
		/// Calls function in the loop
		fn benchmark_direct_call() -> u64;
		/// Allocates vector with given capacity.
		fn vec_with_capacity(size: u32) -> Vec<u8>;
		/// Returns the initialized block number.
		fn get_block_number() -> u64;

		/// Test that `ed25519` crypto works in the runtime.
		///
		/// Returns the signature generated for the message `ed25519` and the public key.
		fn test_ed25519_crypto() -> (ed25519::AppSignature, ed25519::AppPublic);
		/// Test that `sr25519` crypto works in the runtime.
		///
		/// Returns the signature generated for the message `sr25519`.
		fn test_sr25519_crypto() -> (sr25519::AppSignature, sr25519::AppPublic);
		/// Test that `ecdsa` crypto works in the runtime.
		///
		/// Returns the signature generated for the message `ecdsa`.
		fn test_ecdsa_crypto() -> (ecdsa::AppSignature, ecdsa::AppPublic);
		/// Run various tests against storage.
		fn test_storage();
		/// Check a witness.
		fn test_witness(proof: StorageProof, root: crate::Hash);
		/// Test that ensures that we can call a function that takes multiple
		/// arguments.
		fn test_multiple_arguments(data: Vec<u8>, other: Vec<u8>, num: u32);
		/// Traces log "Hey I'm runtime."
		fn do_trace_log();
		/// Verify the given signature, public & message bundle.
		fn verify_ed25519(sig: ed25519::Signature, public: ed25519::Public, message: Vec<u8>) -> bool;
	}
}

pub type Executive = frame_executive::Executive<
	Runtime,
	Block,
	frame_system::ChainContext<Runtime>,
	Runtime,
	AllPalletsWithSystem,
>;

#[derive(Copy, Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, TypeInfo)]
pub struct CheckSubstrateCall;

impl sp_runtime::traits::Printable for CheckSubstrateCall {
	fn print(&self) {
		"CheckSubstrateCall".print()
	}
}

impl sp_runtime::traits::Dispatchable for CheckSubstrateCall {
	type RuntimeOrigin = CheckSubstrateCall;
	type Config = CheckSubstrateCall;
	type Info = CheckSubstrateCall;
	type PostInfo = CheckSubstrateCall;

	fn dispatch(
		self,
		_origin: Self::RuntimeOrigin,
	) -> sp_runtime::DispatchResultWithInfo<Self::PostInfo> {
		panic!("This implementation should not be used for actual dispatch.");
	}
}

impl sp_runtime::traits::SignedExtension for CheckSubstrateCall {
	type AccountId = AccountId;
	type Call = RuntimeCall;
	type AdditionalSigned = ();
	type Pre = ();
	const IDENTIFIER: &'static str = "CheckSubstrateCall";

	fn additional_signed(
		&self,
	) -> sp_std::result::Result<Self::AdditionalSigned, TransactionValidityError> {
		Ok(())
	}

	fn validate(
		&self,
		_who: &Self::AccountId,
		call: &Self::Call,
		_info: &DispatchInfoOf<Self::Call>,
		_len: usize,
	) -> TransactionValidity {
		log::trace!(target: LOG_TARGET, "validate");
		match call {
			RuntimeCall::SubstrateTest(ref substrate_test_call) =>
				substrate_test_pallet::validate_runtime_call(substrate_test_call),
			_ => Ok(Default::default()),
		}
	}

	fn pre_dispatch(
		self,
		who: &Self::AccountId,
		call: &Self::Call,
		info: &sp_runtime::traits::DispatchInfoOf<Self::Call>,
		len: usize,
	) -> Result<Self::Pre, TransactionValidityError> {
		self.validate(who, call, info, len).map(drop)
	}
}

construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = Extrinsic
	{
		System: frame_system,
		Babe: pallet_babe,
		SubstrateTest: substrate_test_pallet::pallet,
		Balances: pallet_balances,
	}
);

/// We assume that ~10% of the block weight is consumed by `on_initialize` handlers.
/// This is used to limit the maximal weight of a single extrinsic.
const AVERAGE_ON_INITIALIZE_RATIO: Perbill = Perbill::from_percent(10);
/// We allow `Normal` extrinsics to fill up the block up to 75%, the rest can be used
/// by  Operational  extrinsics.
const NORMAL_DISPATCH_RATIO: Perbill = Perbill::from_percent(75);
/// Max weight, actual value does not matter for test runtime.
const MAXIMUM_BLOCK_WEIGHT: Weight =
	Weight::from_parts(WEIGHT_REF_TIME_PER_SECOND.saturating_mul(2), u64::MAX);

parameter_types! {
	pub const BlockHashCount: BlockNumber = 2400;
	pub const Version: RuntimeVersion = VERSION;

	pub RuntimeBlockLength: BlockLength =
		BlockLength::max_with_normal_ratio(5 * 1024 * 1024, NORMAL_DISPATCH_RATIO);

	pub RuntimeBlockWeights: BlockWeights = BlockWeights::builder()
		.base_block(BlockExecutionWeight::get())
		.for_class(DispatchClass::all(), |weights| {
			weights.base_extrinsic = ExtrinsicBaseWeight::get();
		})
		.for_class(DispatchClass::Normal, |weights| {
			weights.max_total = Some(NORMAL_DISPATCH_RATIO * MAXIMUM_BLOCK_WEIGHT);
		})
		.for_class(DispatchClass::Operational, |weights| {
			weights.max_total = Some(MAXIMUM_BLOCK_WEIGHT);
			// Operational transactions have some extra reserved space, so that they
			// are included even if block reached `MAXIMUM_BLOCK_WEIGHT`.
			weights.reserved = Some(
				MAXIMUM_BLOCK_WEIGHT - NORMAL_DISPATCH_RATIO * MAXIMUM_BLOCK_WEIGHT
			);
		})
		.avg_block_initialization(AVERAGE_ON_INITIALIZE_RATIO)
		.build_or_panic();
}

impl frame_system::pallet::Config for Runtime {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = RuntimeBlockWeights;
	type BlockLength = ();
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type Index = Index;
	type BlockNumber = BlockNumber;
	type Hash = H256;
	type Hashing = Hashing;
	type AccountId = AccountId;
	type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<2400>;
	type DbWeight = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<Balance>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}

pub mod currency {
	use crate::Balance;
	const MILLICENTS: Balance = 1_000_000_000;
	const CENTS: Balance = 1_000 * MILLICENTS; // assume this is worth about a cent.
	pub const DOLLARS: Balance = 100 * CENTS;
}

parameter_types! {
	pub const ExistentialDeposit: Balance = 1 * currency::DOLLARS;
	// For weight estimation, we assume that the most locks on an individual account will be 50.
	// This number may need to be adjusted in the future if this assumption no longer holds true.
	pub const MaxLocks: u32 = 50;
	pub const MaxReserves: u32 = 50;
}

impl pallet_balances::Config for Runtime {
	type MaxLocks = MaxLocks;
	type MaxReserves = MaxReserves;
	type ReserveIdentifier = [u8; 8];
	type Balance = Balance;
	type DustRemoval = ();
	type RuntimeEvent = RuntimeEvent;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = pallet_balances::weights::SubstrateWeight<Runtime>;
	type FreezeIdentifier = ();
	type MaxFreezes = ();
	type HoldIdentifier = ();
	type MaxHolds = ConstU32<1>;
}

impl substrate_test_pallet::Config for Runtime {}

// Required for `pallet_babe::Config`.
impl pallet_timestamp::Config for Runtime {
	type Moment = u64;
	type OnTimestampSet = Babe;
	type MinimumPeriod = ConstU64<500>;
	type WeightInfo = pallet_timestamp::weights::SubstrateWeight<Runtime>;
}

parameter_types! {
	pub const EpochDuration: u64 = 6;
}

impl pallet_babe::Config for Runtime {
	type EpochDuration = EpochDuration;
	type ExpectedBlockTime = ConstU64<10_000>;
	type EpochChangeTrigger = pallet_babe::SameAuthoritiesForever;
	type DisabledValidators = ();
	type KeyOwnerProof = sp_core::Void;
	type EquivocationReportSystem = ();
	type WeightInfo = ();
	type MaxAuthorities = ConstU32<10>;
}

/// Adds one to the given input and returns the final result.
#[inline(never)]
fn benchmark_add_one(i: u64) -> u64 {
	i + 1
}

fn code_using_trie() -> u64 {
	let pairs = [
		(b"0103000000000000000464".to_vec(), b"0400000000".to_vec()),
		(b"0103000000000000000469".to_vec(), b"0401000000".to_vec()),
	]
	.to_vec();

	let mut mdb = PrefixedMemoryDB::default();
	let mut root = sp_std::default::Default::default();
	{
		let mut t = TrieDBMutBuilderV1::<Hashing>::new(&mut mdb, &mut root).build();
		for (key, value) in &pairs {
			if t.insert(key, value).is_err() {
				return 101
			}
		}
	}

	let trie = TrieDBBuilder::<Hashing>::new(&mdb, &root).build();
	let res = if let Ok(iter) = trie.iter() { iter.flatten().count() as u64 } else { 102 };

	res
}

impl_opaque_keys! {
	pub struct SessionKeys {
		pub ed25519: ed25519::AppPublic,
		pub sr25519: sr25519::AppPublic,
		pub ecdsa: ecdsa::AppPublic,
	}
}

pub(crate) const TEST_RUNTIME_BABE_EPOCH_CONFIGURATION: BabeEpochConfiguration =
	BabeEpochConfiguration {
		c: (3, 10),
		allowed_slots: AllowedSlots::PrimaryAndSecondaryPlainSlots,
	};

impl_runtime_apis! {
	impl sp_api::Core<Block> for Runtime {
		fn version() -> RuntimeVersion {
			version()
		}

		fn execute_block(block: Block) {
			log::trace!(target: LOG_TARGET, "execute_block: {block:#?}");
			Executive::execute_block(block);
		}

		fn initialize_block(header: &<Block as BlockT>::Header) {
			log::trace!(target: LOG_TARGET, "initialize_block: {header:#?}");
			Executive::initialize_block(header);
		}
	}

	impl sp_api::Metadata<Block> for Runtime {
		fn metadata() -> OpaqueMetadata {
			unimplemented!()
		}

		fn metadata_at_version(_version: u32) -> Option<OpaqueMetadata> {
			unimplemented!()
		}
		fn metadata_versions() -> sp_std::vec::Vec<u32> {
			unimplemented!()
		}
	}

	impl sp_transaction_pool::runtime_api::TaggedTransactionQueue<Block> for Runtime {
		fn validate_transaction(
			source: TransactionSource,
			utx: <Block as BlockT>::Extrinsic,
			block_hash: <Block as BlockT>::Hash,
		) -> TransactionValidity {
			let validity = Executive::validate_transaction(source, utx.clone(), block_hash);
			log::trace!(target: LOG_TARGET, "validate_transaction {:?} {:?}", utx, validity);
			validity
		}
	}

	impl sp_block_builder::BlockBuilder<Block> for Runtime {
		fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic) -> ApplyExtrinsicResult {
			Executive::apply_extrinsic(extrinsic)
		}

		fn finalize_block() -> <Block as BlockT>::Header {
			log::trace!(target: LOG_TARGET, "finalize_block");
			Executive::finalize_block()
		}

		fn inherent_extrinsics(_data: InherentData) -> Vec<<Block as BlockT>::Extrinsic> {
			vec![]
		}

		fn check_inherents(_block: Block, _data: InherentData) -> CheckInherentsResult {
			CheckInherentsResult::new()
		}
	}

	impl frame_system_rpc_runtime_api::AccountNonceApi<Block, AccountId, Index> for Runtime {
		fn account_nonce(account: AccountId) -> Index {
			System::account_nonce(account)
		}
	}

	impl self::TestAPI<Block> for Runtime {
		fn balance_of(id: AccountId) -> u64 {
			Balances::free_balance(id)
		}

		fn benchmark_add_one(val: &u64) -> u64 {
			val + 1
		}

		fn benchmark_vector_add_one(vec: &Vec<u64>) -> Vec<u64> {
			let mut vec = vec.clone();
			vec.iter_mut().for_each(|v| *v += 1);
			vec
		}

		fn function_signature_changed() -> u64 {
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

		fn vec_with_capacity(size: u32) -> Vec<u8> {
			Vec::with_capacity(size as usize)
		}

		fn get_block_number() -> u64 {
			System::block_number()
		}

		fn test_ed25519_crypto() -> (ed25519::AppSignature, ed25519::AppPublic) {
			test_ed25519_crypto()
		}

		fn test_sr25519_crypto() -> (sr25519::AppSignature, sr25519::AppPublic) {
			test_sr25519_crypto()
		}

		fn test_ecdsa_crypto() -> (ecdsa::AppSignature, ecdsa::AppPublic) {
			test_ecdsa_crypto()
		}

		fn test_storage() {
			test_read_storage();
			test_read_child_storage();
		}

		fn test_witness(proof: StorageProof, root: crate::Hash) {
			test_witness(proof, root);
		}

		fn test_multiple_arguments(data: Vec<u8>, other: Vec<u8>, num: u32) {
			assert_eq!(&data[..], &other[..]);
			assert_eq!(data.len(), num as usize);
		}

		fn do_trace_log() {
			log::trace!("Hey I'm runtime");
		}

		fn verify_ed25519(sig: ed25519::Signature, public: ed25519::Public, message: Vec<u8>) -> bool {
			sp_io::crypto::ed25519_verify(&sig, &message, &public)
		}
	}

	impl sp_consensus_aura::AuraApi<Block, AuraId> for Runtime {
		fn slot_duration() -> sp_consensus_aura::SlotDuration {
			sp_consensus_aura::SlotDuration::from_millis(1000)
		}

		fn authorities() -> Vec<AuraId> {
			SubstrateTest::authorities().into_iter().map(|a| {
				let authority: sr25519::Public = a.into();
				AuraId::from(authority)
			}).collect()
		}
	}

	impl sp_consensus_babe::BabeApi<Block> for Runtime {
		fn configuration() -> sp_consensus_babe::BabeConfiguration {
			let epoch_config = Babe::epoch_config().unwrap_or(TEST_RUNTIME_BABE_EPOCH_CONFIGURATION);
			sp_consensus_babe::BabeConfiguration {
				slot_duration: Babe::slot_duration(),
				epoch_length: EpochDuration::get(),
				c: epoch_config.c,
				authorities: SubstrateTest::authorities()
					.into_iter().map(|x|(x, 1)).collect(),
					randomness: Babe::randomness(),
					allowed_slots: epoch_config.allowed_slots,
			}
		}

		fn current_epoch_start() -> Slot {
			Babe::current_epoch_start()
		}

		fn current_epoch() -> sp_consensus_babe::Epoch {
			Babe::current_epoch()
		}

		fn next_epoch() -> sp_consensus_babe::Epoch {
			Babe::next_epoch()
		}

		fn submit_report_equivocation_unsigned_extrinsic(
			_equivocation_proof: sp_consensus_babe::EquivocationProof<
			<Block as BlockT>::Header,
			>,
			_key_owner_proof: sp_consensus_babe::OpaqueKeyOwnershipProof,
		) -> Option<()> {
			None
		}

		fn generate_key_ownership_proof(
			_slot: sp_consensus_babe::Slot,
			_authority_id: sp_consensus_babe::AuthorityId,
		) -> Option<sp_consensus_babe::OpaqueKeyOwnershipProof> {
			None
		}
	}

	impl sp_offchain::OffchainWorkerApi<Block> for Runtime {
		fn offchain_worker(header: &<Block as BlockT>::Header) {
			let ext = Extrinsic::new_unsigned(
				substrate_test_pallet::pallet::Call::storage_change{
					key:b"some_key".encode(),
					value:Some(header.number.encode())
				}.into(),
			);
			sp_io::offchain::submit_transaction(ext.encode()).unwrap();
		}
	}

	impl sp_session::SessionKeys<Block> for Runtime {
		fn generate_session_keys(_: Option<Vec<u8>>) -> Vec<u8> {
			SessionKeys::generate(None)
		}

		fn decode_session_keys(
			encoded: Vec<u8>,
		) -> Option<Vec<(Vec<u8>, sp_core::crypto::KeyTypeId)>> {
			SessionKeys::decode_into_raw_public_keys(&encoded)
		}
	}

	impl sp_consensus_grandpa::GrandpaApi<Block> for Runtime {
		fn grandpa_authorities() -> sp_consensus_grandpa::AuthorityList {
			Vec::new()
		}

		fn current_set_id() -> sp_consensus_grandpa::SetId {
			0
		}

		fn submit_report_equivocation_unsigned_extrinsic(
			_equivocation_proof: sp_consensus_grandpa::EquivocationProof<
			<Block as BlockT>::Hash,
			NumberFor<Block>,
			>,
			_key_owner_proof: sp_consensus_grandpa::OpaqueKeyOwnershipProof,
		) -> Option<()> {
			None
		}

		fn generate_key_ownership_proof(
			_set_id: sp_consensus_grandpa::SetId,
			_authority_id: sp_consensus_grandpa::AuthorityId,
		) -> Option<sp_consensus_grandpa::OpaqueKeyOwnershipProof> {
			None
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

fn test_ecdsa_crypto() -> (ecdsa::AppSignature, ecdsa::AppPublic) {
	let public0 = ecdsa::AppPublic::generate_pair(None);
	let public1 = ecdsa::AppPublic::generate_pair(None);
	let public2 = ecdsa::AppPublic::generate_pair(None);

	let all = ecdsa::AppPublic::all();
	assert!(all.contains(&public0));
	assert!(all.contains(&public1));
	assert!(all.contains(&public2));

	let signature = public0.sign(&"ecdsa").expect("Generates a valid `ecdsa` signature.");

	assert!(public0.verify(&"ecdsa", &signature));
	(signature, public0)
}

fn test_read_storage() {
	const KEY: &[u8] = b":read_storage";
	sp_io::storage::set(KEY, b"test");

	let mut v = [0u8; 4];
	let r = sp_io::storage::read(KEY, &mut v, 0);
	assert_eq!(r, Some(4));
	assert_eq!(&v, b"test");

	let mut v = [0u8; 4];
	let r = sp_io::storage::read(KEY, &mut v, 4);
	assert_eq!(r, Some(0));
	assert_eq!(&v, &[0, 0, 0, 0]);
}

fn test_read_child_storage() {
	const STORAGE_KEY: &[u8] = b"unique_id_1";
	const KEY: &[u8] = b":read_child_storage";
	sp_io::default_child_storage::set(STORAGE_KEY, KEY, b"test");

	let mut v = [0u8; 4];
	let r = sp_io::default_child_storage::read(STORAGE_KEY, KEY, &mut v, 0);
	assert_eq!(r, Some(4));
	assert_eq!(&v, b"test");

	let mut v = [0u8; 4];
	let r = sp_io::default_child_storage::read(STORAGE_KEY, KEY, &mut v, 8);
	assert_eq!(r, Some(0));
	assert_eq!(&v, &[0, 0, 0, 0]);
}

fn test_witness(proof: StorageProof, root: crate::Hash) {
	use sp_externalities::Externalities;
	let db: sp_trie::MemoryDB<crate::Hashing> = proof.into_memory_db();
	let backend = sp_state_machine::TrieBackendBuilder::<_, crate::Hashing>::new(db, root).build();
	let mut overlay = sp_state_machine::OverlayedChanges::default();
	let mut cache = sp_state_machine::StorageTransactionCache::<_, _>::default();
	let mut ext = sp_state_machine::Ext::new(
		&mut overlay,
		&mut cache,
		&backend,
		#[cfg(feature = "std")]
		None,
	);
	assert!(ext.storage(b"value3").is_some());
	assert!(ext.storage_root(Default::default()).as_slice() == &root[..]);
	ext.place_storage(vec![0], Some(vec![1]));
	assert!(ext.storage_root(Default::default()).as_slice() != &root[..]);
}

/// Some tests require the hashed keys of the storage. As the values of hashed keys are not trivial
/// to guess, this small module provides the values of the keys, and the code which is required to
/// generate the keys.
#[cfg(feature = "std")]
pub mod storage_key_generator {
	use super::*;
	use sp_core::Pair;
	use sp_keyring::AccountKeyring;

	/// Generate hex string without prefix
	pub(super) fn hex<T>(x: T) -> String
	where
		T: array_bytes::Hex,
	{
		x.hex(Default::default())
	}

	fn concat_hashes(input: &Vec<&[u8]>) -> String {
		input.iter().map(|s| sp_core::hashing::twox_128(s)).map(hex).collect()
	}

	fn twox_64_concat(x: &[u8]) -> Vec<u8> {
		sp_core::hashing::twox_64(x).iter().chain(x.iter()).cloned().collect::<Vec<_>>()
	}

	/// Generate the hashed storage keys from the raw literals. These keys are expected to be be in
	/// storage with given substrate-test runtime.
	pub fn generate_expected_storage_hashed_keys() -> Vec<String> {
		let literals: Vec<&[u8]> = vec![b":code", b":extrinsic_index", b":heappages"];

		let keys: Vec<Vec<&[u8]>> = vec![
			vec![b"Babe", b"Authorities"],
			vec![b"Babe", b"EpochConfig"],
			vec![b"Babe", b"NextAuthorities"],
			vec![b"Babe", b"SegmentIndex"],
			vec![b"Babe", b":__STORAGE_VERSION__:"],
			vec![b"Balances", b":__STORAGE_VERSION__:"],
			vec![b"Balances", b"TotalIssuance"],
			vec![b"SubstrateTest", b"Authorities"],
			vec![b"SubstrateTest", b":__STORAGE_VERSION__:"],
			vec![b"System", b"LastRuntimeUpgrade"],
			vec![b"System", b"ParentHash"],
			vec![b"System", b":__STORAGE_VERSION__:"],
			vec![b"System", b"UpgradedToTripleRefCount"],
			vec![b"System", b"UpgradedToU32RefCount"],
		];

		let mut expected_keys = keys.iter().map(concat_hashes).collect::<Vec<String>>();

		expected_keys.extend(literals.into_iter().map(hex));

		let balances_map_keys = (0..16_usize)
			.into_iter()
			.map(|i| AccountKeyring::numeric(i).public().to_vec())
			.chain(vec![
				AccountKeyring::Alice.public().to_vec(),
				AccountKeyring::Bob.public().to_vec(),
				AccountKeyring::Charlie.public().to_vec(),
			])
			.map(|pubkey| {
				sp_core::hashing::blake2_128(&pubkey)
					.iter()
					.chain(pubkey.iter())
					.cloned()
					.collect::<Vec<u8>>()
			})
			.map(|hash_pubkey| {
				[concat_hashes(&vec![b"System", b"Account"]), hex(hash_pubkey)].concat()
			});

		expected_keys.extend(balances_map_keys);

		expected_keys.push(
			[
				concat_hashes(&vec![b"System", b"BlockHash"]),
				hex(0u64.using_encoded(twox_64_concat)),
			]
			.concat(),
		);

		expected_keys.sort();
		expected_keys
	}

	/// Provides the commented list of hashed keys. This contains a hard-coded list of hashed keys
	/// that would be generated by `generate_expected_storage_hashed_keys`. This list is provided
	/// for the debugging convenience only. Value of each hex-string is documented with the literal
	/// origin.
	pub fn get_expected_storage_hashed_keys() -> Vec<String> {
		[
			//System|:__STORAGE_VERSION__:
			"00771836bebdd29870ff246d305c578c4e7b9012096b41c4eb3aaf947f6ea429",
			//SubstrateTest|Authorities
			"00771836bebdd29870ff246d305c578c5e0621c4869aa60c02be9adcc98a0d1d",
			//Babe|:__STORAGE_VERSION__:
			"1cb6f36e027abb2091cfb5110ab5087f4e7b9012096b41c4eb3aaf947f6ea429",
			//Babe|Authorities
			"1cb6f36e027abb2091cfb5110ab5087f5e0621c4869aa60c02be9adcc98a0d1d",
			//Babe|SegmentIndex
			"1cb6f36e027abb2091cfb5110ab5087f66e8f035c8adbe7f1547b43c51e6f8a4",
			//Babe|NextAuthorities
			"1cb6f36e027abb2091cfb5110ab5087faacf00b9b41fda7a9268821c2a2b3e4c",
			//Babe|EpochConfig
			"1cb6f36e027abb2091cfb5110ab5087fdc6b171b77304263c292cc3ea5ed31ef",
			//System|:__STORAGE_VERSION__:
			"26aa394eea5630e07c48ae0c9558cef74e7b9012096b41c4eb3aaf947f6ea429",
			//System|UpgradedToU32RefCount
			"26aa394eea5630e07c48ae0c9558cef75684a022a34dd8bfa2baaf44f172b710",
			//System|ParentHash
			"26aa394eea5630e07c48ae0c9558cef78a42f33323cb5ced3b44dd825fda9fcc",
			//System::BlockHash|0
			"26aa394eea5630e07c48ae0c9558cef7a44704b568d21667356a5a050c118746bb1bdbcacd6ac9340000000000000000",
			//System|UpgradedToTripleRefCount
			"26aa394eea5630e07c48ae0c9558cef7a7fd6c28836b9a28522dc924110cf439",

			// System|Account|blake2_128Concat("//11")
			"26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da901cae4e3edfbb32c91ed3f01ab964f4eeeab50338d8e5176d3141802d7b010a55dadcd5f23cf8aaafa724627e967e90e",
			// System|Account|blake2_128Concat("//4")
			"26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da91b614bd4a126f2d5d294e9a8af9da25248d7e931307afb4b68d8d565d4c66e00d856c6d65f5fed6bb82dcfb60e936c67",
			// System|Account|blake2_128Concat("//7")
			"26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da94b21aff9fe1e8b2fc4b0775b8cbeff28ba8e2c7594dd74730f3ca835e95455d199261897edc9735d602ea29615e2b10b",
			// System|Account|blake2_128Concat("//Bob")
			"26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da94f9aea1afa791265fae359272badc1cf8eaf04151687736326c9fea17e25fc5287613693c912909cb226aa4794f26a48",
			// System|Account|blake2_128Concat("//3")
			"26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da95786a2916fcb81e1bd5dcd81e0d2452884617f575372edb5a36d85c04cdf2e4699f96fe33eb5f94a28c041b88e398d0c",
			// System|Account|blake2_128Concat("//14")
			"26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da95b8542d9672c7b7e779cc7c1e6b605691c2115d06120ea2bee32dd601d02f36367564e7ddf84ae2717ca3f097459652e",
			// System|Account|blake2_128Concat("//6")
			"26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da996c30bdbfab640838e6b6d3c33ab4adb4211b79e34ee8072eab506edd4b93a7b85a14c9a05e5cdd056d98e7dbca87730",
			// System|Account|blake2_128Concat("//9")
			"26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da99dc65b1339ec388fbf2ca0cdef51253512c6cfd663203ea16968594f24690338befd906856c4d2f4ef32dad578dba20c",
			// System|Account|blake2_128Concat("//8")
			"26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da99e6eb5abd62f5fd54793da91a47e6af6125d57171ff9241f07acaa1bb6a6103517965cf2cd00e643b27e7599ebccba70",
			// System|Account|blake2_128Concat("//Charlie")
			"26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da9b0edae20838083f2cde1c4080db8cf8090b5ab205c6974c9ea841be688864633dc9ca8a357843eeacf2314649965fe22",
			// System|Account|blake2_128Concat("//10")
			"26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da9d0052993b6f3bd0544fd1f5e4125b9fbde3e789ecd53431fe5c06c12b72137153496dace35c695b5f4d7b41f7ed5763b",
			// System|Account|blake2_128Concat("//1")
			"26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da9d6b7e9a5f12bc571053265dade10d3b4b606fc73f57f03cdb4c932d475ab426043e429cecc2ffff0d2672b0df8398c48",
			// System|Account|blake2_128Concat("//Alice")
			"26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da9de1e86a9a8c739864cf3cc5ec2bea59fd43593c715fdd31c61141abd04a99fd6822c8558854ccde39a5684e7a56da27d",
			// System|Account|blake2_128Concat("//2")
			"26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da9e1a35f56ee295d39287cbffcfc60c4b346f136b564e1fad55031404dd84e5cd3fa76bfe7cc7599b39d38fd06663bbc0a",
			// System|Account|blake2_128Concat("//5")
			"26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da9e2c1dc507e2035edbbd8776c440d870460c57f0008067cc01c5ff9eb2e2f9b3a94299a915a91198bd1021a6c55596f57",
			// System|Account|blake2_128Concat("//0")
			"26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da9eca0e653a94f4080f6311b4e7b6934eb2afba9278e30ccf6a6ceb3a8b6e336b70068f045c666f2e7f4f9cc5f47db8972",
			// System|Account|blake2_128Concat("//13")
			"26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da9ee8bf7ef90fc56a8aa3b90b344c599550c29b161e27ff8ba45bf6bad4711f326fc506a8803453a4d7e3158e993495f10",
			// System|Account|blake2_128Concat("//12")
			"26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da9f5d6f1c082fe63eec7a71fcad00f4a892e3d43b7b0d04e776e69e7be35247cecdac65504c579195731eaf64b7940966e",
			// System|Account|blake2_128Concat("//15")
			"26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da9fbf0818841edf110e05228a6379763c4fc3c37459d9bdc61f58a5ebc01e9e2305a19d390c0543dc733861ec3cf1de01f",
			// System|LastRuntimeUpgrade
			"26aa394eea5630e07c48ae0c9558cef7f9cce9c888469bb1a0dceaa129672ef8",
			// :code
			"3a636f6465",
			// :extrinsic_index
			"3a65787472696e7369635f696e646578",
			// :heappages
			"3a686561707061676573",
			// Balances|:__STORAGE_VERSION__:
			"c2261276cc9d1f8598ea4b6a74b15c2f4e7b9012096b41c4eb3aaf947f6ea429",
			// Balances|TotalIssuance
			"c2261276cc9d1f8598ea4b6a74b15c2f57c875e4cff74148e4628f264b974c80",
		].into_iter().map(String::from).collect::<Vec<_>>()
	}

	#[test]
	fn expected_keys_vec_are_matching() {
		assert_eq!(
			storage_key_generator::get_expected_storage_hashed_keys(),
			storage_key_generator::generate_expected_storage_hashed_keys(),
		);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use codec::Encode;
	use frame_support::dispatch::DispatchInfo;
	use sc_block_builder::BlockBuilderProvider;
	use sp_api::ProvideRuntimeApi;
	use sp_consensus::BlockOrigin;
	use sp_core::{storage::well_known_keys::HEAP_PAGES, ExecutionContext};
	use sp_keyring::AccountKeyring;
	use sp_runtime::{traits::SignedExtension, transaction_validity::InvalidTransaction};
	use sp_state_machine::ExecutionStrategy;
	use substrate_test_runtime_client::{
		prelude::*, runtime::TestAPI, DefaultTestClientBuilderExt, TestClientBuilder,
	};

	#[test]
	fn heap_pages_is_respected() {
		// This tests that the on-chain `HEAP_PAGES` parameter is respected.

		// Create a client devoting only 8 pages of wasm memory. This gives us ~512k of heap memory.
		let mut client = TestClientBuilder::new()
			.set_execution_strategy(ExecutionStrategy::AlwaysWasm)
			.set_heap_pages(8)
			.build();
		let best_hash = client.chain_info().best_hash;

		// Try to allocate 1024k of memory on heap. This is going to fail since it is twice larger
		// than the heap.
		let ret = client.runtime_api().vec_with_capacity_with_context(
			best_hash,
			// Use `BlockImport` to ensure we use the on chain heap pages as configured above.
			ExecutionContext::Importing,
			1048576,
		);
		assert!(ret.is_err());

		// Create a block that sets the `:heap_pages` to 32 pages of memory which corresponds to
		// ~2048k of heap memory.
		let (new_at_hash, block) = {
			let mut builder = client.new_block(Default::default()).unwrap();
			builder.push_storage_change(HEAP_PAGES.to_vec(), Some(32u64.encode())).unwrap();
			let block = builder.build().unwrap().block;
			let hash = block.header.hash();
			(hash, block)
		};

		futures::executor::block_on(client.import(BlockOrigin::Own, block)).unwrap();

		// Allocation of 1024k while having ~2048k should succeed.
		let ret = client.runtime_api().vec_with_capacity(new_at_hash, 1048576);
		assert!(ret.is_ok());
	}

	#[test]
	fn test_storage() {
		let client =
			TestClientBuilder::new().set_execution_strategy(ExecutionStrategy::Both).build();
		let runtime_api = client.runtime_api();
		let best_hash = client.chain_info().best_hash;

		runtime_api.test_storage(best_hash).unwrap();
	}

	fn witness_backend() -> (sp_trie::MemoryDB<crate::Hashing>, crate::Hash) {
		let mut root = crate::Hash::default();
		let mut mdb = sp_trie::MemoryDB::<crate::Hashing>::default();
		{
			let mut trie =
				sp_trie::trie_types::TrieDBMutBuilderV1::new(&mut mdb, &mut root).build();
			trie.insert(b"value3", &[142]).expect("insert failed");
			trie.insert(b"value4", &[124]).expect("insert failed");
		};
		(mdb, root)
	}

	#[test]
	fn witness_backend_works() {
		let (db, root) = witness_backend();
		let backend =
			sp_state_machine::TrieBackendBuilder::<_, crate::Hashing>::new(db, root).build();
		let proof = sp_state_machine::prove_read(backend, vec![b"value3"]).unwrap();
		let client =
			TestClientBuilder::new().set_execution_strategy(ExecutionStrategy::Both).build();
		let runtime_api = client.runtime_api();
		let best_hash = client.chain_info().best_hash;

		runtime_api.test_witness(best_hash, proof, root).unwrap();
	}

	pub fn new_test_ext() -> sp_io::TestExternalities {
		genesismap::GenesisStorageBuilder::new(
			vec![AccountKeyring::One.public().into(), AccountKeyring::Two.public().into()],
			vec![AccountKeyring::One.into(), AccountKeyring::Two.into()],
			1000 * currency::DOLLARS,
		)
		.build_storage()
		.into()
	}

	#[test]
	fn validate_storage_keys() {
		assert_eq!(
			genesismap::GenesisStorageBuilder::default()
				.build_storage()
				.top
				.keys()
				.cloned()
				.map(storage_key_generator::hex)
				.collect::<Vec<_>>(),
			storage_key_generator::get_expected_storage_hashed_keys()
		);
	}

	#[test]
	fn validate_unsigned_works() {
		sp_tracing::try_init_simple();
		new_test_ext().execute_with(|| {
			assert_eq!(
				<SubstrateTest as sp_runtime::traits::ValidateUnsigned>::validate_unsigned(
					TransactionSource::External,
					&substrate_test_pallet::Call::bench_call { transfer: Default::default() },
				),
				InvalidTransaction::Call.into(),
			);

			assert_eq!(
				<SubstrateTest as sp_runtime::traits::ValidateUnsigned>::validate_unsigned(
					TransactionSource::External,
					&substrate_test_pallet::Call::include_data { data: vec![] },
				),
				InvalidTransaction::Call.into(),
			);

			assert_eq!(
				<SubstrateTest as sp_runtime::traits::ValidateUnsigned>::validate_unsigned(
					TransactionSource::External,
					&substrate_test_pallet::Call::fill_block { ratio: Perbill::from_percent(50) },
				),
				InvalidTransaction::Call.into(),
			);

			assert_eq!(
				<SubstrateTest as sp_runtime::traits::ValidateUnsigned>::validate_unsigned(
					TransactionSource::External,
					&substrate_test_pallet::Call::deposit_log_digest_item {
						log: DigestItem::Other(vec![])
					},
				),
				Ok(Default::default()),
			);

			assert_eq!(
				<SubstrateTest as sp_runtime::traits::ValidateUnsigned>::validate_unsigned(
					TransactionSource::External,
					&substrate_test_pallet::Call::storage_change { key: vec![], value: None },
				),
				Ok(Default::default()),
			);

			assert_eq!(
				<SubstrateTest as sp_runtime::traits::ValidateUnsigned>::validate_unsigned(
					TransactionSource::External,
					&substrate_test_pallet::Call::read { count: 0 },
				),
				Ok(Default::default()),
			);

			assert_eq!(
				<SubstrateTest as sp_runtime::traits::ValidateUnsigned>::validate_unsigned(
					TransactionSource::External,
					&substrate_test_pallet::Call::read_and_panic { count: 0 },
				),
				Ok(Default::default()),
			);
		});
	}

	#[test]
	fn check_substrate_check_signed_extension_works() {
		sp_tracing::try_init_simple();
		new_test_ext().execute_with(|| {
			let x = sp_keyring::AccountKeyring::Alice.into();
			let info = DispatchInfo::default();
			let len = 0_usize;
			assert_eq!(
				CheckSubstrateCall {}
					.validate(
						&x,
						&ExtrinsicBuilder::new_call_with_priority(16).build().function,
						&info,
						len
					)
					.unwrap()
					.priority,
				16
			);

			assert_eq!(
				CheckSubstrateCall {}
					.validate(
						&x,
						&ExtrinsicBuilder::new_call_do_not_propagate().build().function,
						&info,
						len
					)
					.unwrap()
					.propagate,
				false
			);
		})
	}
}
