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
// pub type SignedExtra = SignedExtraDummy;
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
		fn benchmark_indirect_call() -> u64;
		fn benchmark_direct_call() -> u64;
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
	type Pre = CheckSubstrateCall;
	const IDENTIFIER: &'static str = "DummySignedExtension";

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
		self.validate(who, call, info, len).map(|_| CheckSubstrateCall {})
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
/// We allow for 2 seconds of compute with a 6 second average block time, with maximum proof size.
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

/// Money matters.
pub mod currency {
	use crate::Balance;
	pub const MILLICENTS: Balance = 1_000_000_000;
	pub const CENTS: Balance = 1_000 * MILLICENTS; // assume this is worth about a cent.
	pub const DOLLARS: Balance = 100 * CENTS;

	pub const fn deposit(items: u32, bytes: u32) -> Balance {
		items as Balance * 15 * CENTS + (bytes as Balance) * 6 * CENTS
	}
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
	type AccountStore = frame_system::Pallet<Runtime>;
	type WeightInfo = pallet_balances::weights::SubstrateWeight<Runtime>;
	type FreezeIdentifier = ();
	type MaxFreezes = ();
	type HoldIdentifier = ();
	type MaxHolds = ConstU32<1>;
}

impl substrate_test_pallet::Config for Runtime {}

// required for pallet_babe::Config
impl pallet_timestamp::Config for Runtime {
	/// A timestamp: milliseconds since the unix epoch.
	type Moment = u64;
	type OnTimestampSet = Babe;
	type MinimumPeriod = ConstU64<5>;
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
			log::trace!(target: LOG_TARGET, "validate_transaction {:?}", utx);
			let r = Executive::validate_transaction(source, utx, block_hash);
			log::trace!(target: LOG_TARGET, "validate_transaction a {:?}", r);
			r
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
			// unimplemented!("is not expected to be invoked from non-wasm builds");
			Vec::with_capacity(size as usize)
		}

		fn get_block_number() -> u64 {
			// substrate_test_pallet::get_block_number().expect("Block number is initialized")
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
				slot_duration: 1000,
				epoch_length: EpochDuration::get(),
				c: epoch_config.c,
				authorities: SubstrateTest::authorities()
					.into_iter().map(|x|(x, 1)).collect(),
					randomness: <pallet_babe::Pallet<Runtime>>::randomness(),
					allowed_slots: epoch_config.allowed_slots,
			}
		}

		fn current_epoch_start() -> Slot {
			<pallet_babe::Pallet<Runtime>>::current_epoch_start()
		}

		fn current_epoch() -> sp_consensus_babe::Epoch {
			<pallet_babe::Pallet<Runtime>>::current_epoch()
		}

		fn next_epoch() -> sp_consensus_babe::Epoch {
			<pallet_babe::Pallet<Runtime>>::next_epoch()
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
				substrate_test_pallet::pallet::Call::include_data{data:header.number.encode()}.into(),
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

#[cfg(test)]
mod tests {
	use codec::Encode;
	use sc_block_builder::BlockBuilderProvider;
	use sp_api::ProvideRuntimeApi;
	use sp_consensus::BlockOrigin;
	use sp_core::{storage::well_known_keys::HEAP_PAGES, ExecutionContext};
	use sp_state_machine::ExecutionStrategy;
	use substrate_test_runtime_client::{
		prelude::*, runtime::TestAPI, DefaultTestClientBuilderExt, TestClientBuilder,
	};

	#[test]
	fn heap_pages_is_respected() {
		// This tests that the on-chain HEAP_PAGES parameter is respected.

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
		use sp_trie::TrieMut;
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
}
