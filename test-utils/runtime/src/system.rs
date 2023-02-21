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

//! System manager: Handles all of the top-level stuff; executing block/transaction, setting code
//! and depositing logs.

use crate::{
	AccountId, AuthorityId, Block, BlockNumber, Digest, Extrinsic, Header, Runtime, Transfer,
	H256 as Hash,
};
use codec::{Decode, Encode, KeyedVec};
use frame_support::storage;
use sp_core::storage::well_known_keys;
use sp_io::{hashing::blake2_256, storage::root as storage_root, trie};
use sp_runtime::{
	generic,
	traits::Header as _,
	transaction_validity::{
		InvalidTransaction, TransactionValidity, TransactionValidityError, ValidTransaction,
	},
	ApplyExtrinsicResult,
};
use sp_std::prelude::*;

const NONCE_OF: &[u8] = b"nonce:";
const BALANCE_OF: &[u8] = b"balance:";

pub use self::pallet::*;

#[frame_support::pallet]
mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	#[pallet::without_storage_info]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::storage]
	pub type ExtrinsicData<T> = StorageMap<_, Blake2_128Concat, u32, Vec<u8>, ValueQuery>;

	// The current block number being processed. Set by `execute_block`.
	#[pallet::storage]
	pub type Number<T> = StorageValue<_, BlockNumber, OptionQuery>;

	#[pallet::storage]
	pub type ParentHash<T> = StorageValue<_, Hash, ValueQuery>;

	#[pallet::storage]
	pub type NewAuthorities<T> = StorageValue<_, Vec<AuthorityId>, OptionQuery>;

	#[pallet::storage]
	pub type StorageDigest<T> = StorageValue<_, Digest, OptionQuery>;

	#[pallet::storage]
	pub type Authorities<T> = StorageValue<_, Vec<AuthorityId>, ValueQuery>;

	#[pallet::genesis_config]
	#[cfg_attr(feature = "std", derive(Default))]
	pub struct GenesisConfig {
		pub authorities: Vec<AuthorityId>,
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig {
		fn build(&self) {
			<Authorities<T>>::put(self.authorities.clone());
		}
	}
}

pub fn balance_of_key(who: AccountId) -> Vec<u8> {
	who.to_keyed_vec(BALANCE_OF)
}

pub fn balance_of(who: AccountId) -> u64 {
	storage::hashed::get_or(&blake2_256, &balance_of_key(who), 0)
}

pub fn nonce_of(who: AccountId) -> u64 {
	storage::hashed::get_or(&blake2_256, &who.to_keyed_vec(NONCE_OF), 0)
}

pub fn initialize_block(header: &Header) {
	// populate environment.
	<Number<Runtime>>::put(&header.number);
	<ParentHash<Runtime>>::put(&header.parent_hash);
	<StorageDigest<Runtime>>::put(header.digest());
	storage::unhashed::put(well_known_keys::EXTRINSIC_INDEX, &0u32);

	// try to read something that depends on current header digest
	// so that it'll be included in execution proof
	if let Some(generic::DigestItem::Other(v)) = header.digest().logs().iter().next() {
		let _: Option<u32> = storage::unhashed::get(v);
	}
}

pub fn authorities() -> Vec<AuthorityId> {
	<Authorities<Runtime>>::get()
}

pub fn get_block_number() -> Option<BlockNumber> {
	<Number<Runtime>>::get()
}

pub fn take_block_number() -> Option<BlockNumber> {
	<Number<Runtime>>::take()
}

#[derive(Copy, Clone)]
enum Mode {
	Verify,
	Overwrite,
}

/// Actually execute all transitioning for `block`.
pub fn polish_block(block: &mut Block) {
	execute_block_with_state_root_handler(block, Mode::Overwrite);
}

pub fn execute_block(mut block: Block) -> Header {
	execute_block_with_state_root_handler(&mut block, Mode::Verify)
}

fn execute_block_with_state_root_handler(block: &mut Block, mode: Mode) -> Header {
	let header = &mut block.header;

	initialize_block(header);

	// execute transactions
	block.extrinsics.iter().for_each(|e| {
		let _ = execute_transaction(e.clone()).unwrap_or_else(|_| panic!("Invalid transaction"));
	});

	let new_header = finalize_block();

	if let Mode::Overwrite = mode {
		header.state_root = new_header.state_root;
	} else {
		info_expect_equal_hash(&new_header.state_root, &header.state_root);
		assert_eq!(
			new_header.state_root, header.state_root,
			"Storage root must match that calculated.",
		);
	}

	if let Mode::Overwrite = mode {
		header.extrinsics_root = new_header.extrinsics_root;
	} else {
		info_expect_equal_hash(&new_header.extrinsics_root, &header.extrinsics_root);
		assert_eq!(
			new_header.extrinsics_root, header.extrinsics_root,
			"Transaction trie root must be valid.",
		);
	}

	new_header
}

/// The block executor.
pub struct BlockExecutor;

impl frame_support::traits::ExecuteBlock<Block> for BlockExecutor {
	fn execute_block(block: Block) {
		execute_block(block);
	}
}

/// Execute a transaction outside of the block execution function.
/// This doesn't attempt to validate anything regarding the block.
pub fn validate_transaction(utx: Extrinsic) -> TransactionValidity {
	if check_signature(&utx).is_err() {
		return InvalidTransaction::BadProof.into()
	}

	let tx = utx.transfer();
	let nonce_key = tx.from.to_keyed_vec(NONCE_OF);
	let expected_nonce: u64 = storage::hashed::get_or(&blake2_256, &nonce_key, 0);
	if tx.nonce < expected_nonce {
		return InvalidTransaction::Stale.into()
	}
	if tx.nonce > expected_nonce + 64 {
		return InvalidTransaction::Future.into()
	}

	let encode = |from: &AccountId, nonce: u64| (from, nonce).encode();
	let requires = if tx.nonce != expected_nonce && tx.nonce > 0 {
		vec![encode(&tx.from, tx.nonce - 1)]
	} else {
		vec![]
	};

	let provides = vec![encode(&tx.from, tx.nonce)];

	Ok(ValidTransaction { priority: tx.amount, requires, provides, longevity: 64, propagate: true })
}

/// Execute a transaction outside of the block execution function.
/// This doesn't attempt to validate anything regarding the block.
pub fn execute_transaction(utx: Extrinsic) -> ApplyExtrinsicResult {
	let extrinsic_index: u32 =
		storage::unhashed::get(well_known_keys::EXTRINSIC_INDEX).unwrap_or_default();
	let result = execute_transaction_backend(&utx, extrinsic_index);
	<ExtrinsicData<Runtime>>::insert(extrinsic_index, utx.encode());
	storage::unhashed::put(well_known_keys::EXTRINSIC_INDEX, &(extrinsic_index + 1));
	result
}

/// Finalize the block.
pub fn finalize_block() -> Header {
	use sp_core::storage::StateVersion;
	let extrinsic_index: u32 = storage::unhashed::take(well_known_keys::EXTRINSIC_INDEX).unwrap();
	let txs: Vec<_> = (0..extrinsic_index).map(<ExtrinsicData<Runtime>>::take).collect();
	let extrinsics_root = trie::blake2_256_ordered_root(txs, StateVersion::V0);
	let number = <Number<Runtime>>::take().expect("Number is set by `initialize_block`");
	let parent_hash = <ParentHash<Runtime>>::take();
	let mut digest =
		<StorageDigest<Runtime>>::take().expect("StorageDigest is set by `initialize_block`");

	let o_new_authorities = <NewAuthorities<Runtime>>::take();

	// This MUST come after all changes to storage are done. Otherwise we will fail the
	// “Storage root does not match that calculated” assertion.
	let storage_root = Hash::decode(&mut &storage_root(StateVersion::V1)[..])
		.expect("`storage_root` is a valid hash");

	if let Some(new_authorities) = o_new_authorities {
		digest.push(generic::DigestItem::Consensus(*b"aura", new_authorities.encode()));
		digest.push(generic::DigestItem::Consensus(*b"babe", new_authorities.encode()));
	}

	Header { number, extrinsics_root, state_root: storage_root, parent_hash, digest }
}

#[inline(always)]
fn check_signature(utx: &Extrinsic) -> Result<(), TransactionValidityError> {
	use sp_runtime::traits::BlindCheckable;
	utx.clone().check().map_err(|_| InvalidTransaction::BadProof.into()).map(|_| ())
}

fn execute_transaction_backend(utx: &Extrinsic, extrinsic_index: u32) -> ApplyExtrinsicResult {
	check_signature(utx)?;
	match utx {
		Extrinsic::Transfer { exhaust_resources_when_not_first: true, .. }
			if extrinsic_index != 0 =>
			Err(InvalidTransaction::ExhaustsResources.into()),
		Extrinsic::Transfer { ref transfer, .. } => execute_transfer_backend(transfer),
		Extrinsic::AuthoritiesChange(ref new_auth) => execute_new_authorities_backend(new_auth),
		Extrinsic::IncludeData(_) => Ok(Ok(())),
		Extrinsic::StorageChange(key, value) =>
			execute_storage_change(key, value.as_ref().map(|v| &**v)),
		Extrinsic::OffchainIndexSet(key, value) => {
			sp_io::offchain_index::set(key, value);
			Ok(Ok(()))
		},
		Extrinsic::OffchainIndexClear(key) => {
			sp_io::offchain_index::clear(key);
			Ok(Ok(()))
		},
		Extrinsic::Store(data) => execute_store(data.clone()),
	}
}

fn execute_transfer_backend(tx: &Transfer) -> ApplyExtrinsicResult {
	// check nonce
	let nonce_key = tx.from.to_keyed_vec(NONCE_OF);
	let expected_nonce: u64 = storage::hashed::get_or(&blake2_256, &nonce_key, 0);
	if tx.nonce != expected_nonce {
		return Err(InvalidTransaction::Stale.into())
	}

	// increment nonce in storage
	storage::hashed::put(&blake2_256, &nonce_key, &(expected_nonce + 1));

	// check sender balance
	let from_balance_key = tx.from.to_keyed_vec(BALANCE_OF);
	let from_balance: u64 = storage::hashed::get_or(&blake2_256, &from_balance_key, 0);

	// enact transfer
	if tx.amount > from_balance {
		return Err(InvalidTransaction::Payment.into())
	}
	let to_balance_key = tx.to.to_keyed_vec(BALANCE_OF);
	let to_balance: u64 = storage::hashed::get_or(&blake2_256, &to_balance_key, 0);
	storage::hashed::put(&blake2_256, &from_balance_key, &(from_balance - tx.amount));
	storage::hashed::put(&blake2_256, &to_balance_key, &(to_balance + tx.amount));
	Ok(Ok(()))
}

fn execute_store(data: Vec<u8>) -> ApplyExtrinsicResult {
	let content_hash = sp_io::hashing::blake2_256(&data);
	let extrinsic_index: u32 = storage::unhashed::get(well_known_keys::EXTRINSIC_INDEX).unwrap();
	sp_io::transaction_index::index(extrinsic_index, data.len() as u32, content_hash);
	Ok(Ok(()))
}

fn execute_new_authorities_backend(new_authorities: &[AuthorityId]) -> ApplyExtrinsicResult {
	<NewAuthorities<Runtime>>::put(new_authorities.to_vec());
	Ok(Ok(()))
}

fn execute_storage_change(key: &[u8], value: Option<&[u8]>) -> ApplyExtrinsicResult {
	match value {
		Some(value) => storage::unhashed::put_raw(key, value),
		None => storage::unhashed::kill(key),
	}
	Ok(Ok(()))
}

#[cfg(feature = "std")]
fn info_expect_equal_hash(given: &Hash, expected: &Hash) {
	use sp_core::hexdisplay::HexDisplay;
	if given != expected {
		println!(
			"Hash: given={}, expected={}",
			HexDisplay::from(given.as_fixed_bytes()),
			HexDisplay::from(expected.as_fixed_bytes()),
		);
	}
}

#[cfg(not(feature = "std"))]
fn info_expect_equal_hash(given: &Hash, expected: &Hash) {
	if given != expected {
		sp_runtime::print("Hash not equal");
		sp_runtime::print(given.as_bytes());
		sp_runtime::print(expected.as_bytes());
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use crate::{wasm_binary_unwrap, Header, Transfer};
	use sc_executor::{NativeElseWasmExecutor, WasmExecutionMethod};
	use sp_core::{
		map,
		traits::{CodeExecutor, RuntimeCode},
	};
	use sp_io::{hashing::twox_128, TestExternalities};
	use substrate_test_runtime_client::{AccountKeyring, Sr25519Keyring};

	// Declare an instance of the native executor dispatch for the test runtime.
	pub struct NativeDispatch;

	impl sc_executor::NativeExecutionDispatch for NativeDispatch {
		type ExtendHostFunctions = ();

		fn dispatch(method: &str, data: &[u8]) -> Option<Vec<u8>> {
			crate::api::dispatch(method, data)
		}

		fn native_version() -> sc_executor::NativeVersion {
			crate::native_version()
		}
	}

	fn executor() -> NativeElseWasmExecutor<NativeDispatch> {
		NativeElseWasmExecutor::new(WasmExecutionMethod::Interpreted, None, 8, 2)
	}

	fn new_test_ext() -> TestExternalities {
		let authorities = vec![
			Sr25519Keyring::Alice.to_raw_public(),
			Sr25519Keyring::Bob.to_raw_public(),
			Sr25519Keyring::Charlie.to_raw_public(),
		];

		TestExternalities::new_with_code(
			wasm_binary_unwrap(),
			sp_core::storage::Storage {
				top: map![
					twox_128(b"latest").to_vec() => vec![69u8; 32],
					twox_128(b"sys:auth").to_vec() => authorities.encode(),
					blake2_256(&AccountKeyring::Alice.to_raw_public().to_keyed_vec(b"balance:")).to_vec() => {
						vec![111u8, 0, 0, 0, 0, 0, 0, 0]
					},
				],
				children_default: map![],
			},
		)
	}

	fn block_import_works<F>(block_executor: F)
	where
		F: Fn(Block, &mut TestExternalities),
	{
		let h = Header {
			parent_hash: [69u8; 32].into(),
			number: 1,
			state_root: Default::default(),
			extrinsics_root: Default::default(),
			digest: Default::default(),
		};
		let mut b = Block { header: h, extrinsics: vec![] };

		new_test_ext().execute_with(|| polish_block(&mut b));

		block_executor(b, &mut new_test_ext());
	}

	#[test]
	fn block_import_works_native() {
		block_import_works(|b, ext| {
			ext.execute_with(|| {
				execute_block(b);
			})
		});
	}

	#[test]
	fn block_import_works_wasm() {
		block_import_works(|b, ext| {
			let mut ext = ext.ext();
			let runtime_code = RuntimeCode {
				code_fetcher: &sp_core::traits::WrappedRuntimeCode(wasm_binary_unwrap().into()),
				hash: Vec::new(),
				heap_pages: None,
			};

			executor()
				.call(&mut ext, &runtime_code, "Core_execute_block", &b.encode(), false)
				.0
				.unwrap();
		})
	}

	fn block_import_with_transaction_works<F>(block_executor: F)
	where
		F: Fn(Block, &mut TestExternalities),
	{
		let mut b1 = Block {
			header: Header {
				parent_hash: [69u8; 32].into(),
				number: 1,
				state_root: Default::default(),
				extrinsics_root: Default::default(),
				digest: Default::default(),
			},
			extrinsics: vec![Transfer {
				from: AccountKeyring::Alice.into(),
				to: AccountKeyring::Bob.into(),
				amount: 69,
				nonce: 0,
			}
			.into_signed_tx()],
		};

		let mut dummy_ext = new_test_ext();
		dummy_ext.execute_with(|| polish_block(&mut b1));

		let mut b2 = Block {
			header: Header {
				parent_hash: b1.header.hash(),
				number: 2,
				state_root: Default::default(),
				extrinsics_root: Default::default(),
				digest: Default::default(),
			},
			extrinsics: vec![
				Transfer {
					from: AccountKeyring::Bob.into(),
					to: AccountKeyring::Alice.into(),
					amount: 27,
					nonce: 0,
				}
				.into_signed_tx(),
				Transfer {
					from: AccountKeyring::Alice.into(),
					to: AccountKeyring::Charlie.into(),
					amount: 69,
					nonce: 1,
				}
				.into_signed_tx(),
			],
		};

		dummy_ext.execute_with(|| polish_block(&mut b2));
		drop(dummy_ext);

		let mut t = new_test_ext();

		t.execute_with(|| {
			assert_eq!(balance_of(AccountKeyring::Alice.into()), 111);
			assert_eq!(balance_of(AccountKeyring::Bob.into()), 0);
		});

		block_executor(b1, &mut t);

		t.execute_with(|| {
			assert_eq!(balance_of(AccountKeyring::Alice.into()), 42);
			assert_eq!(balance_of(AccountKeyring::Bob.into()), 69);
		});

		block_executor(b2, &mut t);

		t.execute_with(|| {
			assert_eq!(balance_of(AccountKeyring::Alice.into()), 0);
			assert_eq!(balance_of(AccountKeyring::Bob.into()), 42);
			assert_eq!(balance_of(AccountKeyring::Charlie.into()), 69);
		});
	}

	#[test]
	fn block_import_with_transaction_works_native() {
		block_import_with_transaction_works(|b, ext| {
			ext.execute_with(|| {
				execute_block(b);
			})
		});
	}

	#[test]
	fn block_import_with_transaction_works_wasm() {
		block_import_with_transaction_works(|b, ext| {
			let mut ext = ext.ext();
			let runtime_code = RuntimeCode {
				code_fetcher: &sp_core::traits::WrappedRuntimeCode(wasm_binary_unwrap().into()),
				hash: Vec::new(),
				heap_pages: None,
			};

			executor()
				.call(&mut ext, &runtime_code, "Core_execute_block", &b.encode(), false)
				.0
				.unwrap();
		})
	}
}
