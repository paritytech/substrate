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

//! System manager: Handles all of the top-level stuff; executing block/transaction, setting code
//! and depositing logs.

use rstd::prelude::*;
use runtime_io::{storage_root, enumerated_trie_root};
use runtime_support::storage::{self, StorageValue, StorageMap};
use runtime_primitives::traits::{Hash as HashT, BlakeTwo256, Digest as DigestT};
use runtime_primitives::generic;
use runtime_primitives::{ApplyError, ApplyOutcome, ApplyResult};
use codec::{KeyedVec, Encode};
use super::{AccountId, BlockNumber, Extrinsic, H256 as Hash, Block, Header, Digest};
use primitives::Blake2Hasher;
use primitives::storage::well_known_keys;

const NONCE_OF: &[u8] = b"nonce:";
const BALANCE_OF: &[u8] = b"balance:";

storage_items! {
	ExtrinsicIndex: b"sys:xti" => required u32;
	ExtrinsicData: b"sys:xtd" => required map [ u32 => Vec<u8> ];
	// The current block number being processed. Set by `execute_block`.
	Number: b"sys:num" => required BlockNumber;
	ParentHash: b"sys:pha" => required Hash;
}

pub fn balance_of(who: AccountId) -> u64 {
	storage::get_or(&who.to_keyed_vec(BALANCE_OF), 0)
}

pub fn nonce_of(who: AccountId) -> u64 {
	storage::get_or(&who.to_keyed_vec(NONCE_OF), 0)
}

/// Get authorities ar given block.
pub fn authorities() -> Vec<::primitives::AuthorityId> {
	let len: u32 = storage::unhashed::get(well_known_keys::AUTHORITY_COUNT)
		.expect("There are always authorities in test-runtime");
	(0..len)
		.map(|i| storage::unhashed::get(&i.to_keyed_vec(well_known_keys::AUTHORITY_PREFIX))
			.expect("Authority is properly encoded in test-runtime")
		)
		.collect()
}

pub fn initialise_block(header: Header) {
	// populate environment.
	<Number>::put(&header.number);
	<ParentHash>::put(&header.parent_hash);
	<ExtrinsicIndex>::put(0);
}

/// Actually execute all transitioning for `block`.
pub fn execute_block(block: Block) {
	let ref header = block.header;

	// check transaction trie root represents the transactions.
	let txs = block.extrinsics.iter().map(Encode::encode).collect::<Vec<_>>();
	let txs = txs.iter().map(Vec::as_slice).collect::<Vec<_>>();
	let txs_root = enumerated_trie_root::<Blake2Hasher>(&txs).into();
	info_expect_equal_hash(&txs_root, &header.extrinsics_root);
	assert!(txs_root == header.extrinsics_root, "Transaction trie root must be valid.");

	// execute transactions
	block.extrinsics.iter().for_each(|e| { execute_transaction_backend(e).map_err(|_| ()).expect("Extrinsic error"); });

	// check storage root.
	let storage_root = storage_root().into();
	info_expect_equal_hash(&storage_root, &header.state_root);
	assert!(storage_root == header.state_root, "Storage root must match that calculated.");
}

/// Execute a transaction outside of the block execution function.
/// This doesn't attempt to validate anything regarding the block.
pub fn execute_transaction(utx: Extrinsic) -> ApplyResult {
	let extrinsic_index = ExtrinsicIndex::get();
	ExtrinsicData::insert(extrinsic_index, utx.encode());
	ExtrinsicIndex::put(extrinsic_index + 1);
	execute_transaction_backend(&utx)
}

/// Finalise the block.
pub fn finalise_block() -> Header {
	let extrinsic_index = ExtrinsicIndex::take();
	let txs: Vec<_> = (0..extrinsic_index).map(ExtrinsicData::take).collect();
	let txs = txs.iter().map(Vec::as_slice).collect::<Vec<_>>();
	let extrinsics_root = enumerated_trie_root::<Blake2Hasher>(&txs).into();

	let number = <Number>::take();
	let parent_hash = <ParentHash>::take();
	let storage_root = BlakeTwo256::storage_root();
	let storage_changes_root = BlakeTwo256::storage_changes_root(number);

	let mut digest = Digest::default();
	if let Some(storage_changes_root) = storage_changes_root {
		digest.push(generic::DigestItem::ChangesTrieRoot::<Hash, u64>(storage_changes_root));
	}

	Header {
		number,
		extrinsics_root,
		state_root: storage_root,
		parent_hash,
		digest: digest,
	}
}

fn execute_transaction_backend(utx: &Extrinsic) -> ApplyResult {
	use runtime_primitives::traits::BlindCheckable;

	// check signature
	let utx = match utx.clone().check() {
		Ok(tx) => tx,
		Err(_) => return Err(ApplyError::BadSignature),
	};

	let tx: ::Transfer = utx.transfer;

	// check nonce
	let nonce_key = tx.from.to_keyed_vec(NONCE_OF);
	let expected_nonce: u64 = storage::get_or(&nonce_key, 0);
	if !(tx.nonce == expected_nonce) {
		return Err(ApplyError::Stale)
	}

	// increment nonce in storage
	storage::put(&nonce_key, &(expected_nonce + 1));

	// check sender balance
	let from_balance_key = tx.from.to_keyed_vec(BALANCE_OF);
	let from_balance: u64 = storage::get_or(&from_balance_key, 0);

	// enact transfer
	if !(tx.amount <= from_balance) {
		return Err(ApplyError::CantPay)
	}
	let to_balance_key = tx.to.to_keyed_vec(BALANCE_OF);
	let to_balance: u64 = storage::get_or(&to_balance_key, 0);
	storage::put(&from_balance_key, &(from_balance - tx.amount));
	storage::put(&to_balance_key, &(to_balance + tx.amount));
	Ok(ApplyOutcome::Success)
}

#[cfg(feature = "std")]
fn info_expect_equal_hash(given: &Hash, expected: &Hash) {
	use primitives::hexdisplay::HexDisplay;
	if given != expected {
		println!("Hash: given={}, expected={}", HexDisplay::from(&given.0), HexDisplay::from(&expected.0));
	}
}

#[cfg(not(feature = "std"))]
fn info_expect_equal_hash(given: &Hash, expected: &Hash) {
	if given != expected {
		::runtime_io::print("Hash not equal");
		::runtime_io::print(&given.0[..]);
		::runtime_io::print(&expected.0[..]);
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use runtime_io::{with_externalities, twox_128, TestExternalities};
	use codec::{Joiner, KeyedVec};
	use keyring::Keyring;
	use ::{Header, Digest, Extrinsic, Transfer};
	use primitives::{Blake2Hasher, RlpCodec};
	use primitives::storage::well_known_keys;

	fn new_test_ext() -> TestExternalities<Blake2Hasher, RlpCodec> {
		TestExternalities::new(map![
			twox_128(b"latest").to_vec() => vec![69u8; 32],
			twox_128(well_known_keys::AUTHORITY_COUNT).to_vec() => vec![].and(&3u32),
			twox_128(&0u32.to_keyed_vec(well_known_keys::AUTHORITY_PREFIX)).to_vec() => Keyring::Alice.to_raw_public().to_vec(),
			twox_128(&1u32.to_keyed_vec(well_known_keys::AUTHORITY_PREFIX)).to_vec() => Keyring::Bob.to_raw_public().to_vec(),
			twox_128(&2u32.to_keyed_vec(well_known_keys::AUTHORITY_PREFIX)).to_vec() => Keyring::Charlie.to_raw_public().to_vec(),
			twox_128(&Keyring::Alice.to_raw_public().to_keyed_vec(b"balance:")).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		])
	}

	fn construct_signed_tx(tx: Transfer) -> Extrinsic {
		let signature = Keyring::from_raw_public(tx.from.0).unwrap().sign(&tx.encode()).into();
		Extrinsic { transfer: tx, signature }
	}

	#[test]
	fn block_import_works() {
		let mut t = new_test_ext();

		let h = Header {
			parent_hash: [69u8; 32].into(),
			number: 1,
			state_root: hex!("0c22599e15fb5e052c84f79a2aab179ba6bb238218fd86bdd4a74ebcc87adfcd").into(),
			extrinsics_root: hex!("45b0cfc220ceec5b7c1c62c4d4193d38e4eba48e8815729ce75f9c0ab0e4c1c0").into(),
			digest: Digest { logs: vec![], },
		};

		let b = Block {
			header: h,
			extrinsics: vec![],
		};

		with_externalities(&mut t, || {
			execute_block(b);
		});
	}

	#[test]
	fn block_import_with_transaction_works() {
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			assert_eq!(balance_of(Keyring::Alice.to_raw_public().into()), 111);
			assert_eq!(balance_of(Keyring::Bob.to_raw_public().into()), 0);
		});

		let b = Block {
			header: Header {
				parent_hash: [69u8; 32].into(),
				number: 1,
				state_root: hex!("0425393fd07e2a806cfd7e990ee91dc92fe6bba34eab2bf45d5be7d67e24d467").into(),
				extrinsics_root: hex!("83fd59e8fe7cee53d7421713a09fe0abae1aec5f4db94fe5193737b12195f013").into(),
				digest: Digest { logs: vec![], },
			},
			extrinsics: vec![
				construct_signed_tx(Transfer {
					from: Keyring::Alice.to_raw_public().into(),
					to: Keyring::Bob.to_raw_public().into(),
					amount: 69,
					nonce: 0,
				})
			],
		};

		with_externalities(&mut t, || {
			execute_block(b.clone());

			assert_eq!(balance_of(Keyring::Alice.to_raw_public().into()), 42);
			assert_eq!(balance_of(Keyring::Bob.to_raw_public().into()), 69);
		});

		let b = Block {
			header: Header {
				parent_hash: b.header.hash(),
				number: 2,
				state_root: hex!("e32dd1d84d9133ca48078d2d83f2b0db19f9d47229ba98bf5ced0e9f86fac2c7").into(),
				extrinsics_root: hex!("5d2d0a93201744f0df878c33b07da40cd38e24ac2358cc2811ea640835c31b68").into(),
				digest: Digest { logs: vec![], },
			},
			extrinsics: vec![
				construct_signed_tx(Transfer {
					from: Keyring::Bob.to_raw_public().into(),
					to: Keyring::Alice.to_raw_public().into(),
					amount: 27,
					nonce: 0,
				}),
				construct_signed_tx(Transfer {
					from: Keyring::Alice.to_raw_public().into(),
					to: Keyring::Charlie.to_raw_public().into(),
					amount: 69,
					nonce: 1,
				}),
			],
		};

		with_externalities(&mut t, || {
			execute_block(b);

			assert_eq!(balance_of(Keyring::Alice.to_raw_public().into()), 0);
			assert_eq!(balance_of(Keyring::Bob.to_raw_public().into()), 42);
			assert_eq!(balance_of(Keyring::Charlie.to_raw_public().into()), 69);
		});
	}
}
