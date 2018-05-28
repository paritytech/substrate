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
use primitives::AuthorityId;
use runtime_io::{storage_root, enumerated_trie_root, ed25519_verify};
use runtime_support::{Hashable, storage};
use codec::{KeyedVec, Slicable};
use super::{AccountId, UncheckedTransaction, H256 as Hash, Block, Header};

const NONCE_OF: &[u8] = b"nonce:";
const BALANCE_OF: &[u8] = b"balance:";
const LATEST_BLOCK_HASH: &[u8] = b"latest";
const AUTHORITY_AT: &'static[u8] = b":auth:";
const AUTHORITY_COUNT: &'static[u8] = b":auth:len";

pub fn latest_block_hash() -> Hash {
	storage::get(LATEST_BLOCK_HASH).expect("There must always be a latest block")
}

pub fn balance_of(who: AccountId) -> u64 {
	storage::get_or(&who.to_keyed_vec(BALANCE_OF), 0)
}

pub fn nonce_of(who: AccountId) -> u64 {
	storage::get_or(&who.to_keyed_vec(NONCE_OF), 0)
}

/// Get authorities ar given block.
pub fn authorities() -> Vec<AuthorityId> {
	let len: u32 = storage::unhashed::get(AUTHORITY_COUNT).expect("There are always authorities in test-runtime");
	(0..len)
		.map(|i| storage::unhashed::get(&i.to_keyed_vec(AUTHORITY_AT)).expect("Authority is properly encoded in test-runtime"))
		.collect()
}

/// Actually execute all transitioning for `block`.
pub fn execute_block(block: Block) {
	let ref header = block.header;

	// check parent_hash is correct.
	assert!(
		header.number > 0 && latest_block_hash() == header.parent_hash,
		"Parent hash should be valid."
	);

	// check transaction trie root represents the transactions.
	let txs = block.transactions.iter().map(Slicable::encode).collect::<Vec<_>>();
	let txs = txs.iter().map(Vec::as_slice).collect::<Vec<_>>();
	let txs_root = enumerated_trie_root(&txs).into();
	info_expect_equal_hash(&header.extrinsics_root, &txs_root);
	assert!(header.extrinsics_root == txs_root, "Transaction trie root must be valid.");

	// execute transactions
	block.transactions.iter().for_each(execute_transaction_backend);

	// check storage root.
	let storage_root = storage_root().into();
	info_expect_equal_hash(&header.state_root, &storage_root);
	assert!(header.state_root == storage_root, "Storage root must match that calculated.");

	// put the header hash into storage.
	storage::put(LATEST_BLOCK_HASH, &header.blake2_256());
}

/// Execute a transaction outside of the block execution function.
/// This doesn't attempt to validate anything regarding the block.
pub fn execute_transaction(utx: UncheckedTransaction, header: Header) -> Header {
	execute_transaction_backend(&utx);
	header
}

/// Finalise the block - it is up the caller to ensure that all header fields are valid
/// except state-root.
pub fn finalise_block(mut header: Header) -> Header {
	header.state_root = storage_root().into();
	header
}

fn execute_transaction_backend(utx: &UncheckedTransaction) {
	// check signature
	let ref tx = utx.tx;
	let msg = ::codec::Slicable::encode(tx);
	assert!(ed25519_verify(&utx.signature.0, &msg, &tx.from),
		"All transactions should be properly signed");

	// check nonce
	let nonce_key = tx.from.to_keyed_vec(NONCE_OF);
	let expected_nonce: u64 = storage::get_or(&nonce_key, 0);
	assert!(tx.nonce == expected_nonce, "All transactions should have the correct nonce");

	// increment nonce in storage
	storage::put(&nonce_key, &(expected_nonce + 1));

	// check sender balance
	let from_balance_key = tx.from.to_keyed_vec(BALANCE_OF);
	let from_balance: u64 = storage::get_or(&from_balance_key, 0);
	assert!(tx.amount <= from_balance, "All transactions should transfer at most the sender balance");

	// enact transfer
	let to_balance_key = tx.to.to_keyed_vec(BALANCE_OF);
	let to_balance: u64 = storage::get_or(&to_balance_key, 0);
	storage::put(&from_balance_key, &(from_balance - tx.amount));
	storage::put(&to_balance_key, &(to_balance + tx.amount));
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
	use ::{Header, Digest, Transaction, UncheckedTransaction};

	fn new_test_ext() -> TestExternalities {
		map![
			twox_128(b"latest").to_vec() => vec![69u8; 32],
			twox_128(b":auth:len").to_vec() => vec![].and(&3u32),
			twox_128(&0u32.to_keyed_vec(b":auth:")).to_vec() => Keyring::Alice.to_raw_public().to_vec(),
			twox_128(&1u32.to_keyed_vec(b":auth:")).to_vec() => Keyring::Bob.to_raw_public().to_vec(),
			twox_128(&2u32.to_keyed_vec(b":auth:")).to_vec() => Keyring::Charlie.to_raw_public().to_vec(),
			twox_128(&Keyring::Alice.to_raw_public().to_keyed_vec(b"balance:")).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		]
	}

	fn construct_signed_tx(tx: Transaction) -> UncheckedTransaction {
		let signature = Keyring::from_raw_public(tx.from).unwrap().sign(&tx.encode());
		UncheckedTransaction { tx, signature }
	}

	#[test]
	fn block_import_works() {
		let mut t = new_test_ext();

		let h = Header {
			parent_hash: [69u8; 32].into(),
			number: 1,
			state_root: hex!("97dfcd1f8cbf8845fcb544f89332f1a94c1137f7d1b199ef0b0a6ed217015c3e").into(),
			extrinsics_root: hex!("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421").into(),
			digest: Digest { logs: vec![], },
		};

		let b = Block {
			header: h,
			transactions: vec![],
		};

		with_externalities(&mut t, || {
			execute_block(b);
		});
	}

	#[test]
	fn block_import_with_transaction_works() {
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			assert_eq!(balance_of(Keyring::Alice.to_raw_public()), 111);
			assert_eq!(balance_of(Keyring::Bob.to_raw_public()), 0);
		});

		let b = Block {
			header: Header {
				parent_hash: [69u8; 32].into(),
				number: 1,
				state_root: hex!("0dd8210adaf581464cc68555814a787ed491f8c608d0a0dbbf2208a6d44190b1").into(),
				extrinsics_root: hex!("5e44188712452f900acfa1b4bf4084753122ea1856d58187dd33374a2ca653b1").into(),
				digest: Digest { logs: vec![], },
			},
			transactions: vec![
				construct_signed_tx(Transaction {
					from: Keyring::Alice.to_raw_public(),
					to: Keyring::Bob.to_raw_public(),
					amount: 69,
					nonce: 0,
				})
			],
		};

		with_externalities(&mut t, || {
			execute_block(b.clone());

			assert_eq!(balance_of(Keyring::Alice.to_raw_public()), 42);
			assert_eq!(balance_of(Keyring::Bob.to_raw_public()), 69);
		});

		let b = Block {
			header: Header {
				parent_hash: b.header.blake2_256().into(),
				number: 2,
				state_root: hex!("aea7c370a9fa4075b703742c22cc4fb12759bdd7d5aa5cdd85895447f838b81b").into(),
				extrinsics_root: hex!("9ac45fbcc93fa6a8b5a3c44f04d936d53569c72a53fbc12eb58bf884f6dbfae5").into(),
				digest: Digest { logs: vec![], },
			},
			transactions: vec![
				construct_signed_tx(Transaction {
					from: Keyring::Bob.to_raw_public(),
					to: Keyring::Alice.to_raw_public(),
					amount: 27,
					nonce: 0,
				}),
				construct_signed_tx(Transaction {
					from: Keyring::Alice.to_raw_public(),
					to: Keyring::Charlie.to_raw_public(),
					amount: 69,
					nonce: 1,
				})
			],
		};

		with_externalities(&mut t, || {
			execute_block(b);

			assert_eq!(balance_of(Keyring::Alice.to_raw_public()), 0);
			assert_eq!(balance_of(Keyring::Bob.to_raw_public()), 42);
			assert_eq!(balance_of(Keyring::Charlie.to_raw_public()), 69);
		});
	}
}
