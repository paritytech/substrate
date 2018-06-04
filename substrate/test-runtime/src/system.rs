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
use runtime_primitives::traits::{Hashing, BlakeTwo256};
use codec::{KeyedVec, Slicable};
use super::{AccountId, BlockNumber, Call, UncheckedExtrinsic, H256 as Hash, Block, Header};

const NONCE_OF: &[u8] = b"nonce:";
const BALANCE_OF: &[u8] = b"balance:";
const LATEST_BLOCK_HASH: &[u8] = b"latest";
const AUTHORITY_AT: &'static[u8] = b":auth:";
const AUTHORITY_COUNT: &'static[u8] = b":auth:len";

storage_items! {
	ExtrinsicIndex: b"sys:xti" => required u32;
	ExtrinsicData: b"sys:xtd" => required map [ u32 => Vec<u8> ];
	// The current block number being processed. Set by `execute_block`.
	Number: b"sys:num" => required BlockNumber;
	ParentHash: b"sys:pha" => required Hash;
}

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
pub fn authorities() -> Vec<::primitives::AuthorityId> {
	let len: u32 = storage::unhashed::get(AUTHORITY_COUNT).expect("There are always authorities in test-runtime");
	(0..len)
		.map(|i| storage::unhashed::get(&i.to_keyed_vec(AUTHORITY_AT)).expect("Authority is properly encoded in test-runtime"))
		.collect()
}

pub fn initialise_block(header: Header) {
	// populate environment.
	<Number>::put(&header.number);
	<ParentHash>::put(&header.parent_hash);
	<ExtrinsicIndex>::put(0);
	storage::put(LATEST_BLOCK_HASH, &header.parent_hash);
}

/// Actually execute all transitioning for `block`.
pub fn execute_block(block: Block) {
	let ref header = block.header;

	// check transaction trie root represents the transactions.
	let txs = block.extrinsics.iter().map(Slicable::encode).collect::<Vec<_>>();
	let txs = txs.iter().map(Vec::as_slice).collect::<Vec<_>>();
	let txs_root = enumerated_trie_root(&txs).into();
	info_expect_equal_hash(&header.extrinsics_root, &txs_root);
	assert!(header.extrinsics_root == txs_root, "Transaction trie root must be valid.");

	// execute transactions
	block.extrinsics.iter().for_each(execute_transaction_backend);

	// check storage root.
	let storage_root = storage_root().into();
	info_expect_equal_hash(&header.state_root, &storage_root);
	assert!(header.state_root == storage_root, "Storage root must match that calculated.");
}

/// Execute a transaction outside of the block execution function.
/// This doesn't attempt to validate anything regarding the block.
pub fn execute_transaction(utx: UncheckedExtrinsic) {
	let extrinsic_index = ExtrinsicIndex::get();
	ExtrinsicData::insert(extrinsic_index, utx.encode());
	ExtrinsicIndex::put(extrinsic_index + 1);
	execute_transaction_backend(&utx);
}

/// Finalise the block.
pub fn finalise_block() -> Header {
	let extrinsic_index = ExtrinsicIndex::take();
	let txs: Vec<_> = (0..extrinsic_index).map(ExtrinsicData::take).collect();
	let txs = txs.iter().map(Vec::as_slice).collect::<Vec<_>>();
	let extrinsics_root = enumerated_trie_root(&txs).into();

	let number = <Number>::take();
	let parent_hash = <ParentHash>::take();
	let storage_root = BlakeTwo256::storage_root();

	Header {
		number,
		extrinsics_root,
		state_root: storage_root,
		parent_hash,
		digest: Default::default(),
	}
}

fn execute_transaction_backend(utx: &UncheckedExtrinsic) {
	use runtime_primitives::traits::Checkable;

	// check signature
	let utx = match utx.clone().check() {
		Ok(tx) => tx,
		Err(_) => panic!("All transactions should be properly signed"),
	};

	let ref tx = utx.as_unchecked().extrinsic;

	// check nonce
	let nonce_key = tx.signed.to_keyed_vec(NONCE_OF);
	let expected_nonce: u64 = storage::get_or(&nonce_key, 0);
	assert!(tx.index == expected_nonce, "All transactions should have the correct nonce");

	// increment nonce in storage
	storage::put(&nonce_key, &(expected_nonce + 1));

	// check sender balance
	let from_balance_key = tx.signed.to_keyed_vec(BALANCE_OF);
	let from_balance: u64 = storage::get_or(&from_balance_key, 0);

	// enact transfer
	let Call { to, amount } = tx.function.clone();
	assert!(amount <= from_balance, "All transactions should transfer at most the sender balance");
	let to_balance_key = to.to_keyed_vec(BALANCE_OF);
	let to_balance: u64 = storage::get_or(&to_balance_key, 0);
	storage::put(&from_balance_key, &(from_balance - amount));
	storage::put(&to_balance_key, &(to_balance + amount));
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
	use ::{Header, Digest, Extrinsic, UncheckedExtrinsic};

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

	fn construct_signed_tx(tx: Extrinsic) -> UncheckedExtrinsic {
		let signature = Keyring::from_raw_public(tx.signed.0).unwrap().sign(&tx.encode()).into();
		UncheckedExtrinsic { extrinsic: tx, signature }
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
				state_root: hex!("0dd8210adaf581464cc68555814a787ed491f8c608d0a0dbbf2208a6d44190b1").into(),
				extrinsics_root: hex!("65ed452ee5c22a1b3527658f921f9a052d5942762f6363a5ed6525bc017bad44").into(),
				digest: Digest { logs: vec![], },
			},
			extrinsics: vec![
				construct_signed_tx(Extrinsic {
					signed: Keyring::Alice.to_raw_public().into(),
					function: Call { to: Keyring::Bob.to_raw_public().into(), amount: 69 },
					index: 0,
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
				state_root: hex!("c93f2fd494c386fa32ee76b6198a7ccf5db12c02c3a79755fd2d4646ec2bf8d7").into(),
				extrinsics_root: hex!("f6ba96c4df7fcfbcdf58d4ad6ca360dbf7894f17a7136894edb518c0c06829e6").into(),
				digest: Digest { logs: vec![], },
			},
			extrinsics: vec![
				construct_signed_tx(Extrinsic {
					signed: Keyring::Bob.to_raw_public().into(),
					function: Call { to: Keyring::Alice.to_raw_public().into(), amount: 27 },
					index: 0,
				}),
				construct_signed_tx(Extrinsic {
					signed: Keyring::Alice.to_raw_public().into(),
					function: Call { to: Keyring::Charlie.to_raw_public().into(), amount: 69 },
					index: 1,
				})
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
