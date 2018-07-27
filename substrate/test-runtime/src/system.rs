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
use runtime_primitives::traits::{Hash as HashT, BlakeTwo256};
use runtime_primitives::{ApplyError, ApplyOutcome, ApplyResult};
use codec::{KeyedVec, Encode};
use super::{AccountId, BlockNumber, Extrinsic, H256 as Hash, Block, Header};

const NONCE_OF: &[u8] = b"nonce:";
const BALANCE_OF: &[u8] = b"balance:";
const AUTHORITY_AT: &'static[u8] = b":auth:";
const AUTHORITY_COUNT: &'static[u8] = b":auth:len";

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
}

/// Actually execute all transitioning for `block`.
pub fn execute_block(block: Block) {
	let ref header = block.header;

	// check transaction trie root represents the transactions.
	let txs = block.extrinsics.iter().map(Encode::encode).collect::<Vec<_>>();
	let txs = txs.iter().map(Vec::as_slice).collect::<Vec<_>>();
	let txs_root = enumerated_trie_root(&txs).into();
	info_expect_equal_hash(&header.extrinsics_root, &txs_root);
	assert!(header.extrinsics_root == txs_root, "Transaction trie root must be valid.");

	// execute transactions
	block.extrinsics.iter().for_each(|e| { execute_transaction_backend(e).map_err(|_| ()).expect("Extrinsic error"); });

	// check storage root.
	let storage_root = storage_root().into();
	info_expect_equal_hash(&header.state_root, &storage_root);
	assert!(header.state_root == storage_root, "Storage root must match that calculated.");
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
				extrinsics_root: hex!("951508f2cc0071500a74765ab0fb2f280fdcdd329d5f989dda675010adee99d6").into(),
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
				state_root: hex!("c93f2fd494c386fa32ee76b6198a7ccf5db12c02c3a79755fd2d4646ec2bf8d7").into(),
				extrinsics_root: hex!("3563642676d7e042c894eedc579ba2d6eeedf9a6c66d9d557599effc9f674372").into(),
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
