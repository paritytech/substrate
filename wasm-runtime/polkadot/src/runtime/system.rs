// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! System manager: Handles all of the top-level stuff; executing block/transaction, setting code
//! and depositing logs.

use runtime_std::prelude::*;
use runtime_std::{mem, storage_root, enumerated_trie_root};
use codec::{KeyedVec, Slicable};
use support::{Hashable, storage, with_env};
use primitives::{Block, BlockNumber, Hash, UncheckedTransaction, TxOrder};
use runtime::{staking, session};

const NONCE_OF: &[u8] = b"sys:non:";
const BLOCK_HASH_AT: &[u8] = b"sys:old:";
const CODE: &[u8] = b"sys:cod";

/// The current block number being processed. Set by `execute_block`.
pub fn block_number() -> BlockNumber {
	with_env(|e| e.block_number)
}

/// Get the block hash of a given block (uses storage).
pub fn block_hash(number: BlockNumber) -> Hash {
	storage::get_or_default(&number.to_keyed_vec(BLOCK_HASH_AT))
}

pub mod privileged {
	use super::*;

	/// Set the new code.
	pub fn set_code(new: &[u8]) {
		storage::unhashed::put_raw(b":code", new);
	}
}

pub mod internal {
	use super::*;

	/// Deposits a log and ensures it matches the blocks log data.
	pub fn deposit_log(log: &[u8]) {
		with_env(|e| {
			assert_eq!(log, &e.digest.logs[e.next_log_index][..]);
			e.next_log_index += 1;
		});
	}

	/// Actually execute all transitioning for `block`.
	pub fn execute_block(mut block: Block) {
		// populate environment from header.
		with_env(|e| {
			e.block_number = block.header.number;
			mem::swap(&mut e.digest, &mut block.header.digest);
			e.next_log_index = 0;
		});

		let ref header = block.header;

		// check parent_hash is correct.
		assert!(
			header.number > 0 && block_hash(header.number - 1) == header.parent_hash,
			"Parent hash should be valid."
		);

		// check transaction trie root represents the transactions.
		let txs = block.transactions.iter().map(Slicable::to_vec).collect::<Vec<_>>();
		let txs = txs.iter().map(Vec::as_slice).collect::<Vec<_>>();
		let txs_root = enumerated_trie_root(&txs);
		debug_assert_hash(&header.transaction_root, &txs_root);
		assert!(header.transaction_root == txs_root, "Transaction trie root must be valid.");

		// execute transactions
		for tx in &block.transactions {
			execute_transaction(tx);
		}

		staking::internal::check_new_era();
		session::internal::check_rotate_session();

		// any final checks
		final_checks(&block);

		// check storage root.
		let storage_root = storage_root();
		debug_assert_hash(&header.state_root, &storage_root);
		assert!(header.state_root == storage_root, "Storage root must match that calculated.");

		// store the header hash in storage; we can't do it before otherwise there would be a
		// cyclic dependency.
		let header_hash_key = header.number.to_keyed_vec(BLOCK_HASH_AT);
		storage::put(&header_hash_key, &header.blake2_256());
	}

	/// Execute a given transaction.
	pub fn execute_transaction(utx: &UncheckedTransaction) {
		// Verify the signature is good.
		assert!(utx.ed25519_verify(), "All transactions should be properly signed");

		let ref tx = utx.transaction;

		// check nonce
		let nonce_key = tx.signed.to_keyed_vec(NONCE_OF);
		let expected_nonce: TxOrder = storage::get_or(&nonce_key, 0);
		assert!(tx.nonce == expected_nonce, "All transactions should have the correct nonce");

		// increment nonce in storage
		storage::put(&nonce_key, &(expected_nonce + 1));

		// decode parameters and dispatch
		tx.function.dispatch(&tx.signed, &tx.input_data);
	}

	#[cfg(feature = "with-std")]
	fn debug_assert_hash(given: &Hash, expected: &Hash) {
		use support::HexDisplay;
		if given != expected {
			println!("Hash: given={}, expected={}", HexDisplay::from(given), HexDisplay::from(expected));
		}
	}

	#[cfg(not(feature = "with-std"))]
	fn debug_assert_hash(_given: &Hash, _expected: &Hash) {}
}

fn final_checks(_block: &Block) {
	with_env(|e| {
		assert_eq!(e.next_log_index, e.digest.logs.len());
	});
}

#[cfg(test)]
mod tests {
	use super::*;
	use super::internal::*;

	use runtime_std::{with_externalities, twox_128, TestExternalities};
	use codec::{Joiner, KeyedVec, Slicable};
	use support::{StaticHexInto, HexDisplay, one, two};
	use primitives::{UncheckedTransaction, Transaction, Function, Header, Digest};
	use runtime::staking;

	#[test]
	fn staking_balance_transfer_dispatch_works() {
		let one = one();
		let two = two();

		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		let tx = UncheckedTransaction {
			transaction: Transaction {
				signed: one.clone(),
				nonce: 0,
				function: Function::StakingTransfer,
				input_data: vec![].join(&two).join(&69u64),
			},
			signature: "13590ae48241e29780407687b86c331a9f40f3ab7f2cc2441787628bcafab6645dc81863b138a358e2a1ed1ffa940a4584ba94837f022f0cd162791530320904".convert(),
		};

		println!("tx is {}", HexDisplay::from(&tx.transaction.to_vec()));

		with_externalities(&mut t, || {
			execute_transaction(&tx);
			assert_eq!(staking::balance(&one), 42);
			assert_eq!(staking::balance(&two), 69);
		});
	}

	fn new_test_ext() -> TestExternalities {
		let one = one();
		let two = two();
		let three = [3u8; 32];

		TestExternalities { storage: map![
			twox_128(&0u64.to_keyed_vec(b"sys:old:")).to_vec() => [69u8; 32].to_vec(),
			twox_128(b"gov:apr").to_vec() => vec![].join(&667u32),
			twox_128(b"ses:len").to_vec() => vec![].join(&2u64),
			twox_128(b"ses:val:len").to_vec() => vec![].join(&3u32),
			twox_128(&0u32.to_keyed_vec(b"ses:val:")).to_vec() => one.to_vec(),
			twox_128(&1u32.to_keyed_vec(b"ses:val:")).to_vec() => two.to_vec(),
			twox_128(&2u32.to_keyed_vec(b"ses:val:")).to_vec() => three.to_vec(),
			twox_128(b"sta:wil:len").to_vec() => vec![].join(&3u32),
			twox_128(&0u32.to_keyed_vec(b"sta:wil:")).to_vec() => one.to_vec(),
			twox_128(&1u32.to_keyed_vec(b"sta:wil:")).to_vec() => two.to_vec(),
			twox_128(&2u32.to_keyed_vec(b"sta:wil:")).to_vec() => three.to_vec(),
			twox_128(b"sta:spe").to_vec() => vec![].join(&2u64),
			twox_128(b"sta:vac").to_vec() => vec![].join(&3u64),
			twox_128(b"sta:era").to_vec() => vec![].join(&0u64),
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		], }
	}

	#[test]
	fn block_import_works() {
		let one = one();
		let two = two();

		let mut t = new_test_ext();

		let h = Header {
			parent_hash: [69u8; 32],
			number: 1,
			state_root: hex!("1ab2dbb7d4868a670b181327b0b6a58dc64b10cfb9876f737a5aa014b8da31e0"),
			transaction_root: hex!("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"),
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
	#[should_panic]
	fn block_import_of_bad_state_root_fails() {
		let one = one();
		let two = two();

		let mut t = new_test_ext();

		let h = Header {
			parent_hash: [69u8; 32],
			number: 1,
			state_root: [0u8; 32],
			transaction_root: hex!("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"),
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
	#[should_panic]
	fn block_import_of_bad_transaction_root_fails() {
		let one = one();
		let two = two();

		let mut t = new_test_ext();

		let h = Header {
			parent_hash: [69u8; 32],
			number: 1,
			state_root: hex!("1ab2dbb7d4868a670b181327b0b6a58dc64b10cfb9876f737a5aa014b8da31e0"),
			transaction_root: [0u8; 32],
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
}
