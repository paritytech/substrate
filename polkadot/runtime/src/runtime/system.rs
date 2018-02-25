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

use rstd::prelude::*;
use rstd::mem;
use runtime_io::{print, storage_root, enumerated_trie_root};
use codec::{KeyedVec, Slicable};
use runtime_support::{Hashable, storage};
use environment::with_env;
use polkadot_primitives::{AccountId, Hash, TxOrder, BlockNumber, Block, Header,
	UncheckedTransaction, Function, InherentFunction, Log};
use runtime::{staking, session};

const NONCE_OF: &[u8] = b"sys:non:";
const BLOCK_HASH_AT: &[u8] = b"sys:old:";
const TEMP_TRANSACTION_NUMBER: &[u8] = b"temp:txcount:";

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

	struct CheckedTransaction(UncheckedTransaction);

	/// Deposits a log and ensures it matches the blocks log data.
	pub fn deposit_log(log: Log) {
		with_env(|e| e.digest.logs.push(log));
	}

	/// Actually execute all transitioning for `block`.
	pub fn execute_block(mut block: Block) {
		// populate environment from header.
		with_env(|e| {
			e.block_number = block.header.number;
			e.parent_hash = block.header.parent_hash;
		});

		// any initial checks
		initial_checks(&block);

		// execute all transactions, inherent or otherwise.
		for (tx_num, tx) in block.all_transactions().enumerate() {
			super::execute_transaction(tx, tx_num as u64);
		}

		// post-transactional book-keeping.
		staking::internal::check_new_era();
		session::internal::check_rotate_session();

		// any final checks
		final_checks(&block);

		// any stuff that we do after taking the storage root.
		post_finalise(&block.header);
	}

	/// Execute a transaction outside of the block execution function.
	/// This doesn't attempt to validate anything regarding the block.
	/// Note that when building a block transaction by transaction, the
	/// inherent methods must be called manually.
	pub fn execute_transaction(utx: UncheckedTransaction, mut header: Header) -> Header {
		// populate environment from header.
		with_env(|e| {
			e.block_number = header.number;
			e.parent_hash = header.parent_hash;
			mem::swap(&mut header.digest, &mut e.digest);
		});

		let tx_num: u64 = storage::get_or_default(TEMP_TRANSACTION_NUMBER);

		super::execute_transaction(utx, tx_num);

		with_env(|e| {
			mem::swap(&mut header.digest, &mut e.digest);
		});

		storage::put(TEMP_TRANSACTION_NUMBER, &(tx_num + 1));

		header
	}

	/// Finalise the block - it is up the caller to ensure that all header fields are valid
	/// except state-root.
	pub fn finalise_block(mut header: Header) -> Header {
		// populate environment from header.
		with_env(|e| {
			e.block_number = header.number;
			e.parent_hash = header.parent_hash;
			mem::swap(&mut header.digest, &mut e.digest);
		});

		let tx_count: u64 = storage::take_or_default(TEMP_TRANSACTION_NUMBER);
		if tx_count < Function::inherent_functions() {
			panic!("Not enough transactions provided to fulfill all inherent functions.");
		}

		staking::internal::check_new_era();
		session::internal::check_rotate_session();

		header.state_root = storage_root().into();
		with_env(|e| {
			mem::swap(&mut header.digest, &mut e.digest);
		});

		post_finalise(&header);

		header
	}
}

/// Dispatch a function.
fn dispatch_function(function: &Function, transactor: &AccountId) {
	match *function {
		Function::Inherent(InherentFunction::TimestampSet(t)) => {
			::runtime::timestamp::public::set(t);
		}
		Function::StakingStake => {
			::runtime::staking::public::stake(transactor);
		}
		Function::StakingUnstake => {
			::runtime::staking::public::unstake(transactor);
		}
		Function::StakingTransfer(dest, value) => {
			::runtime::staking::public::transfer(transactor, &dest, value);
		}
		Function::SessionSetKey(session) => {
			::runtime::session::public::set_key(transactor, &session);
		}
		Function::GovernancePropose(ref proposal) => {
			::runtime::governance::public::propose(transactor, proposal);
		}
		Function::GovernanceApprove(era_index) => {
			::runtime::governance::public::approve(transactor, era_index);
		}
	}
}

fn execute_transaction(utx: UncheckedTransaction, tx_num: u64) {
	use ::transaction;

	// Verify the transaction is authenticated at its position.
	let tx = match transaction::check(utx, tx_num) {
		Ok(tx) => tx,
		Err(_) => panic!("Transaction at index {} not properly authenticated", tx_num),
	};

	// check nonce
	let nonce_key = tx.signed.to_keyed_vec(NONCE_OF);
	let (expected_nonce, increment_nonce) = if !tx.function.is_inherent() {
		(storage::get_or(&nonce_key, 0), true)
	} else {
		(0, false)
	};

	assert!(tx.nonce == expected_nonce, "All transactions should have the correct nonce");

	// increment nonce in storage, unless it's the EVERYBODY account.
	if increment_nonce {
		storage::put(&nonce_key, &(expected_nonce + 1));
	}

	// decode parameters and dispatch
	dispatch_function(&tx.function, &tx.signed);
}

fn initial_checks(block: &Block) {
	let ref header = block.header;

	// check parent_hash is correct.
	assert!(
		header.number > 0 && block_hash(header.number - 1) == header.parent_hash,
		"Parent hash should be valid."
	);

	// check transaction trie root represents the transactions.
	let txs = block.all_transactions().map(|tx| Slicable::encode(&tx)).collect::<Vec<_>>();
	let txs = txs.iter().map(Vec::as_slice).collect::<Vec<_>>();
	let txs_root = enumerated_trie_root(&txs).into();
	info_expect_equal_hash(&header.transaction_root, &txs_root);
	assert!(header.transaction_root == txs_root, "Transaction trie root must be valid.");
}

fn final_checks(block: &Block) {
	let ref header = block.header;

	// check digest
	with_env(|e| {
		assert!(header.digest == e.digest);
	});

	// check storage root.
	let storage_root = storage_root().into();
	info_expect_equal_hash(&header.state_root, &storage_root);
	assert!(header.state_root == storage_root, "Storage root must match that calculated.");
}

fn post_finalise(header: &Header) {
	// store the header hash in storage; we can't do it before otherwise there would be a
	// cyclic dependency.
	storage::put(&header.number.to_keyed_vec(BLOCK_HASH_AT), &header.blake2_256());
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
		print("Hash not equal");
		print(&given.0[..]);
		print(&expected.0[..]);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use super::internal::*;

	use runtime_io::{with_externalities, twox_128, TestExternalities};
	use codec::{Joiner, KeyedVec, Slicable};
	use keyring::Keyring;
	use environment::with_env;
	use primitives::hexdisplay::HexDisplay;
	use polkadot_primitives::{Header, Body, Digest, UncheckedTransaction, Transaction, Function, InherentFunction};
	use runtime::staking;

	fn set_timestamp() -> UncheckedTransaction {
		UncheckedTransaction::inherent(InherentFunction::TimestampSet(100_000))
	}

	#[test]
	#[should_panic]
	fn fails_if_first_not_timestamp_set() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();

		let mut t: TestExternalities = map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		];

		let tx = UncheckedTransaction {
			transaction: Transaction {
				signed: one.clone(),
				nonce: 0,
				function: Function::StakingTransfer(two, 69),
			},
			signature: hex!("5f9832c5a4a39e2dd4a3a0c5b400e9836beb362cb8f7d845a8291a2ae6fe366612e080e4acd0b5a75c3d0b6ee69614a68fb63698c1e76bf1f2dcd8fa617ddf05").into(),
		};

		with_externalities(&mut t, || {
			internal::execute_transaction(tx, Header::from_block_number(1));
		});
	}

	#[test]
	fn staking_balance_transfer_dispatch_works() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();

		let mut t: TestExternalities = map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		];

		let tx = UncheckedTransaction {
			transaction: Transaction {
				signed: one.clone(),
				nonce: 0,
				function: Function::StakingTransfer(two, 69),
			},
			signature: hex!("5f9832c5a4a39e2dd4a3a0c5b400e9836beb362cb8f7d845a8291a2ae6fe366612e080e4acd0b5a75c3d0b6ee69614a68fb63698c1e76bf1f2dcd8fa617ddf05").into(),
		};

		with_externalities(&mut t, || {
			let header = Header::from_block_number(1);
			let header = internal::execute_transaction(set_timestamp(), header);
			internal::execute_transaction(tx, header);
			assert_eq!(staking::balance(&one), 42);
			assert_eq!(staking::balance(&two), 69);
		});
	}

	fn new_test_ext() -> TestExternalities {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();
		let three = [3u8; 32];

		map![
			twox_128(&0u64.to_keyed_vec(b"sys:old:")).to_vec() => [69u8; 32].encode(),
			twox_128(b"gov:apr").to_vec() => vec![].and(&667u32),
			twox_128(b"ses:len").to_vec() => vec![].and(&2u64),
			twox_128(b"ses:val:len").to_vec() => vec![].and(&3u32),
			twox_128(&0u32.to_keyed_vec(b"ses:val:")).to_vec() => one.to_vec(),
			twox_128(&1u32.to_keyed_vec(b"ses:val:")).to_vec() => two.to_vec(),
			twox_128(&2u32.to_keyed_vec(b"ses:val:")).to_vec() => three.to_vec(),
			twox_128(b"sta:wil:len").to_vec() => vec![].and(&3u32),
			twox_128(&0u32.to_keyed_vec(b"sta:wil:")).to_vec() => one.to_vec(),
			twox_128(&1u32.to_keyed_vec(b"sta:wil:")).to_vec() => two.to_vec(),
			twox_128(&2u32.to_keyed_vec(b"sta:wil:")).to_vec() => three.to_vec(),
			twox_128(b"sta:spe").to_vec() => vec![].and(&2u64),
			twox_128(b"sta:vac").to_vec() => vec![].and(&3u64),
			twox_128(b"sta:era").to_vec() => vec![].and(&0u64),
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		]
	}

	#[test]
	fn block_import_works() {
		let mut t = new_test_ext();

		let h = Header {
			parent_hash: [69u8; 32].into(),
			number: 1,
			state_root: hex!("aa4fbcdc09b21e4366aebccd9b9ec0831a8a2765c712d3397f121ff8e60e21e2").into(),
			transaction_root: hex!("328ae80be3adf358d2a2e188cbe1bfd3f8cd5b15a2e7666e2b4eccf7450efc32").into(),
			digest: Digest { logs: vec![], },
		};

		let b = Block {
			header: h,
			body: Body {
				timestamp: 100_000,
				transactions: vec![]
			}
		};

		with_externalities(&mut t, || {
			execute_block(b);
		});
	}

	#[test]
	#[should_panic]
	fn block_import_of_bad_state_root_fails() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();

		let mut t = new_test_ext();

		let h = Header {
			parent_hash: [69u8; 32].into(),
			number: 1,
			state_root: [0u8; 32].into(),
			transaction_root: hex!("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421").into(),
			digest: Digest { logs: vec![], },
		};

		let b = Block {
			header: h,
			body: Body {
				timestamp: 100_000,
				transactions: vec![],
			}
		};

		with_externalities(&mut t, || {
			execute_block(b);
		});
	}

	#[test]
	#[should_panic]
	fn block_import_of_bad_transaction_root_fails() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();

		let mut t = new_test_ext();

		let h = Header {
			parent_hash: [69u8; 32].into(),
			number: 1,
			state_root: hex!("1ab2dbb7d4868a670b181327b0b6a58dc64b10cfb9876f737a5aa014b8da31e0").into(),
			transaction_root: [0u8; 32].into(),
			digest: Digest { logs: vec![], },
		};

		let b = Block {
			header: h,
			body: Body {
				timestamp: 100_000,
				transactions: vec![],
			}
		};

		with_externalities(&mut t, || {
			execute_block(b);
		});
	}
}
