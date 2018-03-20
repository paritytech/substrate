// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! System manager: Handles all of the top-level stuff; executing block/transaction, setting code
//! and depositing logs.

use rstd::prelude::*;
use rstd::mem;
use runtime_io::{print, storage_root, enumerated_trie_root};
use codec::{KeyedVec, Slicable};
use runtime_support::{Hashable, storage, StorageValue, StorageMap};
use demo_primitives::{AccountId, Hash, TxOrder, BlockNumber, Header, Log};
use block::{self, Block};
use transaction::UncheckedTransaction;
use runtime::{staking, session};
use runtime::democracy::PrivPass;
use dispatch;
use safe_mix::TripletMix;

storage_items! {
	pub Nonce get(nonce): b"sys:non" => default map [ AccountId => TxOrder ];
	pub BlockHashAt get(block_hash): b"sys:old" => required map [ BlockNumber => Hash ];
	RandomSeed get(random_seed): b"sys:rnd" => required Hash;
	// The current block number being processed. Set by `execute_block`.
	Number get(block_number): b"sys:num" => required BlockNumber;
	ParentHash get(parent_hash): b"sys:pha" => required Hash;
	TransactionsRoot get(transactions_root): b"sys:txr" => required Hash;
	Digest: b"sys:dig" => default block::Digest;
}

pub const CODE: &'static[u8] = b":code";

impl_dispatch! {
	pub mod privileged;
	fn set_code(new: Vec<u8>) = 0;
}

impl privileged::Dispatch for PrivPass {
	/// Set the new code.
	fn set_code(self, new: Vec<u8>) {
		storage::unhashed::put_raw(CODE, &new);
	}
}

pub mod internal {
	use super::*;

	struct CheckedTransaction(UncheckedTransaction);

	/// Deposits a log and ensures it matches the blocks log data.
	pub fn deposit_log(log: Log) {
		let mut l = Digest::get();
		l.logs.push(log);
		Digest::put(l);
	}

	/// Actually execute all transitioning for `block`.
	pub fn execute_block(mut block: Block) {
		initialise_block(&block.header);

		// any initial checks
		initial_checks(&block);

		// execute transactions
		block.transactions.iter().cloned().for_each(super::execute_transaction);

		// post-transactional book-keeping.
		staking::internal::check_new_era();
		session::internal::check_rotate_session();

		// any final checks
		final_checks(&block);

		// any stuff that we do after taking the storage root.
		post_finalise(&block.header);
	}

	/// Start the execution of a particular block.
	pub fn initialise_block(mut header: &Header) {
		// populate environment from header.
		Number::put(header.number);
		ParentHash::put(header.parent_hash);
		TransactionsRoot::put(header.transaction_root);
		RandomSeed::put(calculate_random());
	}

	/// Execute a transaction outside of the block execution function.
	/// This doesn't attempt to validate anything regarding the block.
	pub fn execute_transaction(utx: UncheckedTransaction) {
		super::execute_transaction(utx);
	}

	/// Finalise the block - it is up the caller to ensure that all header fields are valid
	/// except state-root.
	pub fn finalise_block() -> Header {
		staking::internal::check_new_era();
		session::internal::check_rotate_session();

		RandomSeed::kill();
		let header = Header {
			number: Number::take(),
			digest: Digest::take(),
			parent_hash: ParentHash::take(),
			transaction_root: TransactionsRoot::take(),
			state_root: storage_root().into(),
		};

		post_finalise(&header);

		header
	}
}

fn execute_transaction(utx: UncheckedTransaction) {
	use ::transaction;

	// Verify the signature is good.
	let tx = match transaction::check(utx) {
		Ok(tx) => tx,
		Err(_) => panic!("All transactions should be properly signed"),
	};

	{
		// check nonce
		let expected_nonce: TxOrder = Nonce::get(&tx.signed);
		assert!(tx.nonce == expected_nonce, "All transactions should have the correct nonce");

		// increment nonce in storage
		Nonce::insert(&tx.signed, &(expected_nonce + 1));
	}

	// decode parameters and dispatch
	let tx = tx.drain().transaction;
	tx.function.dispatch(staking::PublicPass::new(&tx.signed));
}

fn initial_checks(block: &Block) {
	let ref header = block.header;

	// check parent_hash is correct.
	assert!(
		header.number > 0 && BlockHashAt::get(&(header.number - 1)) == header.parent_hash,
		"Parent hash should be valid."
	);

	// check transaction trie root represents the transactions.
	let txs = block.transactions.iter().map(Slicable::encode).collect::<Vec<_>>();
	let txs = txs.iter().map(Vec::as_slice).collect::<Vec<_>>();
	let txs_root = enumerated_trie_root(&txs).into();
	info_expect_equal_hash(&header.transaction_root, &txs_root);
	assert!(header.transaction_root == txs_root, "Transaction trie root must be valid.");
}

fn final_checks(block: &Block) {
	let ref header = block.header;

	// check digest
	assert!(header.digest == Digest::get());

	// remove temporaries.
	kill_temps();

	// check storage root.
	let storage_root = storage_root().into();
	info_expect_equal_hash(&header.state_root, &storage_root);
	assert!(header.state_root == storage_root, "Storage root must match that calculated.");
}

fn kill_temps() {
	Number::kill();
	ParentHash::kill();
	RandomSeed::kill();
	Digest::kill();
	TransactionsRoot::kill();
}

fn post_finalise(header: &Header) {
	// store the header hash in storage; we can't do it before otherwise there would be a
	// cyclic dependency.
	BlockHashAt::insert(&header.number, &header.blake2_256().into());
}

fn calculate_random() -> Hash {
	let c = block_number() - 1;
	(0..81)
		.map(|i| if c >= i { block_hash(c - i) } else { Default::default() })
		.triplet_mix()
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

#[cfg(any(feature = "std", test))]
pub mod testing {
	use super::*;
	use runtime_io::{twox_128, TestExternalities};
	use codec::Joiner;

	pub fn externalities() -> TestExternalities {
		map![
			twox_128(&BlockHashAt::key_for(&0)).to_vec() => [69u8; 32].encode(),
			twox_128(Number::key()).to_vec() => 1u64.encode(),
			twox_128(ParentHash::key()).to_vec() => [69u8; 32].encode(),
			twox_128(RandomSeed::key()).to_vec() => [0u8; 32].encode()
		]
	}

	pub fn set_block_number(n: BlockNumber) {
		Number::put(n);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use super::internal::*;

	use runtime_io::{with_externalities, twox_128, TestExternalities};
	use runtime_support::StorageValue;
	use codec::{Joiner, KeyedVec, Slicable};
	use keyring::Keyring::*;
	use primitives::hexdisplay::HexDisplay;
	use demo_primitives::{Header, Digest};
	use transaction::{UncheckedTransaction, Transaction};
	use runtime::staking;
	use dispatch::public::Call as PubCall;
	use runtime::staking::public::Call as StakingCall;

	#[test]
	fn staking_balance_transfer_dispatch_works() {
		let mut t: TestExternalities = map![
			twox_128(&staking::FreeBalanceOf::key_for(*One)).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(staking::TransactionFee::key()).to_vec() => vec![10u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(&BlockHashAt::key_for(&0)).to_vec() => [69u8; 32].encode()
		];

		let tx = UncheckedTransaction {
			transaction: Transaction {
				signed: One.into(),
				nonce: 0,
				function: PubCall::Staking(StakingCall::transfer(Two.into(), 69)),
			},
			signature: hex!("3a682213cb10e8e375fe0817fe4d220a4622d910088809ed7fc8b4ea3871531dbadb22acfedd28a100a0b7bd2d274e0ff873655b13c88f4640b5569db3222706").into(),
		};

		with_externalities(&mut t, || {
			internal::initialise_block(&Header::from_block_number(1));
			internal::execute_transaction(tx);
			assert_eq!(staking::balance(&One), 32);
			assert_eq!(staking::balance(&Two), 69);
		});
	}

	fn new_test_ext() -> TestExternalities {
		staking::testing::externalities(2, 2, 0)
	}

	#[test]
	fn block_import_works() {
		let mut t = new_test_ext();

		let h = Header {
			parent_hash: [69u8; 32].into(),
			number: 1,
			state_root: hex!("cc3f1f5db826013193e502c76992b5e933b12367e37a269a9822b89218323e9f").into(),
			transaction_root: hex!("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421").into(),
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
			transactions: vec![],
		};

		with_externalities(&mut t, || {
			execute_block(b);
		});
	}

	#[test]
	#[should_panic]
	fn block_import_of_bad_transaction_root_fails() {
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
			transactions: vec![],
		};

		with_externalities(&mut t, || {
			execute_block(b);
		});
	}
}
