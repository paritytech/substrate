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
use runtime_std::{mem, print, storage_root, enumerated_trie_root};
use codec::{KeyedVec, Slicable};
use support::{Hashable, storage, with_env};
use primitives::{AccountId, Hash, TxOrder};
use primitives::block::{Block, Number as BlockNumber};
use primitives::transaction::UncheckedTransaction;
use primitives::runtime_function::Function;
use runtime::{staking, session};

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
		storage::put_raw(CODE, new);
	}
}

pub mod internal {
	use super::*;

	struct CheckedTransaction(UncheckedTransaction);

	/// Deposits a log and ensures it matches the blocks log data.
	pub fn deposit_log(log: &[u8]) {
		with_env(|e| {
			assert_eq!(log, &e.digest.logs[e.next_log_index].0[..]);
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
		let txs_root = enumerated_trie_root(&txs.iter().map(Vec::as_slice).collect::<Vec<_>>());
		assert!(header.transaction_root.0 == txs_root, "Transaction trie root must be valid.");

		// execute transactions
		block.transactions.iter().cloned().for_each(execute_transaction);

		staking::internal::check_new_era();
		session::internal::check_rotate_session();

		// any final checks
		final_checks(&block);


		// check storage root.
		assert!(header.state_root.0 == storage_root(), "Storage root must match that calculated.");

		// store the header hash in storage; we can't do it before otherwise there would be a
		// cyclic dependency.
		let header_hash_key = header.number.to_keyed_vec(BLOCK_HASH_AT);
		storage::put(&header_hash_key, &header.blake2_256());
	}

	/// Execute a given transaction.
	pub fn execute_transaction(utx: UncheckedTransaction) {
		use runtime_std::transaction;

		// Verify the signature is good.
		let tx = match transaction::check(utx) {
			Ok(tx) => tx,
			Err(_) => panic!("All transactions should be properly signed"),
		};

		// check nonce
		let nonce_key = tx.signed.to_keyed_vec(b"sys:non:");
		let expected_nonce: TxOrder = storage::get_or_default(&nonce_key);
		assert!(tx.nonce == expected_nonce, "All transactions should have the correct nonce");

		// increment nonce in storage
		storage::put(&nonce_key, &(expected_nonce + 1));

		// decode parameters and dispatch
		dispatch_function(&tx.function, &tx.signed);
	}

	fn dispatch_function(function: &Function, transactor: &AccountId) {
		match *function {
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
			Function::TimestampSet(t) => {
				::runtime::timestamp::public::set(t);
			}
			Function::GovernancePropose(ref proposal) => {
				::runtime::governance::public::propose(transactor, proposal);
			}
			Function::GovernanceApprove(era_index) => {
				::runtime::governance::public::approve(transactor, era_index);
			}
		}
	}
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
	use primitives::transaction::{UncheckedTransaction, Transaction};
	use primitives::runtime_function::Function;
	use primitives::block::{Header, Digest};
	use primitives::hash::{H256, H512};
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
				function: Function::StakingTransfer(two, 69),
			},
			signature: "b543b41e4b7a0270eddf57ed6c435df04bb63f71c79f6ae2530ab26c734bb4e8cd57b1c190c41d5791bcdea66a16c7339b1e883e5d0538ea2d9acea800d60a00".parse().unwrap(),
		};
		// tx: 2f8c6129d816cf51c374bc7f08c3e63ed156cf78aefb4a6550d97b87997977ee00000000000000000228000000d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a4500000000000000
		// sig: b543b41e4b7a0270eddf57ed6c435df04bb63f71c79f6ae2530ab26c734bb4e8cd57b1c190c41d5791bcdea66a16c7339b1e883e5d0538ea2d9acea800d60a00

		with_externalities(&mut t, || {
			execute_transaction(tx);
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

		let tx = UncheckedTransaction {
			transaction: Transaction {
				signed: one.clone(),
				nonce: 0,
				function: Function::StakingTransfer(two, 69),
			},
			signature: "b543b41e4b7a0270eddf57ed6c435df04bb63f71c79f6ae2530ab26c734bb4e8cd57b1c190c41d5791bcdea66a16c7339b1e883e5d0538ea2d9acea800d60a00".parse().unwrap(),
		};

		let h = Header {
			parent_hash: H256([69u8; 32]),
			number: 1,
			state_root: H256(hex!("2481853da20b9f4322f34650fea5f240dcbfb266d02db94bfa0153c31f4a29db")),
			transaction_root: H256(hex!("c4b361b976b3aa90f9f0cdd32f4afc80dd96f200145a687196388a00363c2235")),
			digest: Digest { logs: vec![], },
		};

		let b = Block {
			header: h,
			transactions: vec![tx],
		};

		with_externalities(&mut t, || {
			execute_block(b);
			assert_eq!(staking::balance(&one), 42);
			assert_eq!(staking::balance(&two), 69);
		});
	}

	#[test]
	#[should_panic]
	fn block_import_of_bad_state_root_fails() {
		let one = one();
		let two = two();

		let mut t = new_test_ext();

		let tx = UncheckedTransaction {
			transaction: Transaction {
				signed: one.clone(),
				nonce: 0,
				function: Function::StakingTransfer(two, 69),
			},
			signature: "679fcf0a846b4224c84ecad7d91a26241c46d00cb53d6480a363274e8965ee34b0b80b4b2e3836d3d8f8f12c0c1aef7350af587d9aee3883561d11726068ac0a".parse().unwrap(),
		};
		// tx: 2f8c6129d816cf51c374bc7f08c3e63ed156cf78aefb4a6550d97b87997977ee00000000000000000228000000d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a4500000000000000
		// sig: 679fcf0a846b4224c84ecad7d91a26241c46d00cb53d6480a363274e8965ee34b0b80b4b2e3836d3d8f8f12c0c1aef7350af587d9aee3883561d11726068ac0a

		let h = Header {
			parent_hash: H256([69u8; 32]),
			number: 1,
			state_root: H256([0u8; 32]),
			transaction_root: H256([0u8; 32]),	// Unchecked currently.
			digest: Digest { logs: vec![], },
		};

		let b = Block {
			header: h,
			transactions: vec![tx],
		};

		with_externalities(&mut t, || {
			execute_block(b);
			assert_eq!(staking::balance(&one), 42);
			assert_eq!(staking::balance(&two), 69);
		});
	}
}
