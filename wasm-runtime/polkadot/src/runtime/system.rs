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

use primitives::{Block, BlockNumber, Hash, UncheckedTransaction, TxOrder, Hashable};
use runtime_support::mem;
use runtime_support::vec::Vec;
use storable::Storable;
use keyedvec::KeyedVec;
use environment::with_env;
use runtime::{staking, session};

/// The current block number being processed. Set by `execute_block`.
pub fn block_number() -> BlockNumber {
	with_env(|e| e.block_number)
}

/// Get the block hash of a given block (uses storage).
pub fn block_hash(number: BlockNumber) -> Hash {
	Storable::lookup_default(&number.to_keyed_vec(b"sys:old:"))
}

/// Deposits a log and ensures it matches the blocks log data.
pub fn deposit_log(log: &[u8]) {
	with_env(|e| {
		assert_eq!(log, &e.digest.logs[e.next_log_index][..]);
		e.next_log_index += 1;
	});
}

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

	// TODO: check transaction trie root represents the transactions.
	// this requires non-trivial changes to the externals API or compiling trie rooting into wasm
	// so will wait until a little later.

	// store the header hash in storage.
	let header_hash_key = header.number.to_keyed_vec(b"sys:old:");
	header.blake2_256().store(&header_hash_key);

	// execute transactions
	block.transactions.iter().for_each(execute_transaction);

	staking::check_new_era();
	session::check_rotate_session();

	// any final checks
	final_checks(&block);

	// TODO: check storage root.
	// this requires non-trivial changes to the externals API or compiling trie rooting into wasm
	// so will wait until a little later.
}

/// Execute a given transaction.
pub fn execute_transaction(utx: &UncheckedTransaction) {
	// Verify the signature is good.
	assert!(utx.ed25519_verify(), "All transactions should be properly signed");

	let ref tx = utx.transaction;

	// check nonce
	let nonce_key = tx.signed.to_keyed_vec(b"sys:non:");
	let expected_nonce: TxOrder = Storable::lookup_default(&nonce_key);
	assert!(tx.nonce == expected_nonce, "All transactions should have the correct nonce");

	// increment nonce in storage
	(expected_nonce + 1).store(&nonce_key);

	// decode parameters and dispatch
	tx.function.dispatch(&tx.signed, &tx.input_data);
}

/// Set the new code.
pub fn set_code(new: &[u8]) {
	new.store(b":code");
}

fn final_checks(_block: &Block) {
	with_env(|e| {
		assert_eq!(e.next_log_index, e.digest.logs.len());
	});
}

#[cfg(test)]
mod tests {
	use joiner::Joiner;
	use function::Function;
	use keyedvec::KeyedVec;
	use slicable::Slicable;
	use runtime_support::{with_externalities, twox_128};
	use primitives::{UncheckedTransaction, Transaction};
	use statichex::StaticHexInto;
	use runtime::{system, staking};
	use testing::{TestExternalities, HexDisplay, one, two};

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
			signature: "679fcf0a846b4224c84ecad7d91a26241c46d00cb53d6480a363274e8965ee34b0b80b4b2e3836d3d8f8f12c0c1aef7350af587d9aee3883561d11726068ac0a".convert(),
		};
		// tx: 2f8c6129d816cf51c374bc7f08c3e63ed156cf78aefb4a6550d97b87997977ee00000000000000000228000000d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a4500000000000000
		// sig: 679fcf0a846b4224c84ecad7d91a26241c46d00cb53d6480a363274e8965ee34b0b80b4b2e3836d3d8f8f12c0c1aef7350af587d9aee3883561d11726068ac0a

		println!("tx is {}", HexDisplay::from(&tx.transaction.to_vec()));

		with_externalities(&mut t, || {
			system::execute_transaction(&tx);
			assert_eq!(staking::balance(&one), 42);
			assert_eq!(staking::balance(&two), 69);
		});
	}
}
