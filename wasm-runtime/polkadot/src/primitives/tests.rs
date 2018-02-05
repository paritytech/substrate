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

//! Tests.

use super::*;
use runtime_std::prelude::*;
use codec::{Joiner, Slicable};
use primitives::Function;

#[test]
fn serialise_transaction_works() {
	let one: AccountID = [1u8; 32];
	let two: AccountID = [2u8; 32];
	let tx = Transaction {
		signed: one.clone(),
		nonce: 69,
		function: Function::StakingTransfer,
		input_data: Vec::new().join(&two).join(&69u64),
	};
	let serialised = tx.to_vec();
	assert_eq!(serialised, vec![
		1u8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
		69, 0, 0, 0, 0, 0, 0, 0,
		34,
		40, 0, 0, 0,
			2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
			69, 0, 0, 0, 0, 0, 0, 0
	]);
}

#[test]
fn deserialise_transaction_works() {
	let one: AccountID = [1u8; 32];
	let two: AccountID = [2u8; 32];
	let tx = Transaction {
		signed: one.clone(),
		nonce: 69,
		function: Function::StakingTransfer,
		input_data: Vec::new().join(&two).join(&69u64),
	};
	let data = [
		1u8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
		69, 0, 0, 0, 0, 0, 0, 0,
		34,
		40, 0, 0, 0,
			2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
			69, 0, 0, 0, 0, 0, 0, 0
	];
	let deserialised = Transaction::from_slice(&data).unwrap();
	assert_eq!(deserialised, tx);
}

#[test]
fn serialise_header_works() {
	let h = Header {
		parent_hash: [4u8; 32],
		number: 42,
		state_root: [5u8; 32],
		transaction_root: [6u8; 32],
		digest: Digest { logs: vec![ b"one log".to_vec(), b"another log".to_vec() ], },
	};
	let serialised = h.to_vec();
	assert_eq!(serialised, vec![
		4u8, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
		42, 0, 0, 0, 0, 0, 0, 0,
		5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
		6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
		26, 0, 0, 0,
			7, 0, 0, 0,
				111, 110, 101, 32, 108, 111, 103,
			11, 0, 0, 0,
				97, 110, 111, 116, 104, 101, 114, 32, 108, 111, 103
	]);
}

#[test]
fn deserialise_header_works() {
	let h = Header {
		parent_hash: [4u8; 32],
		number: 42,
		state_root: [5u8; 32],
		transaction_root: [6u8; 32],
		digest: Digest { logs: vec![ b"one log".to_vec(), b"another log".to_vec() ], },
	};
	let data = [
		4u8, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
		42, 0, 0, 0, 0, 0, 0, 0,
		5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
		6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
		26, 0, 0, 0,
			7, 0, 0, 0,
				111, 110, 101, 32, 108, 111, 103,
			11, 0, 0, 0,
				97, 110, 111, 116, 104, 101, 114, 32, 108, 111, 103
	];
	let deserialised = Header::from_slice(&data).unwrap();
	assert_eq!(deserialised, h);
}

#[test]
fn serialise_block_works() {
	let one: AccountID = [1u8; 32];
	let two: AccountID = [2u8; 32];
	let tx1 = UncheckedTransaction {
		transaction: Transaction {
			signed: one.clone(),
			nonce: 69,
			function: Function::StakingTransfer,
			input_data: Vec::new().join(&two).join(&69u64),
		},
		signature: [1u8; 64],
	};
	let tx2 = UncheckedTransaction {
		transaction: Transaction {
			signed: two.clone(),
			nonce: 42,
			function: Function::StakingStake,
			input_data: Vec::new(),
		},
		signature: [2u8; 64],
	};
	let h = Header {
		parent_hash: [4u8; 32],
		number: 42,
		state_root: [5u8; 32],
		transaction_root: [6u8; 32],
		digest: Digest { logs: vec![ b"one log".to_vec(), b"another log".to_vec() ], },
	};
	let b = Block {
		header: h,
		transactions: vec![tx1, tx2],
	};
	let serialised = b.to_vec();
	assert_eq!(serialised, vec![
		// header
		4u8, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
		42, 0, 0, 0, 0, 0, 0, 0,
		5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
		6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
		26, 0, 0, 0,
			7, 0, 0, 0,
				111, 110, 101, 32, 108, 111, 103,
			11, 0, 0, 0,
				97, 110, 111, 116, 104, 101, 114, 32, 108, 111, 103,
		// transactions
		2, 1, 0, 0,
			// tx1
			1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
			1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
			69, 0, 0, 0, 0, 0, 0, 0,
			34,
			40, 0, 0, 0,
				2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
				69, 0, 0, 0, 0, 0, 0, 0,
			// tx2
			2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
			2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
			42, 0, 0, 0, 0, 0, 0, 0,
			32,
			0, 0, 0, 0
	]);
}

#[test]
fn deserialise_block_works() {
	let one: AccountID = [1u8; 32];
	let two: AccountID = [2u8; 32];
	let tx1 = UncheckedTransaction {
		transaction: Transaction {
			signed: one.clone(),
			nonce: 69,
			function: Function::StakingTransfer,
			input_data: Vec::new().join(&two).join(&69u64),
		},
		signature: [1u8; 64],
	};
	let tx2 = UncheckedTransaction {
		transaction: Transaction {
			signed: two.clone(),
			nonce: 42,
			function: Function::StakingStake,
			input_data: Vec::new(),
		},
		signature: [2u8; 64],
	};
	let h = Header {
		parent_hash: [4u8; 32],
		number: 42,
		state_root: [5u8; 32],
		transaction_root: [6u8; 32],
		digest: Digest { logs: vec![ b"one log".to_vec(), b"another log".to_vec() ], },
	};
	let b = Block {
		header: h,
		transactions: vec![tx1, tx2],
	};
	let data = [
		// header
		4u8, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
		42, 0, 0, 0, 0, 0, 0, 0,
		5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
		6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
		26, 0, 0, 0,
			7, 0, 0, 0,
				111, 110, 101, 32, 108, 111, 103,
			11, 0, 0, 0,
				97, 110, 111, 116, 104, 101, 114, 32, 108, 111, 103,
		// transactions
		2, 1, 0, 0,
			// tx1
			1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
			1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
			69, 0, 0, 0, 0, 0, 0, 0,
			34,
			40, 0, 0, 0,
				2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
				69, 0, 0, 0, 0, 0, 0, 0,
			// tx2
			2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
			2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
			42, 0, 0, 0, 0, 0, 0, 0,
			32,
			0, 0, 0, 0
	];
	let deserialised = Block::from_slice(&data).unwrap();
	assert_eq!(deserialised, b);
}
