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

use codec::Slicable;

use ::AccountId;
use block::{Block, Header, Digest, Log};
use runtime_function::Function;
use transaction::{UncheckedTransaction, Transaction};

#[test]
fn serialise_transaction_works() {
	let one: AccountId = [1u8; 32];
	let two: AccountId = [2u8; 32];
	let tx = Transaction {
		signed: one.clone(),
		nonce: 69,
		function: Function::StakingTransfer(two, 69),
	};

	let serialised = tx.to_vec();
	assert_eq!(serialised, vec![
		1u8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
		69, 0, 0, 0, 0, 0, 0, 0,
		34,
			2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
			69, 0, 0, 0, 0, 0, 0, 0
	]);
}

#[test]
fn deserialise_transaction_works() {
	let one: AccountId = [1u8; 32];
	let two: AccountId = [2u8; 32];
	let tx = Transaction {
		signed: one.clone(),
		nonce: 69,
		function: Function::StakingTransfer(two, 69),
	};

	let data = [
		1u8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
		69, 0, 0, 0, 0, 0, 0, 0,
		34,
			2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
			69, 0, 0, 0, 0, 0, 0, 0
	];
	let deserialised = Transaction::from_slice(&mut &data[..]).unwrap();
	assert_eq!(deserialised, tx);
}

#[test]
fn serialise_header_works() {
	let h = Header {
		parent_hash: [4u8; 32].into(),
		number: 42,
		state_root: [5u8; 32].into(),
		transaction_root: [6u8; 32].into(),
		digest: Digest { logs: vec![ Log(b"one log".to_vec()), Log(b"another log".to_vec()) ], },
	};
	let serialised = h.to_vec();
	assert_eq!(serialised, vec![
		4u8, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
		42, 0, 0, 0, 0, 0, 0, 0,
		5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
		6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
		2, 0, 0, 0,
			7, 0, 0, 0,
				111, 110, 101, 32, 108, 111, 103,
			11, 0, 0, 0,
				97, 110, 111, 116, 104, 101, 114, 32, 108, 111, 103
	]);
}

#[test]
fn deserialise_header_works() {
	let h = Header {
		parent_hash: [4u8; 32].into(),
		number: 42,
		state_root: [5u8; 32].into(),
		transaction_root: [6u8; 32].into(),
		digest: Digest { logs: vec![ Log(b"one log".to_vec()), Log(b"another log".to_vec()) ], },
	};
	let data = [
		4u8, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
		42, 0, 0, 0, 0, 0, 0, 0,
		5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
		6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
		2, 0, 0, 0,
			7, 0, 0, 0,
				111, 110, 101, 32, 108, 111, 103,
			11, 0, 0, 0,
				97, 110, 111, 116, 104, 101, 114, 32, 108, 111, 103
	];
	let deserialised = Header::from_slice(&mut &data[..]).unwrap();
	assert_eq!(deserialised, h);
}

#[test]
fn serialise_block_works() {
	let one: AccountId = [1u8; 32];
	let two: AccountId = [2u8; 32];
	let tx1 = UncheckedTransaction {
		transaction: Transaction {
			signed: one.clone(),
			nonce: 69,
			function: Function::StakingTransfer(two, 69),
		},
		signature: [1u8; 64].into(),
	};
	let tx2 = UncheckedTransaction {
		transaction: Transaction {
			signed: two.clone(),
			nonce: 42,
			function: Function::StakingStake,
		},
		signature: [2u8; 64].into(),
	};
	let h = Header {
		parent_hash: [4u8; 32].into(),
		number: 42,
		state_root: [5u8; 32].into(),
		transaction_root: [6u8; 32].into(),
		digest: Digest { logs: vec![ Log(b"one log".to_vec()), Log(b"another log".to_vec()) ], },
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
		2, 0, 0, 0,
			7, 0, 0, 0,
				111, 110, 101, 32, 108, 111, 103,
			11, 0, 0, 0,
				97, 110, 111, 116, 104, 101, 114, 32, 108, 111, 103,
		// transactions
		2, 0, 0, 0,
			// tx1
			1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
			69, 0, 0, 0, 0, 0, 0, 0,
			34,
				2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
				69, 0, 0, 0, 0, 0, 0, 0,
			1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
			// tx2
			2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
			42, 0, 0, 0, 0, 0, 0, 0,
			32,
			2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
	]);
}

#[test]
fn deserialise_block_works() {
	let one: AccountId = [1u8; 32];
	let two: AccountId = [2u8; 32];
	let tx1 = UncheckedTransaction {
		transaction: Transaction {
			signed: one.clone(),
			nonce: 69,
			function: Function::StakingTransfer(two, 69),
		},
		signature: [1u8; 64].into(),
	};
	let tx2 = UncheckedTransaction {
		transaction: Transaction {
			signed: two.clone(),
			nonce: 42,
			function: Function::StakingStake,
		},
		signature: [2u8; 64].into(),
	};
	let h = Header {
		parent_hash: [4u8; 32].into(),
		number: 42,
		state_root: [5u8; 32].into(),
		transaction_root: [6u8; 32].into(),
		digest: Digest { logs: vec![ Log(b"one log".to_vec()), Log(b"another log".to_vec()) ], },
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
		2, 0, 0, 0,
			7, 0, 0, 0,
				111, 110, 101, 32, 108, 111, 103,
			11, 0, 0, 0,
				97, 110, 111, 116, 104, 101, 114, 32, 108, 111, 103,
		// transactions
		2, 0, 0, 0,
			// tx1
			1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
			69, 0, 0, 0, 0, 0, 0, 0,
			34,
				2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
				69, 0, 0, 0, 0, 0, 0, 0,
			1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
			// tx2
			2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
			42, 0, 0, 0, 0, 0, 0, 0,
			32,
			2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
	];
	let deserialised = Block::from_slice(&mut &data[..]).unwrap();
	assert_eq!(deserialised, b);
}
