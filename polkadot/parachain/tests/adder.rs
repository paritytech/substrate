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

//! Basic parachain that adds a number as part of its state.

#[macro_use]
extern crate substrate_codec_derive;
extern crate substrate_codec as codec;
extern crate polkadot_parachain as parachain;
extern crate tiny_keccak;

use parachain::ValidationParams;
use codec::{Decode, Encode};

/// Head data for this parachain.
#[derive(Default, Clone, Encode, Decode)]
struct HeadData {
	/// Block number
	number: u64,
	/// parent block keccak256
	parent_hash: [u8; 32],
	/// hash of post-execution state.
	post_state: [u8; 32],
}

/// Block data for this parachain.
#[derive(Default, Clone, Encode, Decode)]
struct BlockData {
	/// State to begin from.
	state: u64,
	/// Amount to add (overflowing)
	add: u64,
}

const TEST_CODE: &[u8] = include_bytes!("res/adder.wasm");

fn hash_state(state: u64) -> [u8; 32] {
	::tiny_keccak::keccak256(state.encode().as_slice())
}

fn hash_head(head: &HeadData) -> [u8; 32] {
	::tiny_keccak::keccak256(head.encode().as_slice())
}

#[test]
fn execute_good_on_parent() {
	let parent_head = HeadData {
		number: 0,
		parent_hash: [0; 32],
		post_state: hash_state(0),
	};

	let block_data = BlockData {
		state: 0,
		add: 512,
	};

	let ret = parachain::wasm::validate_candidate(TEST_CODE, ValidationParams {
		parent_head: parent_head.encode(),
		block_data: block_data.encode(),
	}).unwrap();

	let new_head = HeadData::decode(&mut &ret.head_data[..]).unwrap();

	assert_eq!(new_head.number, 1);
	assert_eq!(new_head.parent_hash, hash_head(&parent_head));
	assert_eq!(new_head.post_state, hash_state(512));
}

#[test]
fn execute_good_chain_on_parent() {
	let mut number = 0;
	let mut parent_hash = [0; 32];
	let mut last_state = 0;

	for add in 0..10 {
		let parent_head = HeadData {
			number,
			parent_hash,
			post_state: hash_state(last_state),
		};

		let block_data = BlockData {
			state: last_state,
			add,
		};

		let ret = parachain::wasm::validate_candidate(TEST_CODE, ValidationParams {
			parent_head: parent_head.encode(),
			block_data: block_data.encode(),
		}).unwrap();

		let new_head = HeadData::decode(&mut &ret.head_data[..]).unwrap();

		assert_eq!(new_head.number, number + 1);
		assert_eq!(new_head.parent_hash, hash_head(&parent_head));
		assert_eq!(new_head.post_state, hash_state(last_state + add));

		number += 1;
		parent_hash = hash_head(&new_head);
		last_state += add;
	}
}

#[test]
fn execute_bad_on_parent() {
	let parent_head = HeadData {
		number: 0,
		parent_hash: [0; 32],
		post_state: hash_state(0),
	};

	let block_data = BlockData {
		state: 256, // start state is wrong.
		add: 256,
	};

	let _ret = parachain::wasm::validate_candidate(TEST_CODE, ValidationParams {
		parent_head: parent_head.encode(),
		block_data: block_data.encode(),
	}).unwrap_err();
}
