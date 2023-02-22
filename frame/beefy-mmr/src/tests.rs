// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::vec;

use beefy_primitives::{
	mmr::{BeefyNextAuthoritySet, MmrLeafVersion},
	ValidatorSet,
};
use codec::{Decode, Encode};

use sp_core::H256;
use sp_io::TestExternalities;
use sp_runtime::{traits::Keccak256, DigestItem};

use frame_support::traits::OnInitialize;

use crate::mock::*;

fn init_block(block: u64) {
	System::set_block_number(block);
	Session::on_initialize(block);
	Mmr::on_initialize(block);
	Beefy::on_initialize(block);
	BeefyMmr::on_initialize(block);
}

pub fn beefy_log(log: ConsensusLog<BeefyId>) -> DigestItem {
	DigestItem::Consensus(BEEFY_ENGINE_ID, log.encode())
}

fn read_mmr_leaf(ext: &mut TestExternalities, key: Vec<u8>) -> MmrLeaf {
	type Node = pallet_mmr::primitives::DataOrHash<Keccak256, MmrLeaf>;
	ext.persist_offchain_overlay();
	let offchain_db = ext.offchain_db();
	offchain_db
		.get(&key)
		.map(|d| Node::decode(&mut &*d).unwrap())
		.map(|n| match n {
			Node::Data(d) => d,
			_ => panic!("Unexpected MMR node."),
		})
		.unwrap()
}

#[test]
fn should_contain_mmr_digest() {
	let mut ext = new_test_ext(vec![1, 2, 3, 4]);
	ext.execute_with(|| {
		init_block(1);

		assert_eq!(
			System::digest().logs,
			vec![
				beefy_log(ConsensusLog::AuthoritiesChange(
					ValidatorSet::new(vec![mock_beefy_id(1), mock_beefy_id(2)], 1).unwrap()
				)),
				beefy_log(ConsensusLog::MmrRoot(array_bytes::hex_n_into_unchecked(
					"200e73880940ac0b66735ffb560fa0a3989292463d262deac6ad61e78a3e46a4"
				)))
			]
		);

		// unique every time
		init_block(2);

		assert_eq!(
			System::digest().logs,
			vec![
				beefy_log(ConsensusLog::AuthoritiesChange(
					ValidatorSet::new(vec![mock_beefy_id(1), mock_beefy_id(2)], 1).unwrap()
				)),
				beefy_log(ConsensusLog::MmrRoot(array_bytes::hex_n_into_unchecked(
					"200e73880940ac0b66735ffb560fa0a3989292463d262deac6ad61e78a3e46a4"
				))),
				beefy_log(ConsensusLog::AuthoritiesChange(
					ValidatorSet::new(vec![mock_beefy_id(3), mock_beefy_id(4)], 2).unwrap()
				)),
				beefy_log(ConsensusLog::MmrRoot(array_bytes::hex_n_into_unchecked(
					"ba37d8d5d195ac8caec391da35472f9ecf1116ff1642409148b62e08896d3884"
				))),
			]
		);
	});
}

#[test]
fn should_contain_valid_leaf_data() {
	fn node_offchain_key(pos: usize, parent_hash: H256) -> Vec<u8> {
		(<Test as pallet_mmr::Config>::INDEXING_PREFIX, pos as u64, parent_hash).encode()
	}

	let mut ext = new_test_ext(vec![1, 2, 3, 4]);
	let parent_hash = ext.execute_with(|| {
		init_block(1);
		<frame_system::Pallet<Test>>::parent_hash()
	});

	let mmr_leaf = read_mmr_leaf(&mut ext, node_offchain_key(0, parent_hash));
	assert_eq!(
		mmr_leaf,
		MmrLeaf {
			version: MmrLeafVersion::new(1, 5),
			parent_number_and_hash: (0_u64, H256::repeat_byte(0x45)),
			beefy_next_authority_set: BeefyNextAuthoritySet {
				id: 2,
				len: 2,
				root: array_bytes::hex_n_into_unchecked(
					"9c6b2c1b0d0b25a008e6c882cc7b415f309965c72ad2b944ac0931048ca31cd5"
				)
			},
			leaf_extra: array_bytes::hex2bytes_unchecked(
				"5572d58c82bddf323f4fc7aecab8a8f0ad6ed2f06ab2bfb8ade36a77a45fcc68"
			)
		}
	);

	// build second block on top
	let parent_hash = ext.execute_with(|| {
		init_block(2);
		<frame_system::Pallet<Test>>::parent_hash()
	});

	let mmr_leaf = read_mmr_leaf(&mut ext, node_offchain_key(1, parent_hash));
	assert_eq!(
		mmr_leaf,
		MmrLeaf {
			version: MmrLeafVersion::new(1, 5),
			parent_number_and_hash: (1_u64, H256::repeat_byte(0x45)),
			beefy_next_authority_set: BeefyNextAuthoritySet {
				id: 3,
				len: 2,
				root: array_bytes::hex_n_into_unchecked(
					"9c6b2c1b0d0b25a008e6c882cc7b415f309965c72ad2b944ac0931048ca31cd5"
				)
			},
			leaf_extra: array_bytes::hex2bytes_unchecked(
				"5572d58c82bddf323f4fc7aecab8a8f0ad6ed2f06ab2bfb8ade36a77a45fcc68"
			)
		}
	);
}

#[test]
fn should_update_authorities() {
	new_test_ext(vec![1, 2, 3, 4]).execute_with(|| {
		let auth_set = BeefyMmr::authority_set_proof();
		let next_auth_set = BeefyMmr::next_authority_set_proof();

		// check current authority set
		assert_eq!(0, auth_set.id);
		assert_eq!(2, auth_set.len);
		let want = array_bytes::hex_n_into_unchecked::<H256, 32>(
			"176e73f1bf656478b728e28dd1a7733c98621b8acf830bff585949763dca7a96",
		);
		assert_eq!(want, auth_set.root);

		// next authority set should have same validators but different id
		assert_eq!(1, next_auth_set.id);
		assert_eq!(auth_set.len, next_auth_set.len);
		assert_eq!(auth_set.root, next_auth_set.root);

		let announced_set = next_auth_set;
		init_block(1);
		let auth_set = BeefyMmr::authority_set_proof();
		let next_auth_set = BeefyMmr::next_authority_set_proof();

		// check new auth are expected ones
		assert_eq!(announced_set, auth_set);
		assert_eq!(1, auth_set.id);
		// check next auth set
		assert_eq!(2, next_auth_set.id);
		let want = array_bytes::hex_n_into_unchecked::<H256, 32>(
			"9c6b2c1b0d0b25a008e6c882cc7b415f309965c72ad2b944ac0931048ca31cd5",
		);
		assert_eq!(2, next_auth_set.len);
		assert_eq!(want, next_auth_set.root);

		let announced_set = next_auth_set;
		init_block(2);
		let auth_set = BeefyMmr::authority_set_proof();
		let next_auth_set = BeefyMmr::next_authority_set_proof();

		// check new auth are expected ones
		assert_eq!(announced_set, auth_set);
		assert_eq!(2, auth_set.id);
		// check next auth set
		assert_eq!(3, next_auth_set.id);
		let want = array_bytes::hex_n_into_unchecked::<H256, 32>(
			"9c6b2c1b0d0b25a008e6c882cc7b415f309965c72ad2b944ac0931048ca31cd5",
		);
		assert_eq!(2, next_auth_set.len);
		assert_eq!(want, next_auth_set.root);
	});
}
