// Copyright (C) 2020 - 2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use std::vec;

use beefy_primitives::{
	mmr::{BeefyNextAuthoritySet, MmrLeafVersion},
	ValidatorSet,
};
use codec::{Decode, Encode};
use hex_literal::hex;

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

pub fn beefy_log(log: ConsensusLog<BeefyId>) -> DigestItem<H256> {
	DigestItem::Consensus(BEEFY_ENGINE_ID, log.encode())
}

fn offchain_key(pos: usize) -> Vec<u8> {
	(<Test as pallet_mmr::Config>::INDEXING_PREFIX, pos as u64).encode()
}

fn read_mmr_leaf(ext: &mut TestExternalities, index: usize) -> MmrLeaf {
	type Node = pallet_mmr_primitives::DataOrHash<Keccak256, MmrLeaf>;
	ext.persist_offchain_overlay();
	let offchain_db = ext.offchain_db();
	offchain_db
		.get(&offchain_key(index))
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
			vec![beefy_log(ConsensusLog::MmrRoot(
				hex!("f3e3afbfa69e89cd1e99f8d3570155962f3346d1d8758dc079be49ef70387758").into()
			))]
		);

		// unique every time
		init_block(2);

		assert_eq!(
			System::digest().logs,
			vec![
				beefy_log(ConsensusLog::MmrRoot(
					hex!("f3e3afbfa69e89cd1e99f8d3570155962f3346d1d8758dc079be49ef70387758").into()
				)),
				beefy_log(ConsensusLog::AuthoritiesChange(ValidatorSet {
					validators: vec![mock_beefy_id(3), mock_beefy_id(4),],
					id: 1,
				})),
				beefy_log(ConsensusLog::MmrRoot(
					hex!("7d4ae4524bae75d52b63f08eab173b0c263eb95ae2c55c3a1d871241bd0cc559").into()
				)),
			]
		);
	});
}

#[test]
fn should_contain_valid_leaf_data() {
	let mut ext = new_test_ext(vec![1, 2, 3, 4]);
	ext.execute_with(|| {
		init_block(1);
	});

	let mmr_leaf = read_mmr_leaf(&mut ext, 0);
	assert_eq!(
		mmr_leaf,
		MmrLeaf {
			version: MmrLeafVersion::new(1, 5),
			parent_number_and_hash: (0_u64, H256::repeat_byte(0x45)),
			beefy_next_authority_set: BeefyNextAuthoritySet {
				id: 1,
				len: 2,
				root: hex!("01b1a742589773fc054c8f5021a456316ffcec0370b25678b0696e116d1ef9ae").into(),
			},
			parachain_heads: hex!("ed893c8f8cc87195a5d4d2805b011506322036bcace79642aa3e94ab431e442e").into(),
		}
	);

	// build second block on top
	ext.execute_with(|| {
		init_block(2);
	});

	let mmr_leaf = read_mmr_leaf(&mut ext, 1);
	assert_eq!(
		mmr_leaf,
		MmrLeaf {
			version: MmrLeafVersion::new(1, 5),
			parent_number_and_hash: (1_u64, H256::repeat_byte(0x45)),
			beefy_next_authority_set: BeefyNextAuthoritySet {
				id: 2,
				len: 2,
				root: hex!("9c6b2c1b0d0b25a008e6c882cc7b415f309965c72ad2b944ac0931048ca31cd5").into(),
			},
			parachain_heads: hex!("ed893c8f8cc87195a5d4d2805b011506322036bcace79642aa3e94ab431e442e").into(),
		}
	);
}
