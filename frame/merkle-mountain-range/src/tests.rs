// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use crate::{mmr::utils, mock::*, *};

use frame_support::traits::{Get, OnInitialize};
use mmr_lib::helper;
use sp_core::{
	offchain::{testing::TestOffchainExt, OffchainDbExt, OffchainWorkerExt},
	H256,
};
use sp_mmr_primitives::{BatchProof, Compact};

pub(crate) fn new_test_ext() -> sp_io::TestExternalities {
	frame_system::GenesisConfig::default().build_storage::<Test>().unwrap().into()
}

fn register_offchain_ext(ext: &mut sp_io::TestExternalities) {
	let (offchain, _offchain_state) = TestOffchainExt::with_offchain_db(ext.offchain_db());
	ext.register_extension(OffchainDbExt::new(offchain.clone()));
	ext.register_extension(OffchainWorkerExt::new(offchain));
}

fn new_block() -> u64 {
	let number = frame_system::Pallet::<Test>::block_number() + 1;
	let hash = H256::repeat_byte(number as u8);
	LEAF_DATA.with(|r| r.borrow_mut().a = number);

	frame_system::Pallet::<Test>::reset_events();
	frame_system::Pallet::<Test>::initialize(&number, &hash, &Default::default());
	MMR::on_initialize(number)
}

fn peaks_from_leaves_count(leaves_count: NodeIndex) -> Vec<NodeIndex> {
	let size = utils::NodesUtils::new(leaves_count).size();
	helper::get_peaks(size)
}

pub(crate) fn hex(s: &str) -> H256 {
	s.parse().unwrap()
}

type BlockNumber = <Test as frame_system::Config>::BlockNumber;

fn decode_node(
	v: Vec<u8>,
) -> mmr::Node<<Test as Config>::Hashing, ((BlockNumber, H256), LeafData)> {
	use crate::primitives::DataOrHash;
	type A = DataOrHash<<Test as Config>::Hashing, (BlockNumber, H256)>;
	type B = DataOrHash<<Test as Config>::Hashing, LeafData>;
	type Node = mmr::Node<<Test as Config>::Hashing, (A, B)>;
	let tuple: Node = codec::Decode::decode(&mut &v[..]).unwrap();

	match tuple {
		mmr::Node::Data((DataOrHash::Data(a), DataOrHash::Data(b))) => mmr::Node::Data((a, b)),
		mmr::Node::Hash(hash) => mmr::Node::Hash(hash),
		_ => unreachable!(),
	}
}

fn add_blocks(blocks: usize) {
	// given
	for _ in 0..blocks {
		new_block();
	}
}

#[test]
fn should_start_empty() {
	let _ = env_logger::try_init();
	new_test_ext().execute_with(|| {
		// given
		assert_eq!(
			crate::RootHash::<Test>::get(),
			"0000000000000000000000000000000000000000000000000000000000000000"
				.parse()
				.unwrap()
		);
		assert_eq!(crate::NumberOfLeaves::<Test>::get(), 0);
		assert_eq!(crate::Nodes::<Test>::get(0), None);

		// when
		let weight = new_block();

		// then
		assert_eq!(crate::NumberOfLeaves::<Test>::get(), 1);
		assert_eq!(
			crate::Nodes::<Test>::get(0),
			Some(hex("4320435e8c3318562dba60116bdbcc0b82ffcecb9bb39aae3300cfda3ad0b8b0"))
		);
		assert_eq!(
			crate::RootHash::<Test>::get(),
			hex("4320435e8c3318562dba60116bdbcc0b82ffcecb9bb39aae3300cfda3ad0b8b0")
		);
		assert!(weight != 0);
	});
}

#[test]
fn should_append_to_mmr_when_on_initialize_is_called() {
	let _ = env_logger::try_init();
	let mut ext = new_test_ext();
	let (parent_b1, parent_b2) = ext.execute_with(|| {
		// when
		new_block();
		let parent_b1 = <frame_system::Pallet<Test>>::parent_hash();

		// then
		assert_eq!(crate::NumberOfLeaves::<Test>::get(), 1);
		assert_eq!(
			(
				crate::Nodes::<Test>::get(0),
				crate::Nodes::<Test>::get(1),
				crate::RootHash::<Test>::get(),
			),
			(
				Some(hex("4320435e8c3318562dba60116bdbcc0b82ffcecb9bb39aae3300cfda3ad0b8b0")),
				None,
				hex("0x4320435e8c3318562dba60116bdbcc0b82ffcecb9bb39aae3300cfda3ad0b8b0"),
			)
		);

		// when
		new_block();
		let parent_b2 = <frame_system::Pallet<Test>>::parent_hash();

		// then
		assert_eq!(crate::NumberOfLeaves::<Test>::get(), 2);
		let peaks = peaks_from_leaves_count(2);
		assert_eq!(peaks, vec![2]);
		assert_eq!(
			(
				crate::Nodes::<Test>::get(0),
				crate::Nodes::<Test>::get(1),
				crate::Nodes::<Test>::get(2),
				crate::Nodes::<Test>::get(3),
				crate::RootHash::<Test>::get(),
			),
			(
				None,
				None,
				Some(hex("672c04a9cd05a644789d769daa552d35d8de7c33129f8a7cbf49e595234c4854")),
				None,
				hex("672c04a9cd05a644789d769daa552d35d8de7c33129f8a7cbf49e595234c4854"),
			)
		);

		(parent_b1, parent_b2)
	});
	// make sure the leaves end up in the offchain DB
	ext.persist_offchain_overlay();

	let offchain_db = ext.offchain_db();
	assert_eq!(
		offchain_db.get(&MMR::offchain_key(parent_b1, 0)).map(decode_node),
		Some(mmr::Node::Data(((0, H256::repeat_byte(1)), LeafData::new(1),)))
	);
	assert_eq!(
		offchain_db.get(&MMR::offchain_key(parent_b2, 1)).map(decode_node),
		Some(mmr::Node::Data(((1, H256::repeat_byte(2)), LeafData::new(2),)))
	);
	assert_eq!(
		offchain_db.get(&MMR::offchain_key(parent_b2, 2)).map(decode_node),
		Some(mmr::Node::Hash(hex(
			"672c04a9cd05a644789d769daa552d35d8de7c33129f8a7cbf49e595234c4854"
		)))
	);
	assert_eq!(offchain_db.get(&MMR::offchain_key(parent_b2, 3)), None);

	assert_eq!(offchain_db.get(&MMR::canon_offchain_key(0)), None);
	assert_eq!(offchain_db.get(&MMR::canon_offchain_key(1)), None);
	assert_eq!(offchain_db.get(&MMR::canon_offchain_key(2)), None);
	assert_eq!(offchain_db.get(&MMR::canon_offchain_key(3)), None);
}

#[test]
fn should_construct_larger_mmr_correctly() {
	let _ = env_logger::try_init();
	new_test_ext().execute_with(|| {
		// when
		add_blocks(7);

		// then
		assert_eq!(crate::NumberOfLeaves::<Test>::get(), 7);
		let peaks = peaks_from_leaves_count(7);
		assert_eq!(peaks, vec![6, 9, 10]);
		for i in (0..=10).filter(|p| !peaks.contains(p)) {
			assert!(crate::Nodes::<Test>::get(i).is_none());
		}
		assert_eq!(
			(
				crate::Nodes::<Test>::get(6),
				crate::Nodes::<Test>::get(9),
				crate::Nodes::<Test>::get(10),
				crate::RootHash::<Test>::get(),
			),
			(
				Some(hex("ae88a0825da50e953e7a359c55fe13c8015e48d03d301b8bdfc9193874da9252")),
				Some(hex("7e4316ae2ebf7c3b6821cb3a46ca8b7a4f9351a9b40fcf014bb0a4fd8e8f29da")),
				Some(hex("611c2174c6164952a66d985cfe1ec1a623794393e3acff96b136d198f37a648c")),
				hex("e45e25259f7930626431347fa4dd9aae7ac83b4966126d425ca70ab343709d2c"),
			)
		);
	});
}

#[test]
fn should_generate_proofs_correctly() {
	let _ = env_logger::try_init();
	let mut ext = new_test_ext();
	// given
	ext.execute_with(|| add_blocks(7));
	ext.persist_offchain_overlay();

	// Try to generate proofs now. This requires the offchain extensions to be present
	// to retrieve full leaf data.
	register_offchain_ext(&mut ext);
	ext.execute_with(|| {
		// when generate proofs for all leaves
		let proofs = (0_u64..crate::NumberOfLeaves::<Test>::get())
			.into_iter()
			.map(|leaf_index| {
				crate::Pallet::<Test>::generate_batch_proof(vec![leaf_index]).unwrap()
			})
			.collect::<Vec<_>>();

		// then
		assert_eq!(
			proofs[0],
			(
				vec![Compact::new(((0, H256::repeat_byte(1)).into(), LeafData::new(1).into(),))],
				BatchProof {
					leaf_indices: vec![0],
					leaf_count: 7,
					items: vec![
						hex("ad4cbc033833612ccd4626d5f023b9dfc50a35e838514dd1f3c86f8506728705"),
						hex("cb24f4614ad5b2a5430344c99545b421d9af83c46fd632d70a332200884b4d46"),
						hex("dca421199bdcc55bb773c6b6967e8d16675de69062b52285ca63685241fdf626"),
					],
				}
			)
		);
		assert_eq!(
			proofs[4],
			(
				vec![Compact::new(((4, H256::repeat_byte(5)).into(), LeafData::new(5).into(),))],
				BatchProof {
					leaf_indices: vec![4],
					leaf_count: 7,
					items: vec![
						hex("ae88a0825da50e953e7a359c55fe13c8015e48d03d301b8bdfc9193874da9252"),
						hex("8ed25570209d8f753d02df07c1884ddb36a3d9d4770e4608b188322151c657fe"),
						hex("611c2174c6164952a66d985cfe1ec1a623794393e3acff96b136d198f37a648c"),
					],
				}
			)
		);
		assert_eq!(
			proofs[6],
			(
				vec![Compact::new(((6, H256::repeat_byte(7)).into(), LeafData::new(7).into(),))],
				BatchProof {
					leaf_indices: vec![6],
					leaf_count: 7,
					items: vec![
						hex("ae88a0825da50e953e7a359c55fe13c8015e48d03d301b8bdfc9193874da9252"),
						hex("7e4316ae2ebf7c3b6821cb3a46ca8b7a4f9351a9b40fcf014bb0a4fd8e8f29da"),
					],
				}
			)
		);
	});
}

#[test]
fn should_generate_batch_proof_correctly() {
	let _ = env_logger::try_init();
	let mut ext = new_test_ext();
	// given
	ext.execute_with(|| add_blocks(7));
	ext.persist_offchain_overlay();

	// Try to generate proofs now. This requires the offchain extensions to be present
	// to retrieve full leaf data.
	register_offchain_ext(&mut ext);
	ext.execute_with(|| {
		// when generate proofs for all leaves
		let (.., proof) = crate::Pallet::<Test>::generate_batch_proof(vec![0, 4, 5]).unwrap();

		// then
		assert_eq!(
			proof,
			BatchProof {
				leaf_indices: vec![0, 4, 5],
				leaf_count: 7,
				items: vec![
					hex("ad4cbc033833612ccd4626d5f023b9dfc50a35e838514dd1f3c86f8506728705"),
					hex("cb24f4614ad5b2a5430344c99545b421d9af83c46fd632d70a332200884b4d46"),
					hex("611c2174c6164952a66d985cfe1ec1a623794393e3acff96b136d198f37a648c"),
				],
			}
		);
	});
}

#[test]
fn should_verify() {
	let _ = env_logger::try_init();

	// Start off with chain initialisation and storing indexing data off-chain
	// (MMR Leafs)
	let mut ext = new_test_ext();
	ext.execute_with(|| add_blocks(7));
	ext.persist_offchain_overlay();

	// Try to generate proof now. This requires the offchain extensions to be present
	// to retrieve full leaf data.
	register_offchain_ext(&mut ext);
	let (leaves, proof5) = ext.execute_with(|| {
		// when
		crate::Pallet::<Test>::generate_batch_proof(vec![5]).unwrap()
	});

	ext.execute_with(|| {
		add_blocks(7);
		// then
		assert_eq!(crate::Pallet::<Test>::verify_leaves(leaves, proof5), Ok(()));
	});
}

#[test]
fn should_verify_batch_proof() {
	let _ = env_logger::try_init();

	// Start off with chain initialisation and storing indexing data off-chain
	// (MMR Leafs)
	let mut ext = new_test_ext();
	ext.execute_with(|| add_blocks(7));
	ext.persist_offchain_overlay();

	// Try to generate proof now. This requires the offchain extensions to be present
	// to retrieve full leaf data.
	register_offchain_ext(&mut ext);
	let (leaves, proof) = ext.execute_with(|| {
		// when
		crate::Pallet::<Test>::generate_batch_proof(vec![0, 4, 5]).unwrap()
	});

	ext.execute_with(|| {
		add_blocks(7);
		// then
		assert_eq!(crate::Pallet::<Test>::verify_leaves(leaves, proof), Ok(()));
	});
}

#[test]
fn verification_should_be_stateless() {
	let _ = env_logger::try_init();

	// Start off with chain initialisation and storing indexing data off-chain
	// (MMR Leafs)
	let mut ext = new_test_ext();
	ext.execute_with(|| add_blocks(7));
	ext.persist_offchain_overlay();

	// Try to generate proof now. This requires the offchain extensions to be present
	// to retrieve full leaf data.
	register_offchain_ext(&mut ext);
	let (leaves, proof5) = ext.execute_with(|| {
		// when
		crate::Pallet::<Test>::generate_batch_proof(vec![5]).unwrap()
	});
	let root = ext.execute_with(|| crate::Pallet::<Test>::mmr_root_hash());

	// Verify proof without relying on any on-chain data.
	let leaf = crate::primitives::DataOrHash::Data(leaves[0].clone());
	assert_eq!(
		crate::verify_leaves_proof::<<Test as Config>::Hashing, _>(root, vec![leaf], proof5),
		Ok(())
	);
}

#[test]
fn should_verify_batch_proof_statelessly() {
	let _ = env_logger::try_init();

	// Start off with chain initialisation and storing indexing data off-chain
	// (MMR Leafs)
	let mut ext = new_test_ext();
	ext.execute_with(|| add_blocks(7));
	ext.persist_offchain_overlay();

	// Try to generate proof now. This requires the offchain extensions to be present
	// to retrieve full leaf data.
	register_offchain_ext(&mut ext);
	let (leaves, proof) = ext.execute_with(|| {
		// when
		crate::Pallet::<Test>::generate_batch_proof(vec![0, 4, 5]).unwrap()
	});
	let root = ext.execute_with(|| crate::Pallet::<Test>::mmr_root_hash());

	// Verify proof without relying on any on-chain data.
	assert_eq!(
		crate::verify_leaves_proof::<<Test as Config>::Hashing, _>(
			root,
			leaves
				.into_iter()
				.map(|leaf| crate::primitives::DataOrHash::Data(leaf))
				.collect(),
			proof
		),
		Ok(())
	);
}

#[test]
fn should_verify_on_the_next_block_since_there_is_no_pruning_yet() {
	let _ = env_logger::try_init();
	let mut ext = new_test_ext();
	// given
	ext.execute_with(|| add_blocks(7));

	ext.persist_offchain_overlay();
	register_offchain_ext(&mut ext);

	ext.execute_with(|| {
		// when
		let (leaves, proof5) = crate::Pallet::<Test>::generate_batch_proof(vec![5]).unwrap();
		new_block();

		// then
		assert_eq!(crate::Pallet::<Test>::verify_leaves(leaves, proof5), Ok(()));
	});
}

#[test]
fn should_canonicalize_offchain() {
	use frame_support::traits::Hooks;

	let _ = env_logger::try_init();
	let mut ext = new_test_ext();
	register_offchain_ext(&mut ext);

	// add 3 blocks and verify leaves and nodes for them have been added to
	// offchain MMR using fork-proof keys.
	ext.execute_with(|| add_blocks(3));
	ext.persist_offchain_overlay();
	let offchain_db = ext.offchain_db();
	let (parent_b1, parent_b2, parent_b3, block_hash_size) = ext.execute_with(|| {
		// check nodes added by 1st block:
		// not canon,
		assert_eq!(offchain_db.get(&MMR::canon_offchain_key(0)), None);
		let parent_b1 = <frame_system::Pallet<Test>>::block_hash(0);
		// but available in fork-proof storage.
		assert_eq!(
			offchain_db.get(&MMR::offchain_key(parent_b1, 0)).map(decode_node),
			Some(mmr::Node::Data(((0, H256::repeat_byte(1)), LeafData::new(1),)))
		);

		// check nodes added by 2nd block:
		// not canon,
		assert_eq!(offchain_db.get(&MMR::canon_offchain_key(1)), None);
		assert_eq!(offchain_db.get(&MMR::canon_offchain_key(2)), None);
		let parent_b2 = <frame_system::Pallet<Test>>::block_hash(1);
		// but available in fork-proof storage.
		assert_eq!(
			offchain_db.get(&MMR::offchain_key(parent_b2, 1)).map(decode_node),
			Some(mmr::Node::Data(((1, H256::repeat_byte(2)), LeafData::new(2),)))
		);
		assert_eq!(
			offchain_db.get(&MMR::offchain_key(parent_b2, 2)).map(decode_node),
			Some(mmr::Node::Hash(hex(
				"672c04a9cd05a644789d769daa552d35d8de7c33129f8a7cbf49e595234c4854"
			)))
		);

		// check nodes added by 3rd block:
		// not canon,
		assert_eq!(offchain_db.get(&MMR::canon_offchain_key(3)), None);
		let parent_b3 = <frame_system::Pallet<Test>>::block_hash(2);
		// but available in fork-proof storage.
		assert_eq!(
			offchain_db.get(&MMR::offchain_key(parent_b3, 3)).map(decode_node),
			Some(mmr::Node::Data(((2, H256::repeat_byte(3)), LeafData::new(3),)))
		);

		let block_hash_size: u64 = <Test as frame_system::Config>::BlockHashCount::get();
		(parent_b1, parent_b2, parent_b3, block_hash_size)
	});

	// add another `frame_system::BlockHashCount` blocks and verify all nodes and leaves
	// added by our original 3 blocks have now been canonicalized in offchain db.
	ext.execute_with(|| {
		for blocknum in 3u32..(3 + block_hash_size).try_into().unwrap() {
			new_block();
			<Pallet<Test> as Hooks<BlockNumber>>::offchain_worker(blocknum.into());
		}
	});
	ext.persist_offchain_overlay();
	ext.execute_with(|| {
		// check nodes added by 1st block:
		// no longer available in fork-proof storage,
		assert_eq!(offchain_db.get(&MMR::offchain_key(parent_b1, 0)), None);
		// but available using canon key.
		assert_eq!(
			offchain_db.get(&MMR::canon_offchain_key(0)).map(decode_node),
			Some(mmr::Node::Data(((0, H256::repeat_byte(1)), LeafData::new(1),)))
		);

		// check nodes added by 2nd block:
		// no longer available in fork-proof storage,
		assert_eq!(offchain_db.get(&MMR::offchain_key(parent_b2, 1)), None);
		assert_eq!(offchain_db.get(&MMR::offchain_key(parent_b2, 2)), None);
		// but available using canon key.
		assert_eq!(
			offchain_db.get(&MMR::canon_offchain_key(1)).map(decode_node),
			Some(mmr::Node::Data(((1, H256::repeat_byte(2)), LeafData::new(2),)))
		);
		assert_eq!(
			offchain_db.get(&MMR::canon_offchain_key(2)).map(decode_node),
			Some(mmr::Node::Hash(hex(
				"672c04a9cd05a644789d769daa552d35d8de7c33129f8a7cbf49e595234c4854"
			)))
		);

		// check nodes added by 3rd block:
		// no longer available in fork-proof storage.
		assert_eq!(offchain_db.get(&MMR::offchain_key(parent_b3, 3)), None);
		// but available using canon key.
		assert_eq!(
			offchain_db.get(&MMR::canon_offchain_key(3)).map(decode_node),
			Some(mmr::Node::Data(((2, H256::repeat_byte(3)), LeafData::new(3),)))
		);
	});
}
