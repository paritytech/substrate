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

use crate::{
	mmr::{storage::PruningMap, utils},
	mock::*,
	*,
};

use frame_support::traits::{Get, Hooks, OnInitialize};
use mmr_lib::helper;
use sp_core::{
	offchain::{testing::TestOffchainExt, OffchainDbExt, OffchainWorkerExt},
	H256,
};
use sp_io::TestExternalities;
use sp_mmr_primitives::{BatchProof, Compact};

pub(crate) fn new_test_ext() -> TestExternalities {
	let mut ext: TestExternalities =
		frame_system::GenesisConfig::default().build_storage::<Test>().unwrap().into();
	let (offchain, _offchain_state) = TestOffchainExt::with_offchain_db(ext.offchain_db());
	ext.register_extension(OffchainDbExt::new(offchain.clone()));
	ext.register_extension(OffchainWorkerExt::new(offchain));
	ext
}

// Use `push_block_with_offchain()` if you need to also generate proofs for this block.
fn new_block() -> (BlockNumber, H256, Weight) {
	let number = frame_system::Pallet::<Test>::block_number() + 1;
	let parent_hash = H256::repeat_byte((number - 1) as u8);
	let hash = H256::repeat_byte(number as u8);
	LeafDataTestValue::mutate(|r| r.a = number);

	frame_system::Pallet::<Test>::reset_events();
	frame_system::Pallet::<Test>::initialize(&number, &parent_hash, &Default::default());
	(number, hash, <pallet::Pallet<mock::Test> as OnInitialize<BlockNumber>>::on_initialize(number))
}

fn push_block_with_offchain() -> (BlockNumber, H256, Weight) {
	let (number, hash, weight) = new_block();
	assert_eq!(number, <frame_system::Pallet<Test>>::block_number());
	// We don't have frame-executive pallet here, populate `BlockHash` ourselves.
	frame_system::BlockHash::<Test>::insert(number, hash);
	// Without frame-executive, call offchain_worker() ourselves.
	<Pallet<Test> as Hooks<BlockNumber>>::offchain_worker(number);
	(number, hash, weight)
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

// Use `add_blocks_with_offchain()` if you need to also generate proofs for these blocks.
fn add_blocks(blocks: usize) {
	// given
	for _ in 0..blocks {
		new_block();
	}
}

// Add blocks and run offchain worker so offchain db MMR is also built.
// Use this function if you plan to generate proofs (offchain data required).
fn add_blocks_with_offchain(blocks: usize) {
	// given
	for _ in 0..blocks {
		push_block_with_offchain();
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
		assert_eq!(crate::Peaks::<Test>::get(0), None);

		// when
		let (_, _, weight) = new_block();

		// then
		assert_eq!(crate::NumberOfLeaves::<Test>::get(), 1);
		assert_eq!(
			crate::Peaks::<Test>::get(0),
			Some(hex("c51a80dfad5ad167c7001f581065bea8db70b04aeca50eedf908cbb3ff859d0b"))
		);
		assert_eq!(
			crate::RootHash::<Test>::get(),
			hex("c51a80dfad5ad167c7001f581065bea8db70b04aeca50eedf908cbb3ff859d0b")
		);
		assert!(weight != Weight::zero());
	});
}

#[test]
fn should_append_to_mmr_after_on_initialize() {
	let _ = env_logger::try_init();
	let mut ext = new_test_ext();
	let (hash1, hash2) = ext.execute_with(|| {
		// when
		let (_, hash1, _) = push_block_with_offchain();

		// then
		assert_eq!(crate::NumberOfLeaves::<Test>::get(), 1);
		assert_eq!(
			(
				crate::Peaks::<Test>::get(0),
				crate::Peaks::<Test>::get(1),
				crate::RootHash::<Test>::get(),
			),
			(
				Some(hex("c51a80dfad5ad167c7001f581065bea8db70b04aeca50eedf908cbb3ff859d0b")),
				None,
				hex("0xc51a80dfad5ad167c7001f581065bea8db70b04aeca50eedf908cbb3ff859d0b"),
			)
		);

		// when
		let (_, hash2, _) = push_block_with_offchain();

		// then
		assert_eq!(crate::NumberOfLeaves::<Test>::get(), 2);
		let peaks = peaks_from_leaves_count(2);
		assert_eq!(peaks, vec![2]);
		assert_eq!(
			(
				crate::Peaks::<Test>::get(0),
				crate::Peaks::<Test>::get(1),
				crate::Peaks::<Test>::get(2),
				crate::Peaks::<Test>::get(3),
				crate::RootHash::<Test>::get(),
			),
			(
				None,
				None,
				Some(hex("843450e593a9103c9fe8c0a0276756a90077108b9aa32d6a15c1b77f264b097e")),
				None,
				hex("843450e593a9103c9fe8c0a0276756a90077108b9aa32d6a15c1b77f264b097e"),
			)
		);

		(hash1, hash2)
	});

	let offchain_db = ext.offchain_db();
	assert_eq!(
		offchain_db.get(&MMR::node_offchain_key(hash1, 0)).map(decode_node),
		Some(mmr::Node::Data(((0, H256::repeat_byte(0)), LeafData::new(1),)))
	);
	assert_eq!(
		offchain_db.get(&MMR::node_offchain_key(hash2, 1)).map(decode_node),
		Some(mmr::Node::Data(((1, H256::repeat_byte(1)), LeafData::new(2),)))
	);
	assert_eq!(
		offchain_db.get(&MMR::node_offchain_key(hash2, 2)).map(decode_node),
		Some(mmr::Node::Hash(hex(
			"843450e593a9103c9fe8c0a0276756a90077108b9aa32d6a15c1b77f264b097e"
		)))
	);
	assert_eq!(offchain_db.get(&MMR::node_offchain_key(hash2, 3)), None);

	assert_eq!(offchain_db.get(&MMR::node_canon_offchain_key(0)), None);
	assert_eq!(offchain_db.get(&MMR::node_canon_offchain_key(1)), None);
	assert_eq!(offchain_db.get(&MMR::node_canon_offchain_key(2)), None);
	assert_eq!(offchain_db.get(&MMR::node_canon_offchain_key(3)), None);
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
			assert!(crate::Peaks::<Test>::get(i).is_none());
		}
		assert_eq!(
			(
				crate::Peaks::<Test>::get(6),
				crate::Peaks::<Test>::get(9),
				crate::Peaks::<Test>::get(10),
				crate::RootHash::<Test>::get(),
			),
			(
				Some(hex("7da2dfae4fc5cdb4ea71672cbb36e1b9cc0e1dbc96f150bbc25ae520c4b0a47c")),
				Some(hex("58d8f809c4f813ab84c777602ca4c6f6b47de2461f990767b9188c994b2085af")),
				Some(hex("29d1b9d334844798b202520ed800c676af83e35d037978b63cf7ff1801e20420")),
				hex("5e80aa6a5c45076b3be28c9c5ac297fd2069a455a76db075988c280257d5a7b4"),
			)
		);
	});
}

#[test]
fn should_generate_proofs_correctly() {
	let _ = env_logger::try_init();
	let mut ext = new_test_ext();
	// given
	let num_blocks: u64 = 7;
	ext.execute_with(|| add_blocks_with_offchain(num_blocks as usize));

	// Try to generate proofs now.
	ext.execute_with(|| {
		let best_block_number = frame_system::Pallet::<Test>::block_number();
		// when generate proofs for all leaves.
		let proofs = (1_u64..=best_block_number)
			.into_iter()
			.map(|block_num| crate::Pallet::<Test>::generate_batch_proof(vec![block_num]).unwrap())
			.collect::<Vec<_>>();
		// when generate historical proofs for all leaves
		let historical_proofs = (1_u64..best_block_number)
			.into_iter()
			.map(|block_num| {
				let mut proofs = vec![];
				for leaves_count in block_num..=num_blocks {
					proofs.push(
						crate::Pallet::<Test>::generate_historical_batch_proof(
							vec![block_num],
							leaves_count,
						)
						.unwrap(),
					)
				}
				proofs
			})
			.collect::<Vec<_>>();

		// then
		assert_eq!(
			proofs[0],
			(
				vec![Compact::new(((0, H256::repeat_byte(0)).into(), LeafData::new(1).into(),))],
				BatchProof {
					leaf_indices: vec![0],
					leaf_count: 7,
					items: vec![
						hex("f5ee0f8e3a4a2eebc50a74552ce459259c4a14fc74d100413258b24dbb2172ad"),
						hex("58c20b8520b2a85db7ee9fde973acc340b75bdcfbc6ca8642f66c0a927a9628f"),
						hex("fbf72a451409d1f74ab3d52b7691019838dc9886594eec7c6a075b80d84003bf"),
					],
				}
			)
		);
		assert_eq!(
			historical_proofs[0][0],
			(
				vec![Compact::new(((0, H256::repeat_byte(0)).into(), LeafData::new(1).into(),))],
				BatchProof { leaf_indices: vec![0], leaf_count: 1, items: vec![] }
			)
		);

		//       D
		//     /   \
		//    /     \
		//   A       B       C
		//  / \     / \     / \
		// 1   2   3   4   5   6  7
		//
		// we're proving 3 => we need { 4, A, C++7 }
		assert_eq!(
			proofs[2],
			(
				vec![Compact::new(((2, H256::repeat_byte(2)).into(), LeafData::new(3).into(),))],
				BatchProof {
					leaf_indices: vec![2],
					leaf_count: 7,
					items: vec![
						hex("6d424e7dc63c18a6e193b1d4b2c68306b166494e21c409824016c4671177d48c"),
						hex("843450e593a9103c9fe8c0a0276756a90077108b9aa32d6a15c1b77f264b097e"),
						hex("fbf72a451409d1f74ab3d52b7691019838dc9886594eec7c6a075b80d84003bf"),
					],
				}
			)
		);
		//   A
		//  / \
		// 1   2   3
		//
		// we're proving 3 => we need { A }
		assert_eq!(
			historical_proofs[2][0],
			(
				vec![Compact::new(((2, H256::repeat_byte(2)).into(), LeafData::new(3).into(),))],
				BatchProof {
					leaf_indices: vec![2],
					leaf_count: 3,
					items: vec![hex(
						"843450e593a9103c9fe8c0a0276756a90077108b9aa32d6a15c1b77f264b097e"
					)],
				}
			)
		);
		//       D
		//     /   \
		//    /     \
		//   A       B
		//  / \     / \
		// 1   2   3   4   5
		// we're proving 3 => we need { 4, A, 5 }
		assert_eq!(
			historical_proofs[2][2],
			(
				vec![Compact::new(((2, H256::repeat_byte(2)).into(), LeafData::new(3).into(),))],
				BatchProof {
					leaf_indices: vec![2],
					leaf_count: 5,
					items: vec![
						hex("6d424e7dc63c18a6e193b1d4b2c68306b166494e21c409824016c4671177d48c"),
						hex("843450e593a9103c9fe8c0a0276756a90077108b9aa32d6a15c1b77f264b097e"),
						hex("23b661b811fd03d596a0707caa6bf363e349f4d879eb655540c4b177a6b4b7cc")
					],
				}
			)
		);
		assert_eq!(historical_proofs[2][4], proofs[2]);

		assert_eq!(
			proofs[4],
			(
				vec![Compact::new(((4, H256::repeat_byte(4)).into(), LeafData::new(5).into(),))],
				BatchProof {
					leaf_indices: vec![4],
					leaf_count: 7,
					items: vec![
						hex("7da2dfae4fc5cdb4ea71672cbb36e1b9cc0e1dbc96f150bbc25ae520c4b0a47c"),
						hex("7a76a3de17cab4a41146b68e7f373be6ee88d7f6cf96f853b4ead9db792985fa"),
						hex("29d1b9d334844798b202520ed800c676af83e35d037978b63cf7ff1801e20420"),
					],
				}
			)
		);
		assert_eq!(
			historical_proofs[4][0],
			(
				vec![Compact::new(((4, H256::repeat_byte(4)).into(), LeafData::new(5).into(),))],
				BatchProof {
					leaf_indices: vec![4],
					leaf_count: 5,
					items: vec![hex(
						"7da2dfae4fc5cdb4ea71672cbb36e1b9cc0e1dbc96f150bbc25ae520c4b0a47c"
					),],
				}
			)
		);
		assert_eq!(historical_proofs[4][2], proofs[4]);

		assert_eq!(
			proofs[6],
			(
				vec![Compact::new(((6, H256::repeat_byte(6)).into(), LeafData::new(7).into(),))],
				BatchProof {
					leaf_indices: vec![6],
					leaf_count: 7,
					items: vec![
						hex("7da2dfae4fc5cdb4ea71672cbb36e1b9cc0e1dbc96f150bbc25ae520c4b0a47c"),
						hex("58d8f809c4f813ab84c777602ca4c6f6b47de2461f990767b9188c994b2085af"),
					],
				}
			)
		);
		assert_eq!(historical_proofs[5][1], proofs[5]);
	});
}

#[test]
fn should_generate_batch_proof_correctly() {
	let _ = env_logger::try_init();
	let mut ext = new_test_ext();
	// given
	ext.execute_with(|| add_blocks_with_offchain(7));

	// Try to generate proofs now.
	ext.execute_with(|| {
		// when generate proofs for a batch of leaves
		let (.., proof) = crate::Pallet::<Test>::generate_batch_proof(vec![1, 5, 6]).unwrap();
		// then
		assert_eq!(
			proof,
			BatchProof {
				// the leaf indices are equivalent to the above specified block numbers - 1.
				leaf_indices: vec![0, 4, 5],
				leaf_count: 7,
				items: vec![
					hex("f5ee0f8e3a4a2eebc50a74552ce459259c4a14fc74d100413258b24dbb2172ad"),
					hex("58c20b8520b2a85db7ee9fde973acc340b75bdcfbc6ca8642f66c0a927a9628f"),
					hex("29d1b9d334844798b202520ed800c676af83e35d037978b63cf7ff1801e20420"),
				],
			}
		);

		// when generate historical proofs for a batch of leaves
		let (.., historical_proof) =
			crate::Pallet::<Test>::generate_historical_batch_proof(vec![1, 5, 6], 6).unwrap();
		// then
		assert_eq!(
			historical_proof,
			BatchProof {
				leaf_indices: vec![0, 4, 5],
				leaf_count: 6,
				items: vec![
					hex("f5ee0f8e3a4a2eebc50a74552ce459259c4a14fc74d100413258b24dbb2172ad"),
					hex("58c20b8520b2a85db7ee9fde973acc340b75bdcfbc6ca8642f66c0a927a9628f"),
				],
			}
		);

		// when generate historical proofs for a batch of leaves
		let (.., historical_proof) =
			crate::Pallet::<Test>::generate_historical_batch_proof(vec![1, 5, 6], 7).unwrap();
		// then
		assert_eq!(historical_proof, proof);
	});
}

#[test]
fn should_verify() {
	let _ = env_logger::try_init();

	// Start off with chain initialisation and storing indexing data off-chain
	// (MMR Leafs)
	let mut ext = new_test_ext();
	ext.execute_with(|| add_blocks_with_offchain(7));

	// Try to generate proof now.
	let (leaves, proof5) = ext.execute_with(|| {
		// when
		crate::Pallet::<Test>::generate_batch_proof(vec![5]).unwrap()
	});
	let (simple_historical_leaves, simple_historical_proof5) = ext.execute_with(|| {
		// when
		crate::Pallet::<Test>::generate_historical_batch_proof(vec![5], 6).unwrap()
	});
	let (advanced_historical_leaves, advanced_historical_proof5) = ext.execute_with(|| {
		// when
		crate::Pallet::<Test>::generate_historical_batch_proof(vec![5], 7).unwrap()
	});

	ext.execute_with(|| {
		add_blocks_with_offchain(7);
		// then
		assert_eq!(crate::Pallet::<Test>::verify_leaves(leaves, proof5), Ok(()));
		assert_eq!(
			crate::Pallet::<Test>::verify_leaves(
				simple_historical_leaves,
				simple_historical_proof5
			),
			Ok(())
		);
		assert_eq!(
			crate::Pallet::<Test>::verify_leaves(
				advanced_historical_leaves,
				advanced_historical_proof5
			),
			Ok(())
		);
	});
}

#[test]
fn should_verify_batch_proofs() {
	fn generate_and_verify_batch_proof(
		ext: &mut TestExternalities,
		block_numbers: &Vec<u64>,
		blocks_to_add: usize,
	) {
		let (leaves, proof) = ext.execute_with(|| {
			crate::Pallet::<Test>::generate_batch_proof(block_numbers.to_vec()).unwrap()
		});

		let mmr_size = ext.execute_with(|| crate::Pallet::<Test>::mmr_leaves());
		let min_mmr_size = block_numbers.iter().max().unwrap() + 1;

		// generate historical proofs for all possible mmr sizes,
		// lower bound being index of highest leaf to be proven
		let historical_proofs = (min_mmr_size..=mmr_size)
			.map(|mmr_size| {
				ext.execute_with(|| {
					crate::Pallet::<Test>::generate_historical_batch_proof(
						block_numbers.to_vec(),
						mmr_size,
					)
					.unwrap()
				})
			})
			.collect::<Vec<_>>();

		ext.execute_with(|| {
			add_blocks_with_offchain(blocks_to_add);
			// then
			assert_eq!(crate::Pallet::<Test>::verify_leaves(leaves, proof), Ok(()));
			historical_proofs.iter().for_each(|(leaves, proof)| {
				assert_eq!(
					crate::Pallet::<Test>::verify_leaves(leaves.clone(), proof.clone()),
					Ok(())
				);
			});
		})
	}

	let _ = env_logger::try_init();

	use itertools::Itertools;

	let mut ext = new_test_ext();

	// verify that up to n=10, valid proofs are generated for all possible block number
	// combinations.
	for n in 1..=10 {
		ext.execute_with(|| push_block_with_offchain());

		// generate powerset (skipping empty set) of all possible block number combinations for mmr
		// size n.
		let blocks_set: Vec<Vec<u64>> = (1..=n).into_iter().powerset().skip(1).collect();

		blocks_set.iter().for_each(|blocks_subset| {
			generate_and_verify_batch_proof(&mut ext, &blocks_subset, 0);
		});
	}

	// verify that up to n=15, valid proofs are generated for all possible 2-block number
	// combinations.
	for n in 11..=15 {
		ext.execute_with(|| push_block_with_offchain());

		// generate all possible 2-block number combinations for mmr size n.
		let blocks_set: Vec<Vec<u64>> = (1..=n).into_iter().combinations(2).collect();

		blocks_set.iter().for_each(|blocks_subset| {
			generate_and_verify_batch_proof(&mut ext, &blocks_subset, 0);
		});
	}

	generate_and_verify_batch_proof(&mut ext, &vec![8, 12], 20);
	ext.execute_with(|| add_blocks_with_offchain(1000));
	generate_and_verify_batch_proof(&mut ext, &vec![8, 12, 100, 800], 100);
}

#[test]
fn verification_should_be_stateless() {
	let _ = env_logger::try_init();

	// Start off with chain initialisation and storing indexing data off-chain
	// (MMR Leafs)
	let mut ext = new_test_ext();
	let (root_6, root_7) = ext.execute_with(|| {
		add_blocks_with_offchain(6);
		let root_6 = crate::Pallet::<Test>::mmr_root_hash();
		add_blocks_with_offchain(1);
		let root_7 = crate::Pallet::<Test>::mmr_root_hash();
		(root_6, root_7)
	});

	// Try to generate proof now.
	let (leaves, proof5) = ext.execute_with(|| {
		// when
		crate::Pallet::<Test>::generate_batch_proof(vec![5]).unwrap()
	});
	let (_, historical_proof5) = ext.execute_with(|| {
		// when
		crate::Pallet::<Test>::generate_historical_batch_proof(vec![5], 6).unwrap()
	});

	// Verify proof without relying on any on-chain data.
	let leaf = crate::primitives::DataOrHash::Data(leaves[0].clone());
	assert_eq!(
		crate::verify_leaves_proof::<<Test as Config>::Hashing, _>(
			root_7,
			vec![leaf.clone()],
			proof5
		),
		Ok(())
	);
	assert_eq!(
		crate::verify_leaves_proof::<<Test as Config>::Hashing, _>(
			root_6,
			vec![leaf],
			historical_proof5
		),
		Ok(())
	);
}

#[test]
fn should_verify_batch_proof_statelessly() {
	let _ = env_logger::try_init();

	// Start off with chain initialisation and storing indexing data off-chain
	// (MMR Leafs)
	let mut ext = new_test_ext();
	let (root_6, root_7) = ext.execute_with(|| {
		add_blocks_with_offchain(6);
		let root_6 = crate::Pallet::<Test>::mmr_root_hash();
		add_blocks_with_offchain(1);
		let root_7 = crate::Pallet::<Test>::mmr_root_hash();
		(root_6, root_7)
	});

	// Try to generate proof now.
	let (leaves, proof) = ext.execute_with(|| {
		// when
		crate::Pallet::<Test>::generate_batch_proof(vec![1, 4, 5]).unwrap()
	});
	let (historical_leaves, historical_proof) = ext.execute_with(|| {
		// when
		crate::Pallet::<Test>::generate_historical_batch_proof(vec![1, 4, 5], 6).unwrap()
	});

	// Verify proof without relying on any on-chain data.
	assert_eq!(
		crate::verify_leaves_proof::<<Test as Config>::Hashing, _>(
			root_7,
			leaves
				.into_iter()
				.map(|leaf| crate::primitives::DataOrHash::Data(leaf))
				.collect(),
			proof
		),
		Ok(())
	);
	assert_eq!(
		crate::verify_leaves_proof::<<Test as Config>::Hashing, _>(
			root_6,
			historical_leaves
				.into_iter()
				.map(|leaf| crate::primitives::DataOrHash::Data(leaf))
				.collect(),
			historical_proof
		),
		Ok(())
	);
}

#[test]
fn should_verify_on_the_next_block_since_there_is_no_pruning_yet() {
	let _ = env_logger::try_init();
	let mut ext = new_test_ext();
	// given
	ext.execute_with(|| add_blocks_with_offchain(7));

	ext.execute_with(|| {
		// when
		let (leaves, proof5) = crate::Pallet::<Test>::generate_batch_proof(vec![5]).unwrap();
		push_block_with_offchain();

		// then
		assert_eq!(crate::Pallet::<Test>::verify_leaves(leaves, proof5), Ok(()));
	});
}

#[test]
fn should_verify_pruning_map() {
	use sp_core::offchain::StorageKind;
	use sp_io::offchain;

	let _ = env_logger::try_init();
	let mut ext = new_test_ext();

	ext.execute_with(|| {
		type TestPruningMap = PruningMap<Test, ()>;
		fn offchain_decoded(key: Vec<u8>) -> Option<Vec<H256>> {
			offchain::local_storage_get(StorageKind::PERSISTENT, &key)
				.and_then(|v| codec::Decode::decode(&mut &*v).ok())
		}

		// test append
		{
			TestPruningMap::append(1, H256::repeat_byte(1));

			TestPruningMap::append(2, H256::repeat_byte(21));
			TestPruningMap::append(2, H256::repeat_byte(22));

			TestPruningMap::append(3, H256::repeat_byte(31));
			TestPruningMap::append(3, H256::repeat_byte(32));
			TestPruningMap::append(3, H256::repeat_byte(33));

			// `0` not present
			let map_key = TestPruningMap::pruning_map_offchain_key(0);
			assert_eq!(offchain::local_storage_get(StorageKind::PERSISTENT, &map_key), None);

			// verify `1` entries
			let map_key = TestPruningMap::pruning_map_offchain_key(1);
			let expected = vec![H256::repeat_byte(1)];
			assert_eq!(offchain_decoded(map_key), Some(expected));

			// verify `2` entries
			let map_key = TestPruningMap::pruning_map_offchain_key(2);
			let expected = vec![H256::repeat_byte(21), H256::repeat_byte(22)];
			assert_eq!(offchain_decoded(map_key), Some(expected));

			// verify `3` entries
			let map_key = TestPruningMap::pruning_map_offchain_key(3);
			let expected =
				vec![H256::repeat_byte(31), H256::repeat_byte(32), H256::repeat_byte(33)];
			assert_eq!(offchain_decoded(map_key), Some(expected));

			// `4` not present
			let map_key = TestPruningMap::pruning_map_offchain_key(4);
			assert_eq!(offchain::local_storage_get(StorageKind::PERSISTENT, &map_key), None);
		}

		// test remove
		{
			// `0` doesn't return anything
			assert_eq!(TestPruningMap::remove(0), None);

			// remove and verify `1` entries
			let expected = vec![H256::repeat_byte(1)];
			assert_eq!(TestPruningMap::remove(1), Some(expected));

			// remove and verify `2` entries
			let expected = vec![H256::repeat_byte(21), H256::repeat_byte(22)];
			assert_eq!(TestPruningMap::remove(2), Some(expected));

			// remove and verify `3` entries
			let expected =
				vec![H256::repeat_byte(31), H256::repeat_byte(32), H256::repeat_byte(33)];
			assert_eq!(TestPruningMap::remove(3), Some(expected));

			// `4` doesn't return anything
			assert_eq!(TestPruningMap::remove(4), None);

			// no entries left in offchain map
			for block in 0..5 {
				let map_key = TestPruningMap::pruning_map_offchain_key(block);
				assert_eq!(offchain::local_storage_get(StorageKind::PERSISTENT, &map_key), None);
			}
		}
	})
}

#[test]
fn should_canonicalize_offchain() {
	let _ = env_logger::try_init();
	let mut ext = new_test_ext();

	// adding 13 blocks that we'll later check have been canonicalized,
	// (test assumes `13 < frame_system::BlockHashCount`).
	let to_canon_count = 13u64;

	// add 13 blocks and verify leaves and nodes for them have been added to
	// offchain MMR using fork-proof keys.
	for blocknum in 1..=to_canon_count {
		ext.execute_with(|| {
			let (number, _, _) = push_block_with_offchain();
			assert_eq!(blocknum, number);
		});
	}
	let offchain_db = ext.offchain_db();
	ext.execute_with(|| {
		// verify leaves added by blocks 1..=13
		for block_num in 1..=to_canon_count {
			let block_hash = <frame_system::Pallet<Test>>::block_hash(block_num);
			let leaf_index = block_num - 1;
			let pos = helper::leaf_index_to_pos(leaf_index);
			// not canon,
			assert_eq!(offchain_db.get(&MMR::node_canon_offchain_key(pos)), None);
			// but available in fork-proof storage.
			assert_eq!(
				offchain_db.get(&MMR::node_offchain_key(block_hash, pos)).map(decode_node),
				Some(mmr::Node::Data((
					(leaf_index, H256::repeat_byte(u8::try_from(leaf_index).unwrap())),
					LeafData::new(block_num.into()),
				)))
			);
		}

		// verify a couple of nodes and peaks:
		// 		`pos` is node to verify,
		// 		`leaf_index` is leaf that added node `pos`,
		// 		`expected` is expected value of node at `pos`.
		let verify = |pos: NodeIndex, leaf_index: LeafIndex, expected: H256| {
			let block_num: BlockNumber = (leaf_index + 1).try_into().unwrap();
			let block_hash = <frame_system::Pallet<Test>>::block_hash(block_num);
			// not canon,
			assert_eq!(offchain_db.get(&MMR::node_canon_offchain_key(pos)), None);
			// but available in fork-proof storage.
			let key = MMR::node_offchain_key(block_hash, pos);
			assert_eq!(offchain_db.get(&key).map(decode_node), Some(mmr::Node::Hash(expected)));
		};
		verify(2, 1, hex("843450e593a9103c9fe8c0a0276756a90077108b9aa32d6a15c1b77f264b097e"));
		verify(13, 7, hex("4a170065d8c8d5360d0208f275de1895c892fcfed388decffd41e27fcaa2329f"));
		verify(21, 11, hex("78668e549013242f30f8e810f9a6a5619df9b36a04705a72d2013191c177b8ee"));
	});

	// add another `frame_system::BlockHashCount` blocks and verify all nodes and leaves
	// added by our original `to_canon_count` blocks have now been canonicalized in offchain db.
	let block_hash_size: u64 = <Test as frame_system::Config>::BlockHashCount::get();
	let base = to_canon_count + 1;
	for blocknum in base..(base + block_hash_size) {
		ext.execute_with(|| {
			let (number, _, _) = push_block_with_offchain();
			assert_eq!(blocknum, number);
		});
	}
	ext.execute_with(|| {
		// verify leaves added by blocks 1..=13, should be in offchain under canon key.
		for block_num in 1..=to_canon_count {
			let leaf_index = block_num - 1;
			let pos = helper::leaf_index_to_pos(leaf_index);
			let block_hash = <frame_system::Pallet<Test>>::block_hash(block_num);
			// no longer available in fork-proof storage (was pruned),
			assert_eq!(offchain_db.get(&MMR::node_offchain_key(block_hash, pos)), None);
			// but available using canon key.
			assert_eq!(
				offchain_db.get(&MMR::node_canon_offchain_key(pos)).map(decode_node),
				Some(mmr::Node::Data((
					(leaf_index, H256::repeat_byte(u8::try_from(leaf_index).unwrap())),
					LeafData::new(block_num),
				)))
			);
		}

		// also check some nodes and peaks:
		// 		`pos` is node to verify,
		// 		`leaf_index` is leaf that added node `pos`,
		// 		`expected` is expected value of node at `pos`.
		let verify = |pos: NodeIndex, leaf_index: LeafIndex, expected: H256| {
			let block_hash = <frame_system::Pallet<Test>>::block_hash(leaf_index + 1);
			// no longer available in fork-proof storage (was pruned),
			assert_eq!(offchain_db.get(&MMR::node_offchain_key(block_hash, pos)), None);
			// but available using canon key.
			assert_eq!(
				offchain_db.get(&MMR::node_canon_offchain_key(pos)).map(decode_node),
				Some(mmr::Node::Hash(expected))
			);
		};
		verify(2, 1, hex("843450e593a9103c9fe8c0a0276756a90077108b9aa32d6a15c1b77f264b097e"));
		verify(13, 7, hex("4a170065d8c8d5360d0208f275de1895c892fcfed388decffd41e27fcaa2329f"));
		verify(21, 11, hex("78668e549013242f30f8e810f9a6a5619df9b36a04705a72d2013191c177b8ee"));
	});
}

#[test]
fn should_verify_canonicalized() {
	let _ = env_logger::try_init();

	// How deep is our fork-aware storage (in terms of blocks/leaves, nodes will be more).
	let block_hash_size: u64 = <Test as frame_system::Config>::BlockHashCount::get();

	// Start off with chain initialisation and storing indexing data off-chain.
	// Create twice as many leaf entries than our fork-aware capacity,
	// resulting in ~half of MMR storage to use canonical keys and the other half fork-aware keys.
	// Verify that proofs can be generated (using leaves and nodes from full set) and verified.
	let mut ext = new_test_ext();
	for _ in 0u32..(2 * block_hash_size).try_into().unwrap() {
		ext.execute_with(|| {
			push_block_with_offchain();
		});
	}

	// Generate proofs for some blocks.
	let (leaves, proofs) =
		ext.execute_with(|| crate::Pallet::<Test>::generate_batch_proof(vec![1, 4, 5, 7]).unwrap());
	// Verify all previously generated proofs.
	ext.execute_with(|| {
		assert_eq!(crate::Pallet::<Test>::verify_leaves(leaves, proofs), Ok(()));
	});

	// Generate proofs for some new blocks.
	let (leaves, proofs) = ext.execute_with(|| {
		crate::Pallet::<Test>::generate_batch_proof(vec![block_hash_size + 7]).unwrap()
	});
	// Add some more blocks then verify all previously generated proofs.
	ext.execute_with(|| {
		add_blocks_with_offchain(7);
		assert_eq!(crate::Pallet::<Test>::verify_leaves(leaves, proofs), Ok(()));
	});
}

#[test]
fn does_not_panic_when_generating_historical_proofs() {
	let _ = env_logger::try_init();
	let mut ext = new_test_ext();

	// given 7 blocks (7 MMR leaves)
	ext.execute_with(|| add_blocks_with_offchain(7));

	// Try to generate historical proof with invalid arguments.
	ext.execute_with(|| {
		// when leaf index is invalid
		assert_eq!(
			crate::Pallet::<Test>::generate_historical_batch_proof(vec![10], 7),
			Err(Error::BlockNumToLeafIndex),
		);

		// when leaves count is invalid
		assert_eq!(
			crate::Pallet::<Test>::generate_historical_batch_proof(vec![3], 100),
			Err(Error::BlockNumToLeafIndex),
		);

		// when both leaf index and leaves count are invalid
		assert_eq!(
			crate::Pallet::<Test>::generate_historical_batch_proof(vec![10], 100),
			Err(Error::BlockNumToLeafIndex),
		);
	});
}
