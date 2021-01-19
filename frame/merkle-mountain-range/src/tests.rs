// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use crate::*;
use crate::mock::*;
use crate::primitives::{Proof, Compact};

use frame_support::traits::OnInitialize;
use sp_core::{
	H256,
	offchain::{
		testing::TestOffchainExt,
		OffchainExt,
	},
};

pub(crate) fn new_test_ext() -> sp_io::TestExternalities {
	frame_system::GenesisConfig::default().build_storage::<Test>().unwrap().into()
}

fn register_offchain_ext(ext: &mut sp_io::TestExternalities) {
	let (offchain, _offchain_state) = TestOffchainExt::with_offchain_db(ext.offchain_db());
	ext.register_extension(OffchainExt::new(offchain));
}

fn new_block() -> u64 {
	let number = frame_system::Module::<Test>::block_number() + 1;
	let hash = H256::repeat_byte(number as u8);
	LEAF_DATA.with(|r| r.borrow_mut().a = number);

	frame_system::Module::<Test>::initialize(
		&number,
		&hash,
		&Default::default(),
		frame_system::InitKind::Full,
	);
	MMR::on_initialize(number)
}

pub(crate) fn hex(s: &str) -> H256 {
	s.parse().unwrap()
}

fn decode_node(v: Vec<u8>) -> mmr::Node<
	<Test as Config>::Hashing,
	(H256, LeafData),
> {
	use crate::primitives::DataOrHash;
	type A = DataOrHash::<<Test as Config>::Hashing, H256>;
	type B = DataOrHash::<<Test as Config>::Hashing, LeafData>;
	type Node = mmr::Node<<Test as Config>::Hashing, (A, B)>;
	let tuple: Node = codec::Decode::decode(&mut &v[..]).unwrap();

	match tuple {
		mmr::Node::Data((DataOrHash::Data(a), DataOrHash::Data(b))) => mmr::Node::Data((a, b)),
		mmr::Node::Hash(hash) => mmr::Node::Hash(hash),
		_ => unreachable!(),
	}
}

fn init_chain(blocks: usize) {
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
			"0000000000000000000000000000000000000000000000000000000000000000".parse().unwrap()
		);
		assert_eq!(crate::NumberOfLeaves::<DefaultInstance>::get(), 0);
		assert_eq!(crate::Nodes::<Test>::get(0), None);

		// when
		let weight = new_block();

		// then
		assert_eq!(crate::NumberOfLeaves::<DefaultInstance>::get(), 1);
		assert_eq!(crate::Nodes::<Test>::get(0),
			Some(hex("da5e6d0616e05c6a6348605a37ca33493fc1a15ad1e6a405ee05c17843fdafed")));
		assert_eq!(
			crate::RootHash::<Test>::get(),
			hex("da5e6d0616e05c6a6348605a37ca33493fc1a15ad1e6a405ee05c17843fdafed")
		);
		assert!(weight != 0);
	});
}

#[test]
fn should_append_to_mmr_when_on_initialize_is_called() {
	let _ = env_logger::try_init();
	let mut ext = new_test_ext();
	ext.execute_with(|| {
		// when
		new_block();
		new_block();

		// then
		assert_eq!(crate::NumberOfLeaves::<DefaultInstance>::get(), 2);
		assert_eq!(crate::Nodes::<Test>::get(0),
			Some(hex("da5e6d0616e05c6a6348605a37ca33493fc1a15ad1e6a405ee05c17843fdafed")));
		assert_eq!(crate::Nodes::<Test>::get(1),
			Some(hex("ff5d891b28463a3440e1b650984685efdf260e482cb3807d53c49090841e755f")));
		assert_eq!(crate::Nodes::<Test>::get(2),
			Some(hex("bc54778fab79f586f007bd408dca2c4aa07959b27d1f2c8f4f2549d1fcfac8f8")));
		assert_eq!(crate::Nodes::<Test>::get(3), None);
		assert_eq!(
			crate::RootHash::<Test>::get(),
			hex("bc54778fab79f586f007bd408dca2c4aa07959b27d1f2c8f4f2549d1fcfac8f8")
		);
	});

	// make sure the leaves end up in the offchain DB
	ext.persist_offchain_overlay();
	let offchain_db = ext.offchain_db();
	assert_eq!(offchain_db.get(&MMR::offchain_key(0)).map(decode_node), Some(mmr::Node::Data((
		H256::repeat_byte(1),
		LeafData::new(1),
	))));
	assert_eq!(offchain_db.get(&MMR::offchain_key(1)).map(decode_node), Some(mmr::Node::Data((
		H256::repeat_byte(2),
		LeafData::new(2),
	))));
	assert_eq!(offchain_db.get(&MMR::offchain_key(2)).map(decode_node), Some(mmr::Node::Hash(
		hex("bc54778fab79f586f007bd408dca2c4aa07959b27d1f2c8f4f2549d1fcfac8f8")
	)));
	assert_eq!(offchain_db.get(&MMR::offchain_key(3)), None);
}

#[test]
fn should_construct_larger_mmr_correctly() {
	let _ = env_logger::try_init();
	new_test_ext().execute_with(|| {
		// when
		init_chain(7);

		// then
		assert_eq!(crate::NumberOfLeaves::<DefaultInstance>::get(), 7);
		assert_eq!(crate::Nodes::<Test>::get(0),
			Some(hex("da5e6d0616e05c6a6348605a37ca33493fc1a15ad1e6a405ee05c17843fdafed")));
		assert_eq!(crate::Nodes::<Test>::get(10),
			Some(hex("af3327deed0515c8d1902c9b5cd375942d42f388f3bfe3d1cd6e1b86f9cc456c")));
		assert_eq!(
			crate::RootHash::<Test>::get(),
			hex("fc4f9042bd2f73feb26f3fc42db834c5f1943fa20070ddf106c486a478a0d561")
		);
	});
}

#[test]
fn should_generate_proofs_correctly() {
	let _ = env_logger::try_init();
	let mut ext = new_test_ext();
	// given
	ext.execute_with(|| init_chain(7));
	ext.persist_offchain_overlay();

	// Try to generate proofs now. This requires the offchain extensions to be present
	// to retrieve full leaf data.
	register_offchain_ext(&mut ext);
	ext.execute_with(|| {
		// when generate proofs for all leaves
		let proofs = (0_u64..crate::NumberOfLeaves::<DefaultInstance>::get())
			.into_iter()
			.map(|leaf_index| crate::Module::<Test>::generate_proof(leaf_index).unwrap())
			.collect::<Vec<_>>();

		// then
		assert_eq!(proofs[0], (Compact::new((
			H256::repeat_byte(1).into(),
			LeafData::new(1).into(),
		)), Proof {
			leaf_index: 0,
			leaf_count: 7,
			items: vec![
				hex("ff5d891b28463a3440e1b650984685efdf260e482cb3807d53c49090841e755f"),
				hex("00b0046bd2d63fcb760cf50a262448bb2bbf9a264b0b0950d8744044edf00dc3"),
				hex("16de0900b57bf359a0733674ebfbba0f494e95a8391b4bfeae850019399f3ec0"),
			],
		}));
		assert_eq!(proofs[4], (Compact::new((
			H256::repeat_byte(5).into(),
			LeafData::new(5).into(),
		)), Proof {
			leaf_index: 4,
			leaf_count: 7,
			items: vec![
				hex("e53ee36ba6c068b1a6cfef7862fed5005df55615e1c9fa6eeefe08329ac4b94b"),
				hex("c09d4a008a0f1ef37860bef33ec3088ccd94268c0bfba7ff1b3c2a1075b0eb92"),
				hex("af3327deed0515c8d1902c9b5cd375942d42f388f3bfe3d1cd6e1b86f9cc456c"),
			],
		}));
		assert_eq!(proofs[6], (Compact::new((
			H256::repeat_byte(7).into(),
			LeafData::new(7).into(),
		)), Proof {
			leaf_index: 6,
			leaf_count: 7,
			items: vec![
				hex("e53ee36ba6c068b1a6cfef7862fed5005df55615e1c9fa6eeefe08329ac4b94b"),
				hex("dad09f50b41822fc5ecadc25b08c3a61531d4d60e962a5aa0b6998fad5c37c5e"),
			],
		}));
	});
}

#[test]
fn should_verify() {
	let _ = env_logger::try_init();

	// Start off with chain initialisation and storing indexing data off-chain
	// (MMR Leafs)
	let mut ext = new_test_ext();
	ext.execute_with(|| init_chain(7));
	ext.persist_offchain_overlay();

	// Try to generate proof now. This requires the offchain extensions to be present
	// to retrieve full leaf data.
	register_offchain_ext(&mut ext);
	let (leaf, proof5) = ext.execute_with(|| {
		// when
		crate::Module::<Test>::generate_proof(5).unwrap()
	});

	// Now to verify the proof, we really shouldn't require offchain storage or extension.
	// Hence we initialize the storage once again, using different externalities and then
	// verify.
	let mut ext2 = new_test_ext();
	ext2.execute_with(|| {
		init_chain(7);
		// then
		assert_eq!(crate::Module::<Test>::verify_leaf(leaf, proof5), Ok(()));
	});
}

#[test]
fn should_verify_on_the_next_block_since_there_is_no_pruning_yet() {
	let _ = env_logger::try_init();
	let mut ext = new_test_ext();
	// given
	ext.execute_with(|| init_chain(7));

	ext.persist_offchain_overlay();
	register_offchain_ext(&mut ext);

	ext.execute_with(|| {
		// when
		let (leaf, proof5) = crate::Module::<Test>::generate_proof(5).unwrap();
		new_block();

		// then
		assert_eq!(crate::Module::<Test>::verify_leaf(leaf, proof5), Ok(()));
	});
}
