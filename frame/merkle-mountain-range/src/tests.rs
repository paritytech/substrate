// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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
use crate::primitives::{Proof, LeafDataProvider, Compact};

use codec::{Encode, Decode};
use frame_support::{
	impl_outer_origin, parameter_types,
	traits::OnInitialize,
	weights::Weight,
};
use sp_core::{
	H256,
	offchain::{
		testing::TestOffchainExt,
		OffchainExt,
	},
};
use sp_runtime::{
	Perbill,
	testing::Header,
	traits::{
		BlakeTwo256, Keccak256, IdentityLookup,
	},
};
use std::cell::RefCell;

impl_outer_origin! {
	pub enum Origin for Test where system = frame_system {}
}

#[derive(Clone, Eq, PartialEq, Encode, Decode)]
pub struct Test;
parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}
impl frame_system::Trait for Test {
	type BaseCallFilter = ();
	type Origin = Origin;
	type Call = ();
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = sp_core::sr25519::Public;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = ();
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type DbWeight = ();
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumExtrinsicWeight = MaximumBlockWeight;
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
	type PalletInfo = ();
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
}

impl Trait for Test {
	type Hashing = Keccak256;
	type Hash = H256;
	type LeafData = Compact<Keccak256, (frame_system::Module<Test>, LeafData)>;
}

#[derive(Encode, Decode, Clone, Default, Eq, PartialEq, Debug)]
pub struct LeafData {
	pub a: u64,
	pub b: String,
}

impl LeafData {
	fn new(a: u64) -> Self {
		Self {
			a,
			b: Default::default(),
		}
	}
}

thread_local! {
	pub static LEAF_DATA: RefCell<LeafData> = RefCell::new(Default::default());
}

impl LeafDataProvider for LeafData {
	type LeafData = Self;

	fn leaf_data() -> (Self::LeafData, Weight) {
		(LEAF_DATA.with(|r| r.borrow().clone()), 1)
	}
}

type MMR = Module<Test>;

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
		&Default::default(),
		frame_system::InitKind::Full,
	);
	MMR::on_initialize(number)
}

pub(crate) fn hex(s: &str) -> H256 {
	s.parse().unwrap()
}

fn decode_node(v: Vec<u8>) -> mmr::Node<
	<Test as Trait>::Hashing,
	(H256, LeafData),
> {
	codec::Decode::decode(&mut &v[..]).unwrap()
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
		assert_eq!(crate::NumberOfLeaves::get(), 0);
		assert_eq!(crate::Nodes::<Test>::get(0), None);

		// when
		let weight = new_block();

		// then
		assert_eq!(crate::NumberOfLeaves::get(), 1);
		assert_eq!(crate::Nodes::<Test>::get(0),
			Some(hex("c3e7ba6b511162fead58f2c8b5764ce869ed1118011ac37392522ed16720bbcd")));
		assert_eq!(
			crate::RootHash::<Test>::get(),
			hex("c3e7ba6b511162fead58f2c8b5764ce869ed1118011ac37392522ed16720bbcd")
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
		assert_eq!(crate::NumberOfLeaves::get(), 2);
		assert_eq!(crate::Nodes::<Test>::get(0),
			Some(hex("c3e7ba6b511162fead58f2c8b5764ce869ed1118011ac37392522ed16720bbcd")));
		assert_eq!(crate::Nodes::<Test>::get(1),
			Some(hex("037ff5a3903a59630e03b84cda912c26bf19442efe2cd30c2a25547e06ded385")));
		assert_eq!(crate::Nodes::<Test>::get(2),
			Some(hex("21b847809cbb535ba771e7bb25b33985b5259f1f3fc9cae81bc097f56efbbd36")));
		assert_eq!(crate::Nodes::<Test>::get(3), None);
		assert_eq!(
			crate::RootHash::<Test>::get(),
			hex("21b847809cbb535ba771e7bb25b33985b5259f1f3fc9cae81bc097f56efbbd36")
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
		hex("21b847809cbb535ba771e7bb25b33985b5259f1f3fc9cae81bc097f56efbbd36")
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
		assert_eq!(crate::NumberOfLeaves::get(), 7);
		assert_eq!(crate::Nodes::<Test>::get(0),
			Some(hex("c3e7ba6b511162fead58f2c8b5764ce869ed1118011ac37392522ed16720bbcd")));
		assert_eq!(crate::Nodes::<Test>::get(10),
			Some(hex("32d44b4a8e8a3046b9c02315847eb091678a59f136226e70d66f3a82bd836ce1")));
		assert_eq!(
			crate::RootHash::<Test>::get(),
			hex("3106f5c4ee095d996b61283b4d7b524c0c2acb4c9eaff90da0c216709b8bd1b7")
		);
	});
}

#[test]
fn should_generate_proofs_correclty() {
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
		let proofs = (0_u64..crate::NumberOfLeaves::get())
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
				hex("037ff5a3903a59630e03b84cda912c26bf19442efe2cd30c2a25547e06ded385"),
				hex("5e149bed24a6997e0440cd2daeaae5b44074e9f2f1403c4149ba3e8a9e5baef1"),
				hex("e858832b2bc93dceb94c0df74e5d897ed418140623af150076116f82fb19e78f"),
			],
		}));
		assert_eq!(proofs[4], (Compact::new((
			H256::repeat_byte(5).into(),
			LeafData::new(5).into(),
		)), Proof {
			leaf_index: 4,
			leaf_count: 7,
			items: vec![
				hex("169dc0e8d0a804f16f2081941199ba3630463c29a761d1e20a7096b33ed8a448"),
				hex("e232c7350837c9d87a948ddfc4286cc49d946e8cdad9121e91595f190ed7e54d"),
				hex("32d44b4a8e8a3046b9c02315847eb091678a59f136226e70d66f3a82bd836ce1"),
			],
		}));
		assert_eq!(proofs[6], (Compact::new((
			H256::repeat_byte(7).into(),
			LeafData::new(7).into(),
		)), Proof {
			leaf_index: 6,
			leaf_count: 7,
			items: vec![
				hex("169dc0e8d0a804f16f2081941199ba3630463c29a761d1e20a7096b33ed8a448"),
				hex("ae11d66a54590bd5c28adf98dfcbb5b05feb7fd51997c4e99c73e87de9ac4e49"),
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
