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
use crate::primitives::Leaf;

use codec::{Encode, Decode};
use frame_support::{
	impl_outer_origin, parameter_types,
	traits::OnInitialize,
	weights::Weight,
};
use sp_core::H256;
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
	type ModuleToIndex = ();
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
}

impl Trait for Test {
	type Hashing = Keccak256;
	type Hash = H256;
	type LeafData = LeafData;
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

impl crate::LeafDataProvider for LeafData {
	type LeafData = Self;

	fn leaf_data() -> (Self::LeafData, Weight) {
		(LEAF_DATA.with(|r| r.borrow().clone()), 1)
	}
}

type MMR = Module<Test>;

pub(crate) fn new_test_ext() -> sp_io::TestExternalities {
	frame_system::GenesisConfig::default().build_storage::<Test>().unwrap().into()
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

fn hex(s: &str) -> H256 {
	s.parse().unwrap()
}

fn decode_node(v: Vec<u8>) -> crate::MMRNode<
	<Test as Trait>::Hashing,
	Leaf<H256, LeafData>,
> {
	codec::Decode::decode(&mut &v[..]).unwrap()
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
	assert_eq!(offchain_db.get(&MMR::offchain_key(0)).map(decode_node), Some(MMRNode::Leaf(Leaf {
		hash: H256::repeat_byte(1),
		data: LeafData::new(1),
	})));
	assert_eq!(offchain_db.get(&MMR::offchain_key(1)).map(decode_node), Some(MMRNode::Leaf(Leaf {
		hash: H256::repeat_byte(2),
		data: LeafData::new(2),
	})));
	assert_eq!(offchain_db.get(&MMR::offchain_key(2)).map(decode_node), Some(MMRNode::Inner(
		hex("21b847809cbb535ba771e7bb25b33985b5259f1f3fc9cae81bc097f56efbbd36")
	)));
	assert_eq!(offchain_db.get(&MMR::offchain_key(3)), None);
}

#[test]
fn should_construct_larger_mmr_correctly() {
	let _ = env_logger::try_init();
	new_test_ext().execute_with(|| {
		// when
		for _ in 0..7 {
			new_block();
		}

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


		// Generate proofs for all leaves
		let proofs = (0_u64..crate::NumberOfLeaves::get())
			.into_iter()
			.map(|leaf_index| crate::Module::<Test>::generate_proof(leaf_index).unwrap())
			.collect::<Vec<_>>();

		assert_eq!(proofs[0], crate::primitives::Proof {
			leaf: 0,
			items: vec![],
		});
		assert_eq!(proofs[4], crate::primitives::Proof {
			leaf: 4,
			items: vec![],
		});
		assert_eq!(proofs[6], crate::primitives::Proof {
			leaf: 6,
			items: vec![],
		});
		// TODO [ToDr] Check that proving works.
		// TODO [ToDr] Prune non-peaks.
	});
}
