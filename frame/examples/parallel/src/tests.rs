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

use crate::{self as pallet_example_parallel, *};

use frame_support::parameter_types;
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
	Perbill,
};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Example: pallet_example_parallel::{Pallet, Call, Storage},
	}
);

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type Origin = Origin;
	type Call = Call;
	type PalletInfo = PalletInfo;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = sp_core::sr25519::Public;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = BlockHashCount;
	type DbWeight = ();
	type BlockWeights = ();
	type BlockLength = ();
	type Version = ();
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

parameter_types! {
	pub const GracePeriod: u64 = 5;
	pub const UnsignedInterval: u64 = 128;
	pub const UnsignedPriority: u64 = 1 << 20;
}

impl Config for Test {
	type Call = Call;
}

#[test]
fn it_can_enlist() {
	use sp_core::Pair;

	sp_io::TestExternalities::default().execute_with(|| {
		let (pair1, _) = sp_core::sr25519::Pair::generate();
		let (pair2, _) = sp_core::sr25519::Pair::generate();

		let event_name = b"test";

		Example::run_event(Origin::signed(Default::default()), event_name.to_vec())
			.expect("Failed to enlist");

		let participants = vec![
			EnlistedParticipant {
				account: pair1.public().to_vec(),
				signature: AsRef::<[u8]>::as_ref(&pair1.sign(event_name)).to_vec(),
			},
			EnlistedParticipant {
				account: pair2.public().to_vec(),
				signature: AsRef::<[u8]>::as_ref(&pair2.sign(event_name)).to_vec(),
			},
		];

		Example::enlist_participants(Origin::signed(Default::default()), participants)
			.expect("Failed to enlist");

		assert_eq!(Example::participants().len(), 2);
	});
}

#[test]
fn one_wrong_will_not_enlist_anyone() {
	use sp_core::Pair;

	sp_io::TestExternalities::default().execute_with(|| {
		let (pair1, _) = sp_core::sr25519::Pair::generate();
		let (pair2, _) = sp_core::sr25519::Pair::generate();
		let (pair3, _) = sp_core::sr25519::Pair::generate();

		let event_name = b"test";

		Example::run_event(Origin::signed(Default::default()), event_name.to_vec())
			.expect("Failed to enlist");

		let participants = vec![
			EnlistedParticipant {
				account: pair1.public().to_vec(),
				signature: AsRef::<[u8]>::as_ref(&pair1.sign(event_name)).to_vec(),
			},
			EnlistedParticipant {
				account: pair2.public().to_vec(),
				signature: AsRef::<[u8]>::as_ref(&pair2.sign(event_name)).to_vec(),
			},
			// signing wrong event
			EnlistedParticipant {
				account: pair3.public().to_vec(),
				signature: AsRef::<[u8]>::as_ref(&pair3.sign(&[])).to_vec(),
			},
		];

		Example::enlist_participants(Origin::signed(Default::default()), participants)
			.expect("Failed to enlist");

		assert_eq!(Example::participants().len(), 0);
	});
}
