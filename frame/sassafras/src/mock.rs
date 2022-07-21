// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Test utilities for Sassafras consensus.

// TODO-SASS-P2 remove
#![allow(unused_imports)]

use crate::{self as pallet_sassafras, Authorities, Config};

use frame_support::{
	parameter_types,
	traits::{ConstU128, ConstU32, ConstU64, GenesisBuild, KeyOwnerProofSystem, OnInitialize},
};
use scale_codec::Encode;
use sp_consensus_sassafras::{AuthorityId, AuthorityPair, Slot};
use sp_consensus_vrf::schnorrkel::{VRFOutput, VRFProof};
use sp_core::{
	crypto::{IsWrappedBy, KeyTypeId, Pair},
	H256, U256,
};
use sp_runtime::{
	curve::PiecewiseLinear,
	impl_opaque_keys,
	testing::{Digest, DigestItem, Header, TestXt},
	traits::{Header as _, IdentityLookup, OpaqueKeys},
	Perbill,
};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

type DummyValidatorId = u64;

type AccountData = u128;

parameter_types! {
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(1024);
}

impl frame_system::Config for Test {
	type Event = Event;
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = Call;
	type Hash = H256;
	type Version = ();
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = DummyValidatorId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type BlockHashCount = ConstU64<250>;
	type PalletInfo = PalletInfo;
	type AccountData = AccountData;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

impl pallet_timestamp::Config for Test {
	type Moment = u64;
	type OnTimestampSet = (); //Sassafras;
	type MinimumPeriod = ConstU64<1>;
	type WeightInfo = ();
}

impl<C> frame_system::offchain::SendTransactionTypes<C> for Test
where
	Call: From<C>,
{
	type OverarchingCall = Call;
	type Extrinsic = TestXt<Call, ()>;
}

impl pallet_sassafras::Config for Test {
	type EpochDuration = ConstU64<3>;
	type ExpectedBlockTime = ConstU64<1>;
	type EpochChangeTrigger = crate::SameAuthoritiesForever;
	type MaxAuthorities = ConstU32<10>;
	type MaxTickets = ConstU32<3>;
	type MaxSubmittedTickets = ConstU32<3>;
}

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system,
		Sassafras: pallet_sassafras,
	}
);

pub fn new_test_ext(authorities_len: usize) -> sp_io::TestExternalities {
	new_test_ext_with_pairs(authorities_len).1
}

pub fn new_test_ext_with_pairs(
	authorities_len: usize,
) -> (Vec<AuthorityPair>, sp_io::TestExternalities) {
	let pairs = (0..authorities_len)
		.map(|i| AuthorityPair::from_seed(&U256::from(i).into()))
		.collect::<Vec<_>>();

	let authorities = pairs.iter().map(|p| (p.public(), 1)).collect();

	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();

	let config = pallet_sassafras::GenesisConfig { authorities, epoch_config: Default::default() };
	<pallet_sassafras::GenesisConfig as GenesisBuild<Test>>::assimilate_storage(&config, &mut t)
		.unwrap();

	(pairs, t.into())
}
