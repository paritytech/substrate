// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! Test utilities

use codec::Encode;
use super::{Trait, Module, GenesisConfig, CurrentSlot};
use sp_runtime::{
	Perbill, impl_opaque_keys,
	testing::{Header, UintAuthorityId, Digest, DigestItem},
	traits::IdentityLookup,
};
use frame_system::InitKind;
use frame_support::{
	impl_outer_origin, parameter_types, StorageValue,
	traits::OnInitialize,
	weights::Weight,
};
use sp_io;
use sp_core::{H256, U256, crypto::Pair};
use sp_consensus_babe::AuthorityPair;
use sp_consensus_vrf::schnorrkel::{VRFOutput, VRFProof};

impl_outer_origin!{
	pub enum Origin for Test where system = frame_system {}
}

type DummyValidatorId = u64;

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Test;

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
	pub const MinimumPeriod: u64 = 1;
	pub const EpochDuration: u64 = 3;
	pub const ExpectedBlockTime: u64 = 1;
	pub const DisabledValidatorsThreshold: Perbill = Perbill::from_percent(16);
}

impl frame_system::Trait for Test {
	type BaseCallFilter = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = ();
	type Hash = H256;
	type Version = ();
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = DummyValidatorId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = ();
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type DbWeight = ();
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumExtrinsicWeight = MaximumBlockWeight;
	type AvailableBlockRatio = AvailableBlockRatio;
	type MaximumBlockLength = MaximumBlockLength;
	type ModuleToIndex = ();
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
}

impl_opaque_keys! {
	pub struct MockSessionKeys {
		pub dummy: UintAuthorityId,
	}
}

impl pallet_session::Trait for Test {
	type Event = ();
	type ValidatorId = <Self as frame_system::Trait>::AccountId;
	type ShouldEndSession = Babe;
	type SessionHandler = (Babe,);
	type SessionManager = ();
	type ValidatorIdOf = ();
	type Keys = MockSessionKeys;
	type DisabledValidatorsThreshold = DisabledValidatorsThreshold;
	type NextSessionRotation = Babe;
}

impl pallet_timestamp::Trait for Test {
	type Moment = u64;
	type OnTimestampSet = Babe;
	type MinimumPeriod = MinimumPeriod;
}

impl Trait for Test {
	type EpochDuration = EpochDuration;
	type ExpectedBlockTime = ExpectedBlockTime;
	type EpochChangeTrigger = crate::ExternalTrigger;
}

pub fn new_test_ext(authorities_len: usize) -> (Vec<AuthorityPair>, sp_io::TestExternalities) {
	let pairs = (0..authorities_len).map(|i| {
		AuthorityPair::from_seed(&U256::from(i).into())
	}).collect::<Vec<_>>();

	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	GenesisConfig {
		authorities: pairs.iter().map(|a| (a.public(), 1)).collect(),
	}.assimilate_storage::<Test>(&mut t).unwrap();
	(pairs, t.into())
}

pub fn go_to_block(n: u64, s: u64) {
	let pre_digest = make_secondary_plain_pre_digest(0, s);
	System::initialize(&n, &Default::default(), &Default::default(), &pre_digest, InitKind::Full);
	System::set_block_number(n);
	if s > 1 {
		CurrentSlot::put(s);
	}
	// includes a call into `Babe::do_initialize`.
	Session::on_initialize(n);
}

/// Slots will grow accordingly to blocks
pub fn progress_to_block(n: u64) {
	let mut slot = Babe::current_slot() + 1;
	for i in System::block_number()+1..=n {
		go_to_block(i, slot);
		slot += 1;
	}
}

pub fn make_pre_digest(
	authority_index: sp_consensus_babe::AuthorityIndex,
	slot_number: sp_consensus_babe::SlotNumber,
	vrf_output: VRFOutput,
	vrf_proof: VRFProof,
) -> Digest {
	let digest_data = sp_consensus_babe::digests::PreDigest::Primary(
		sp_consensus_babe::digests::PrimaryPreDigest {
			authority_index,
			slot_number,
			vrf_output,
			vrf_proof,
		}
	);
	let log = DigestItem::PreRuntime(sp_consensus_babe::BABE_ENGINE_ID, digest_data.encode());
	Digest { logs: vec![log] }
}

pub fn make_secondary_plain_pre_digest(
	authority_index: sp_consensus_babe::AuthorityIndex,
	slot_number: sp_consensus_babe::SlotNumber,
) -> Digest {
	let digest_data = sp_consensus_babe::digests::PreDigest::SecondaryPlain(
		sp_consensus_babe::digests::SecondaryPlainPreDigest {
			authority_index,
			slot_number,
		}
	);
	let log = DigestItem::PreRuntime(sp_consensus_babe::BABE_ENGINE_ID, digest_data.encode());
	Digest { logs: vec![log] }
}

pub type System = frame_system::Module<Test>;
pub type Babe = Module<Test>;
pub type Session = pallet_session::Module<Test>;
