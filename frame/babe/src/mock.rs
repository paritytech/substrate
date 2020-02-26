// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Test utilities

use codec::Encode;
use super::{Trait, Module, GenesisConfig, CurrentSlot};
use sp_runtime::{
	Perbill, impl_opaque_keys,
	testing::{Header, UintAuthorityId, Digest, DigestItem},
	traits::{IdentityLookup, OnInitialize},
};
use frame_system::InitKind;
use frame_support::{impl_outer_origin, parameter_types, StorageValue, weights::Weight};
use sp_io;
use sp_core::H256;

impl_outer_origin!{
	pub enum Origin for Test  where system = frame_system {}
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

pub fn new_test_ext(authorities: Vec<DummyValidatorId>) -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	GenesisConfig {
		authorities: authorities.into_iter().map(|a| (UintAuthorityId(a).to_public_key(), 1)).collect(),
	}.assimilate_storage::<Test>(&mut t).unwrap();
	t.into()
}

pub fn go_to_block(n: u64, s: u64) {
	let pre_digest = make_pre_digest(0, s, [1; 32], [0xff; 64]);
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
	vrf_output: [u8; sp_consensus_babe::VRF_OUTPUT_LENGTH],
	vrf_proof: [u8; sp_consensus_babe::VRF_PROOF_LENGTH],
) -> Digest {
	let digest_data = sp_consensus_babe::digests::RawPreDigest::Primary {
		authority_index,
		slot_number,
		vrf_output,
		vrf_proof,
	};
	let log = DigestItem::PreRuntime(sp_consensus_babe::BABE_ENGINE_ID, digest_data.encode());
	Digest { logs: vec![log] }
}

pub type System = frame_system::Module<Test>;
pub type Babe = Module<Test>;
pub type Session = pallet_session::Module<Test>;
