// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// Copyright (C) 2021 Subspace Labs, Inc.
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

use crate::{self as pallet_spartan, Config, NormalEpochChange};
use codec::Encode;
use frame_support::{parameter_types, traits::OnInitialize};
use frame_system::InitKind;
use sp_consensus_poc::digests::{PreDigest, Solution};
use sp_core::H256;
use sp_io;
use sp_runtime::{
    testing::{Digest, DigestItem, Header, TestXt},
    traits::{Header as _, IdentityLookup},
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
        Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
        Spartan: pallet_spartan::{Pallet, Call, Storage, Config},
        Timestamp: pallet_timestamp::{Pallet, Call, Storage, Inherent},
    }
);

parameter_types! {
    pub const BlockHashCount: u64 = 250;
    pub const DisabledValidatorsThreshold: Perbill = Perbill::from_percent(16);
    pub BlockWeights: frame_system::limits::BlockWeights =
        frame_system::limits::BlockWeights::simple_max(1024);
}

impl frame_system::Config for Test {
    type BaseCallFilter = ();
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
    type AccountId = u64;
    type Lookup = IdentityLookup<Self::AccountId>;
    type Header = Header;
    type Event = Event;
    type BlockHashCount = BlockHashCount;
    type PalletInfo = PalletInfo;
    type AccountData = pallet_balances::AccountData<u128>;
    type OnNewAccount = ();
    type OnKilledAccount = ();
    type SystemWeightInfo = ();
    type SS58Prefix = ();
    type OnSetCode = ();
}

impl<C> frame_system::offchain::SendTransactionTypes<C> for Test
where
    Call: From<C>,
{
    type OverarchingCall = Call;
    type Extrinsic = TestXt<Call, ()>;
}
parameter_types! {
    pub const UncleGenerations: u64 = 0;
}

impl pallet_authorship::Config for Test {
    type FindAuthor = ();
    type UncleGenerations = UncleGenerations;
    type FilterUncle = ();
    type EventHandler = ();
}

parameter_types! {
    pub const MinimumPeriod: u64 = 1;
}

impl pallet_timestamp::Config for Test {
    type Moment = u64;
    type OnTimestampSet = Spartan;
    type MinimumPeriod = MinimumPeriod;
    type WeightInfo = ();
}

parameter_types! {
    pub const ExistentialDeposit: u128 = 1;
}

impl pallet_balances::Config for Test {
    type MaxLocks = ();
    type Balance = u128;
    type DustRemoval = ();
    type Event = Event;
    type ExistentialDeposit = ExistentialDeposit;
    type AccountStore = System;
    type WeightInfo = ();
}

parameter_types! {
    pub const EpochDuration: u64 = 3;
    pub const ExpectedBlockTime: u64 = 1;
}

impl Config for Test {
    type EpochDuration = EpochDuration;
    type ExpectedBlockTime = ExpectedBlockTime;
    type EpochChangeTrigger = NormalEpochChange;

    // TODO: milestone 3
    // type HandleEquivocation =
    // 	super::EquivocationHandler<Self::KeyOwnerIdentification, Offences, ReportLongevity>;

    type WeightInfo = ();
}

pub fn go_to_block(n: u64, s: u64) {
    use frame_support::traits::OnFinalize;

    Spartan::on_finalize(System::block_number());

    let parent_hash = if System::block_number() > 1 {
        let hdr = System::finalize();
        hdr.hash()
    } else {
        System::parent_hash()
    };

    // TODO: Fix this
    // let pre_digest = PreDigest {
    //     slot: 0.into(),
    //     solution: s.into(),
    // };
    //
    // System::initialize(&n, &parent_hash, &pre_digest, InitKind::Full);
    //
    // Spartan::on_initialize(n);
}

/// Slots will grow accordingly to blocks
pub fn progress_to_block(n: u64) {
    let mut slot = u64::from(Spartan::current_slot()) + 1;
    for i in System::block_number() + 1..=n {
        go_to_block(i, slot);
        slot += 1;
    }
}

pub fn make_pre_digest(slot: sp_consensus_poc::Slot, solution: Solution) -> Digest {
    let digest_data = PreDigest { slot, solution };
    let log = DigestItem::PreRuntime(sp_consensus_poc::POC_ENGINE_ID, digest_data.encode());
    Digest { logs: vec![log] }
}

pub fn new_test_ext() -> sp_io::TestExternalities {
    frame_system::GenesisConfig::default()
        .build_storage::<Test>()
        .unwrap()
        .into()
}

// TODO: milestone 3
// /// Creates an equivocation at the current block, by generating two headers.
// pub fn generate_equivocation_proof(
// 	offender_authority_index: u32,
// 	offender_authority_pair: &AuthorityPair,
// 	slot: Slot,
// ) -> sp_consensus_poc::EquivocationProof<Header> {
// 	use sp_consensus_poc::digests::CompatibleDigestItem;
//
// 	let current_block = System::block_number();
// 	let current_slot = CurrentSlot::<Test>::get();
//
// 	let make_header = || {
// 		let parent_hash = System::parent_hash();
// 		let pre_digest = make_secondary_plain_pre_digest(offender_authority_index, slot);
// 		System::initialize(&current_block, &parent_hash, &pre_digest, InitKind::Full);
// 		System::set_block_number(current_block);
// 		Timestamp::set_timestamp(current_block);
// 		System::finalize()
// 	};
//
// 	// sign the header prehash and sign it, adding it to the block as the seal
// 	// digest item
// 	let seal_header = |header: &mut Header| {
// 		let prehash = header.hash();
// 		let seal = <DigestItem as CompatibleDigestItem>::babe_seal(
// 			offender_authority_pair.sign(prehash.as_ref()),
// 		);
// 		header.digest_mut().push(seal);
// 	};
//
// 	// generate two headers at the current block
// 	let mut h1 = make_header();
// 	let mut h2 = make_header();
//
// 	seal_header(&mut h1);
// 	seal_header(&mut h2);
//
// 	// restore previous runtime state
// 	go_to_block(current_block, *current_slot);
//
// 	sp_consensus_poc::EquivocationProof {
// 		slot,
// 		offender: offender_authority_pair.public(),
// 		first_header: h1,
// 		second_header: h2,
// 	}
// }
