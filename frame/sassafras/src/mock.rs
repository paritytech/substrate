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

//! Test utilities for Sassafras pallet.

use crate::{self as pallet_sassafras, SameAuthoritiesForever};

use frame_support::traits::{ConstU32, ConstU64, GenesisBuild, OnFinalize, OnInitialize};
use scale_codec::Encode;
use sp_consensus_sassafras::{
	digests::PreDigest,
	vrf::{self, VRFOutput, VRFProof},
	AuthorityIndex, AuthorityPair, Slot,
};
use sp_core::{
	crypto::{IsWrappedBy, Pair},
	H256, U256,
};
use sp_runtime::{
	testing::{Digest, DigestItem, Header, TestXt},
	traits::IdentityLookup,
};

const SLOT_DURATION: u64 = 1000;
const EPOCH_DURATION: u64 = 10;
const MAX_TICKETS: u32 = 6;

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

type DummyValidatorId = u64;

type AccountData = u128;

impl frame_system::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	type Index = u64;
	type BlockNumber = u64;
	type RuntimeCall = RuntimeCall;
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
	RuntimeCall: From<C>,
{
	type OverarchingCall = RuntimeCall;
	type Extrinsic = TestXt<RuntimeCall, ()>;
}

impl pallet_sassafras::Config for Test {
	type SlotDuration = ConstU64<SLOT_DURATION>;
	type EpochDuration = ConstU64<EPOCH_DURATION>;
	type EpochChangeTrigger = SameAuthoritiesForever;
	type MaxAuthorities = ConstU32<10>;
	type MaxTickets = ConstU32<MAX_TICKETS>;
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

/// Build and returns test storage externalities
pub fn new_test_ext(authorities_len: usize) -> sp_io::TestExternalities {
	new_test_ext_with_pairs(authorities_len).1
}

/// Build and returns test storage externalities and authority set pairs used
/// by Sassafras genesis configuration.
pub fn new_test_ext_with_pairs(
	authorities_len: usize,
) -> (Vec<AuthorityPair>, sp_io::TestExternalities) {
	let pairs = (0..authorities_len)
		.map(|i| AuthorityPair::from_seed(&U256::from(i).into()))
		.collect::<Vec<_>>();

	let authorities = pairs.iter().map(|p| (p.public(), 1)).collect();

	let mut storage = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();

	let config = pallet_sassafras::GenesisConfig { authorities, epoch_config: Default::default() };
	<pallet_sassafras::GenesisConfig as GenesisBuild<Test>>::assimilate_storage(
		&config,
		&mut storage,
	)
	.unwrap();

	(pairs, storage.into())
}

fn make_ticket_vrf(slot: Slot, attempt: u32, pair: &AuthorityPair) -> (VRFOutput, VRFProof) {
	let pair = sp_core::sr25519::Pair::from_ref(pair).as_ref();

	let mut epoch = Sassafras::epoch_index();
	let mut randomness = Sassafras::randomness();

	// Check if epoch is going to change on initialization
	let epoch_start = Sassafras::current_epoch_start();
	if epoch_start != 0_u64 && slot >= epoch_start + EPOCH_DURATION {
		epoch += slot.saturating_sub(epoch_start).saturating_div(EPOCH_DURATION);
		randomness = crate::NextRandomness::<Test>::get();
	}

	let transcript = vrf::make_ticket_transcript(&randomness, attempt, epoch);
	let inout = pair.vrf_sign(transcript);
	let output = VRFOutput(inout.0.to_output());
	let proof = VRFProof(inout.1);

	(output, proof)
}

/// Construct at most `attempts` tickets for the given `slot`.
/// TODO-SASS-P3: filter out invalid tickets according to test threshold.
pub fn make_tickets(slot: Slot, attempts: u32, pair: &AuthorityPair) -> Vec<(VRFOutput, VRFProof)> {
	(0..attempts)
		.into_iter()
		.map(|attempt| make_ticket_vrf(slot, attempt, pair))
		.collect()
}

fn make_slot_vrf(slot: Slot, pair: &AuthorityPair) -> (VRFOutput, VRFProof) {
	let pair = sp_core::sr25519::Pair::from_ref(pair).as_ref();

	let mut epoch = Sassafras::epoch_index();
	let mut randomness = Sassafras::randomness();

	// Check if epoch is going to change on initialization.
	let epoch_start = Sassafras::current_epoch_start();
	if epoch_start != 0_u64 && slot >= epoch_start + EPOCH_DURATION {
		epoch += slot.saturating_sub(epoch_start).saturating_div(EPOCH_DURATION);
		randomness = crate::NextRandomness::<Test>::get();
	}

	let transcript = vrf::make_slot_transcript(&randomness, slot, epoch);
	let inout = pair.vrf_sign(transcript);
	let output = VRFOutput(inout.0.to_output());
	let proof = VRFProof(inout.1);

	(output, proof)
}

/// Produce a `PreDigest` instance for the given parameters.
pub fn make_pre_digest(
	authority_idx: AuthorityIndex,
	slot: Slot,
	pair: &AuthorityPair,
) -> PreDigest {
	let (vrf_output, vrf_proof) = make_slot_vrf(slot, pair);
	PreDigest { authority_idx, slot, vrf_output, vrf_proof, ticket_aux: None }
}

/// Produce a `PreDigest` instance for the given parameters and wrap the result into a `Digest`
/// instance.
pub fn make_wrapped_pre_digest(
	authority_idx: AuthorityIndex,
	slot: Slot,
	pair: &AuthorityPair,
) -> Digest {
	let pre_digest = make_pre_digest(authority_idx, slot, pair);
	let log =
		DigestItem::PreRuntime(sp_consensus_sassafras::SASSAFRAS_ENGINE_ID, pre_digest.encode());
	Digest { logs: vec![log] }
}

/// Progress the pallet state up to the given block `number` and `slot`.
pub fn go_to_block(number: u64, slot: Slot, pair: &AuthorityPair) -> Digest {
	Sassafras::on_finalize(System::block_number());
	let parent_hash = System::finalize().hash();

	let digest = make_wrapped_pre_digest(0, slot, pair);

	System::reset_events();
	System::initialize(&number, &parent_hash, &digest);
	Sassafras::on_initialize(number);

	digest
}

/// Progress the pallet state up to the given block `number`.
/// Slots will grow linearly accordingly to blocks.
pub fn progress_to_block(number: u64, pair: &AuthorityPair) -> Option<Digest> {
	let mut slot = Sassafras::current_slot() + 1;
	let mut digest = None;
	for i in System::block_number() + 1..=number {
		let dig = go_to_block(i, slot, pair);
		digest = Some(dig);
		slot = slot + 1;
	}
	digest
}
