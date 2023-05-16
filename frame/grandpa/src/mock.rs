// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

#![cfg(test)]

use crate::{self as pallet_grandpa, AuthorityId, AuthorityList, Config, ConsensusLog};
use ::grandpa as finality_grandpa;
use codec::Encode;
use frame_election_provider_support::{onchain, SequentialPhragmen};
use frame_support::{
	parameter_types,
	traits::{
		ConstU128, ConstU32, ConstU64, GenesisBuild, KeyOwnerProofSystem, OnFinalize, OnInitialize,
	},
};
use pallet_session::historical as pallet_session_historical;
use sp_consensus_grandpa::{RoundNumber, SetId, GRANDPA_ENGINE_ID};
use sp_core::{crypto::KeyTypeId, H256};
use sp_keyring::Ed25519Keyring;
use sp_runtime::{
	curve::PiecewiseLinear,
	impl_opaque_keys,
	testing::{Header, TestXt, UintAuthorityId},
	traits::{IdentityLookup, OpaqueKeys},
	DigestItem, Perbill,
};
use sp_staking::{EraIndex, SessionIndex};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system,
		Authorship: pallet_authorship,
		Timestamp: pallet_timestamp,
		Balances: pallet_balances,
		Staking: pallet_staking,
		Session: pallet_session,
		Grandpa: pallet_grandpa,
		Offences: pallet_offences,
		Historical: pallet_session_historical,
	}
);

impl_opaque_keys! {
	pub struct TestSessionKeys {
		pub grandpa_authority: super::Pallet<Test>,
	}
}

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	type Index = u64;
	type BlockNumber = u64;
	type RuntimeCall = RuntimeCall;
	type Hash = H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u128>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

impl<C> frame_system::offchain::SendTransactionTypes<C> for Test
where
	RuntimeCall: From<C>,
{
	type OverarchingCall = RuntimeCall;
	type Extrinsic = TestXt<RuntimeCall, ()>;
}

parameter_types! {
	pub const Period: u64 = 1;
	pub const Offset: u64 = 0;
}

/// Custom `SessionHandler` since we use `TestSessionKeys` as `Keys`.
impl pallet_session::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type ValidatorId = u64;
	type ValidatorIdOf = pallet_staking::StashOf<Self>;
	type ShouldEndSession = pallet_session::PeriodicSessions<ConstU64<1>, ConstU64<0>>;
	type NextSessionRotation = pallet_session::PeriodicSessions<ConstU64<1>, ConstU64<0>>;
	type SessionManager = pallet_session::historical::NoteHistoricalRoot<Self, Staking>;
	type SessionHandler = <TestSessionKeys as OpaqueKeys>::KeyTypeIdProviders;
	type Keys = TestSessionKeys;
	type WeightInfo = ();
}

impl pallet_session::historical::Config for Test {
	type FullIdentification = pallet_staking::Exposure<u64, u128>;
	type FullIdentificationOf = pallet_staking::ExposureOf<Self>;
}

impl pallet_authorship::Config for Test {
	type FindAuthor = ();
	type EventHandler = ();
}

impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type Balance = u128;
	type DustRemoval = ();
	type RuntimeEvent = RuntimeEvent;
	type ExistentialDeposit = ConstU128<1>;
	type AccountStore = System;
	type WeightInfo = ();
	type FreezeIdentifier = ();
	type MaxFreezes = ();
	type HoldIdentifier = ();
	type MaxHolds = ();
}

impl pallet_timestamp::Config for Test {
	type Moment = u64;
	type OnTimestampSet = ();
	type MinimumPeriod = ConstU64<3>;
	type WeightInfo = ();
}

pallet_staking_reward_curve::build! {
	const REWARD_CURVE: PiecewiseLinear<'static> = curve!(
		min_inflation: 0_025_000u64,
		max_inflation: 0_100_000,
		ideal_stake: 0_500_000,
		falloff: 0_050_000,
		max_piece_count: 40,
		test_precision: 0_005_000,
	);
}

parameter_types! {
	pub const SessionsPerEra: SessionIndex = 3;
	pub const BondingDuration: EraIndex = 3;
	pub const RewardCurve: &'static PiecewiseLinear<'static> = &REWARD_CURVE;
	pub const OffendingValidatorsThreshold: Perbill = Perbill::from_percent(17);
}

pub struct OnChainSeqPhragmen;
impl onchain::Config for OnChainSeqPhragmen {
	type System = Test;
	type Solver = SequentialPhragmen<u64, Perbill>;
	type DataProvider = Staking;
	type WeightInfo = ();
	type MaxWinners = ConstU32<100>;
	type VotersBound = ConstU32<{ u32::MAX }>;
	type TargetsBound = ConstU32<{ u32::MAX }>;
}

impl pallet_staking::Config for Test {
	type MaxNominations = ConstU32<16>;
	type RewardRemainder = ();
	type CurrencyToVote = frame_support::traits::SaturatingCurrencyToVote;
	type RuntimeEvent = RuntimeEvent;
	type Currency = Balances;
	type CurrencyBalance = <Self as pallet_balances::Config>::Balance;
	type Slash = ();
	type Reward = ();
	type SessionsPerEra = SessionsPerEra;
	type BondingDuration = BondingDuration;
	type SlashDeferDuration = ();
	type AdminOrigin = frame_system::EnsureRoot<Self::AccountId>;
	type SessionInterface = Self;
	type UnixTime = pallet_timestamp::Pallet<Test>;
	type EraPayout = pallet_staking::ConvertCurve<RewardCurve>;
	type MaxNominatorRewardedPerValidator = ConstU32<64>;
	type OffendingValidatorsThreshold = OffendingValidatorsThreshold;
	type NextNewSession = Session;
	type ElectionProvider = onchain::OnChainExecution<OnChainSeqPhragmen>;
	type GenesisElectionProvider = Self::ElectionProvider;
	type VoterList = pallet_staking::UseNominatorsAndValidatorsMap<Self>;
	type TargetList = pallet_staking::UseValidatorsMap<Self>;
	type MaxUnlockingChunks = ConstU32<32>;
	type HistoryDepth = ConstU32<84>;
	type OnStakerSlash = ();
	type BenchmarkingConfig = pallet_staking::TestBenchmarkingConfig;
	type WeightInfo = ();
}

impl pallet_offences::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type IdentificationTuple = pallet_session::historical::IdentificationTuple<Self>;
	type OnOffenceHandler = Staking;
}

parameter_types! {
	pub const ReportLongevity: u64 =
		BondingDuration::get() as u64 * SessionsPerEra::get() as u64 * Period::get();
	pub const MaxSetIdSessionEntries: u32 = BondingDuration::get() * SessionsPerEra::get();
}

impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type WeightInfo = ();
	type MaxAuthorities = ConstU32<100>;
	type MaxSetIdSessionEntries = MaxSetIdSessionEntries;
	type KeyOwnerProof = <Historical as KeyOwnerProofSystem<(KeyTypeId, AuthorityId)>>::Proof;
	type EquivocationReportSystem =
		super::EquivocationReportSystem<Self, Offences, Historical, ReportLongevity>;
}

pub fn grandpa_log(log: ConsensusLog<u64>) -> DigestItem {
	DigestItem::Consensus(GRANDPA_ENGINE_ID, log.encode())
}

pub fn to_authorities(vec: Vec<(u64, u64)>) -> AuthorityList {
	vec.into_iter()
		.map(|(id, weight)| (UintAuthorityId(id).to_public_key::<AuthorityId>(), weight))
		.collect()
}

pub fn extract_keyring(id: &AuthorityId) -> Ed25519Keyring {
	let mut raw_public = [0; 32];
	raw_public.copy_from_slice(id.as_ref());
	Ed25519Keyring::from_raw_public(raw_public).unwrap()
}

pub fn new_test_ext(vec: Vec<(u64, u64)>) -> sp_io::TestExternalities {
	new_test_ext_raw_authorities(to_authorities(vec))
}

pub fn new_test_ext_raw_authorities(authorities: AuthorityList) -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();

	let balances: Vec<_> = (0..authorities.len()).map(|i| (i as u64, 10_000_000)).collect();

	pallet_balances::GenesisConfig::<Test> { balances }
		.assimilate_storage(&mut t)
		.unwrap();

	// stashes are the index.
	let session_keys: Vec<_> = authorities
		.iter()
		.enumerate()
		.map(|(i, (k, _))| {
			(
				i as u64,
				i as u64,
				TestSessionKeys { grandpa_authority: AuthorityId::from(k.clone()) },
			)
		})
		.collect();

	// NOTE: this will initialize the grandpa authorities
	// through OneSessionHandler::on_genesis_session
	pallet_session::GenesisConfig::<Test> { keys: session_keys }
		.assimilate_storage(&mut t)
		.unwrap();

	// controllers are the same as stash
	let stakers: Vec<_> = (0..authorities.len())
		.map(|i| (i as u64, i as u64, 10_000, pallet_staking::StakerStatus::<u64>::Validator))
		.collect();

	let staking_config = pallet_staking::GenesisConfig::<Test> {
		stakers,
		validator_count: 8,
		force_era: pallet_staking::Forcing::ForceNew,
		minimum_validator_count: 0,
		invulnerables: vec![],
		..Default::default()
	};

	staking_config.assimilate_storage(&mut t).unwrap();

	t.into()
}

pub fn start_session(session_index: SessionIndex) {
	for i in Session::current_index()..session_index {
		System::on_finalize(System::block_number());
		Session::on_finalize(System::block_number());
		Staking::on_finalize(System::block_number());
		Grandpa::on_finalize(System::block_number());

		let parent_hash = if System::block_number() > 1 {
			let hdr = System::finalize();
			hdr.hash()
		} else {
			System::parent_hash()
		};

		System::reset_events();
		System::initialize(&(i as u64 + 1), &parent_hash, &Default::default());
		System::set_block_number((i + 1).into());
		Timestamp::set_timestamp(System::block_number() * 6000);

		System::on_initialize(System::block_number());
		Session::on_initialize(System::block_number());
		Staking::on_initialize(System::block_number());
		Grandpa::on_initialize(System::block_number());
	}

	assert_eq!(Session::current_index(), session_index);
}

pub fn start_era(era_index: EraIndex) {
	start_session((era_index * 3).into());
	assert_eq!(Staking::current_era(), Some(era_index));
}

pub fn initialize_block(number: u64, parent_hash: H256) {
	System::reset_events();
	System::initialize(&number, &parent_hash, &Default::default());
}

pub fn generate_equivocation_proof(
	set_id: SetId,
	vote1: (RoundNumber, H256, u64, &Ed25519Keyring),
	vote2: (RoundNumber, H256, u64, &Ed25519Keyring),
) -> sp_consensus_grandpa::EquivocationProof<H256, u64> {
	let signed_prevote = |round, hash, number, keyring: &Ed25519Keyring| {
		let prevote = finality_grandpa::Prevote { target_hash: hash, target_number: number };

		let prevote_msg = finality_grandpa::Message::Prevote(prevote.clone());
		let payload = sp_consensus_grandpa::localized_payload(round, set_id, &prevote_msg);
		let signed = keyring.sign(&payload).into();
		(prevote, signed)
	};

	let (prevote1, signed1) = signed_prevote(vote1.0, vote1.1, vote1.2, vote1.3);
	let (prevote2, signed2) = signed_prevote(vote2.0, vote2.1, vote2.2, vote2.3);

	sp_consensus_grandpa::EquivocationProof::new(
		set_id,
		sp_consensus_grandpa::Equivocation::Prevote(finality_grandpa::Equivocation {
			round_number: vote1.0,
			identity: vote1.3.public().into(),
			first: (prevote1, signed1),
			second: (prevote2, signed2),
		}),
	)
}
