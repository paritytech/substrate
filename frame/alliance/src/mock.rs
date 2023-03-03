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

pub use sp_core::H256;
use sp_runtime::traits::Hash;
pub use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
	BuildStorage,
};
use sp_std::convert::{TryFrom, TryInto};

pub use frame_support::{
	assert_noop, assert_ok, ord_parameter_types, parameter_types,
	traits::{EitherOfDiverse, GenesisBuild, SortedMembers},
	BoundedVec,
};
use frame_system::{EnsureRoot, EnsureSignedBy};
use pallet_identity::{Data, IdentityInfo, Judgement};

pub use crate as pallet_alliance;

use super::*;

type BlockNumber = u64;
type AccountId = u64;

parameter_types! {
	pub const BlockHashCount: BlockNumber = 250;
}
impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type Index = u64;
	type BlockNumber = BlockNumber;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = BlockHashCount;
	type DbWeight = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<AccountId>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
	pub const MaxLocks: u32 = 10;
}
impl pallet_balances::Config for Test {
	type Balance = u64;
	type DustRemoval = ();
	type RuntimeEvent = RuntimeEvent;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
	type MaxLocks = MaxLocks;
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
}

const MOTION_DURATION_IN_BLOCKS: BlockNumber = 3;

parameter_types! {
	pub const MotionDuration: BlockNumber = MOTION_DURATION_IN_BLOCKS;
	pub const MaxProposals: u32 = 100;
	pub const MaxMembers: u32 = 100;
}
type AllianceCollective = pallet_collective::Instance1;
impl pallet_collective::Config<AllianceCollective> for Test {
	type RuntimeOrigin = RuntimeOrigin;
	type Proposal = RuntimeCall;
	type RuntimeEvent = RuntimeEvent;
	type MotionDuration = MotionDuration;
	type MaxProposals = MaxProposals;
	type MaxMembers = MaxMembers;
	type DefaultVote = pallet_collective::PrimeDefaultVote;
	type WeightInfo = ();
	type SetMembersOrigin = EnsureRoot<Self::AccountId>;
}

parameter_types! {
	pub const BasicDeposit: u64 = 10;
	pub const FieldDeposit: u64 = 10;
	pub const SubAccountDeposit: u64 = 10;
	pub const MaxSubAccounts: u32 = 2;
	pub const MaxAdditionalFields: u32 = 2;
	pub const MaxRegistrars: u32 = 20;
}
ord_parameter_types! {
	pub const One: u64 = 1;
	pub const Two: u64 = 2;
	pub const Three: u64 = 3;
	pub const Four: u64 = 4;
	pub const Five: u64 = 5;
}
type EnsureOneOrRoot = EitherOfDiverse<EnsureRoot<AccountId>, EnsureSignedBy<One, AccountId>>;
type EnsureTwoOrRoot = EitherOfDiverse<EnsureRoot<AccountId>, EnsureSignedBy<Two, AccountId>>;

impl pallet_identity::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type Currency = Balances;
	type BasicDeposit = BasicDeposit;
	type FieldDeposit = FieldDeposit;
	type SubAccountDeposit = SubAccountDeposit;
	type MaxSubAccounts = MaxSubAccounts;
	type MaxAdditionalFields = MaxAdditionalFields;
	type MaxRegistrars = MaxRegistrars;
	type Slashed = ();
	type RegistrarOrigin = EnsureOneOrRoot;
	type ForceOrigin = EnsureTwoOrRoot;
	type WeightInfo = ();
}

pub struct AllianceIdentityVerifier;
impl IdentityVerifier<AccountId> for AllianceIdentityVerifier {
	fn has_identity(who: &AccountId, fields: u64) -> bool {
		Identity::has_identity(who, fields)
	}

	fn has_good_judgement(who: &AccountId) -> bool {
		if let Some(judgements) =
			Identity::identity(who).map(|registration| registration.judgements)
		{
			judgements
				.iter()
				.any(|(_, j)| matches!(j, Judgement::KnownGood | Judgement::Reasonable))
		} else {
			false
		}
	}

	fn super_account_id(who: &AccountId) -> Option<AccountId> {
		Identity::super_of(who).map(|parent| parent.0)
	}
}

pub struct AllianceProposalProvider;
impl ProposalProvider<AccountId, H256, RuntimeCall> for AllianceProposalProvider {
	fn propose_proposal(
		who: AccountId,
		threshold: u32,
		proposal: Box<RuntimeCall>,
		length_bound: u32,
	) -> Result<(u32, u32), DispatchError> {
		AllianceMotion::do_propose_proposed(who, threshold, proposal, length_bound)
	}

	fn vote_proposal(
		who: AccountId,
		proposal: H256,
		index: ProposalIndex,
		approve: bool,
	) -> Result<bool, DispatchError> {
		AllianceMotion::do_vote(who, proposal, index, approve)
	}

	fn close_proposal(
		proposal_hash: H256,
		proposal_index: ProposalIndex,
		proposal_weight_bound: Weight,
		length_bound: u32,
	) -> DispatchResultWithPostInfo {
		AllianceMotion::do_close(proposal_hash, proposal_index, proposal_weight_bound, length_bound)
	}

	fn proposal_of(proposal_hash: H256) -> Option<RuntimeCall> {
		AllianceMotion::proposal_of(proposal_hash)
	}
}

parameter_types! {
	pub const MaxFellows: u32 = MaxMembers::get();
	pub const MaxAllies: u32 = 100;
	pub const AllyDeposit: u64 = 25;
	pub const RetirementPeriod: BlockNumber = MOTION_DURATION_IN_BLOCKS + 1;
}
impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type Proposal = RuntimeCall;
	type AdminOrigin = EnsureSignedBy<One, AccountId>;
	type MembershipManager = EnsureSignedBy<Two, AccountId>;
	type AnnouncementOrigin = EnsureSignedBy<Three, AccountId>;
	type Currency = Balances;
	type Slashed = ();
	type InitializeMembers = AllianceMotion;
	type MembershipChanged = AllianceMotion;
	#[cfg(not(feature = "runtime-benchmarks"))]
	type IdentityVerifier = AllianceIdentityVerifier;
	#[cfg(feature = "runtime-benchmarks")]
	type IdentityVerifier = ();
	type ProposalProvider = AllianceProposalProvider;
	type MaxProposals = MaxProposals;
	type MaxFellows = MaxFellows;
	type MaxAllies = MaxAllies;
	type MaxUnscrupulousItems = ConstU32<100>;
	type MaxWebsiteUrlLength = ConstU32<255>;
	type MaxAnnouncementsCount = ConstU32<100>;
	type MaxMembersCount = MaxMembers;
	type AllyDeposit = AllyDeposit;
	type WeightInfo = ();
	type RetirementPeriod = RetirementPeriod;
}

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system,
		Balances: pallet_balances,
		Identity: pallet_identity,
		AllianceMotion: pallet_collective::<Instance1>,
		Alliance: pallet_alliance,
	}
);

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();

	pallet_balances::GenesisConfig::<Test> {
		balances: vec![
			(1, 50),
			(2, 50),
			(3, 50),
			(4, 50),
			(5, 30),
			(6, 50),
			(7, 50),
			(8, 50),
			(9, 50),
		],
	}
	.assimilate_storage(&mut t)
	.unwrap();

	GenesisBuild::<Test>::assimilate_storage(
		&pallet_alliance::GenesisConfig {
			fellows: vec![],
			allies: vec![],
			phantom: Default::default(),
		},
		&mut t,
	)
	.unwrap();

	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| {
		assert_ok!(Identity::add_registrar(RuntimeOrigin::signed(1), 1));

		let info = IdentityInfo {
			additional: BoundedVec::default(),
			display: Data::Raw(b"name".to_vec().try_into().unwrap()),
			legal: Data::default(),
			web: Data::Raw(b"website".to_vec().try_into().unwrap()),
			riot: Data::default(),
			email: Data::default(),
			pgp_fingerprint: None,
			image: Data::default(),
			twitter: Data::default(),
		};
		assert_ok!(Identity::set_identity(RuntimeOrigin::signed(1), Box::new(info.clone())));
		assert_ok!(Identity::provide_judgement(
			RuntimeOrigin::signed(1),
			0,
			1,
			Judgement::KnownGood,
			BlakeTwo256::hash_of(&info)
		));
		assert_ok!(Identity::set_identity(RuntimeOrigin::signed(2), Box::new(info.clone())));
		assert_ok!(Identity::provide_judgement(
			RuntimeOrigin::signed(1),
			0,
			2,
			Judgement::KnownGood,
			BlakeTwo256::hash_of(&info)
		));
		assert_ok!(Identity::set_identity(RuntimeOrigin::signed(3), Box::new(info.clone())));
		assert_ok!(Identity::provide_judgement(
			RuntimeOrigin::signed(1),
			0,
			3,
			Judgement::KnownGood,
			BlakeTwo256::hash_of(&info)
		));
		assert_ok!(Identity::set_identity(RuntimeOrigin::signed(4), Box::new(info.clone())));
		assert_ok!(Identity::provide_judgement(
			RuntimeOrigin::signed(1),
			0,
			4,
			Judgement::KnownGood,
			BlakeTwo256::hash_of(&info)
		));
		assert_ok!(Identity::set_identity(RuntimeOrigin::signed(5), Box::new(info.clone())));
		assert_ok!(Identity::provide_judgement(
			RuntimeOrigin::signed(1),
			0,
			5,
			Judgement::KnownGood,
			BlakeTwo256::hash_of(&info)
		));
		assert_ok!(Identity::set_identity(RuntimeOrigin::signed(6), Box::new(info.clone())));
		assert_ok!(Identity::set_identity(RuntimeOrigin::signed(8), Box::new(info.clone())));
		assert_ok!(Identity::provide_judgement(
			RuntimeOrigin::signed(1),
			0,
			8,
			Judgement::KnownGood,
			BlakeTwo256::hash_of(&info)
		));
		assert_ok!(Identity::set_identity(RuntimeOrigin::signed(9), Box::new(info.clone())));
		assert_ok!(Identity::provide_judgement(
			RuntimeOrigin::signed(1),
			0,
			9,
			Judgement::KnownGood,
			BlakeTwo256::hash_of(&info)
		));

		// Joining before init should fail.
		assert_noop!(
			Alliance::join_alliance(RuntimeOrigin::signed(1)),
			Error::<Test, ()>::AllianceNotYetInitialized
		);

		assert_ok!(Alliance::init_members(RuntimeOrigin::root(), vec![1, 2, 3], vec![]));

		System::set_block_number(1);
	});
	ext
}

#[cfg(feature = "runtime-benchmarks")]
pub fn new_bench_ext() -> sp_io::TestExternalities {
	GenesisConfig::default().build_storage().unwrap().into()
}

pub fn test_cid() -> Cid {
	let result = sp_core_hashing::sha2_256(b"hello world");
	Cid::new_v0(result)
}

pub fn make_remark_proposal(value: u64) -> (RuntimeCall, u32, H256) {
	make_proposal(RuntimeCall::System(frame_system::Call::remark { remark: value.encode() }))
}

pub fn make_kick_member_proposal(who: AccountId) -> (RuntimeCall, u32, H256) {
	make_proposal(RuntimeCall::Alliance(pallet_alliance::Call::kick_member { who }))
}

pub fn make_proposal(proposal: RuntimeCall) -> (RuntimeCall, u32, H256) {
	let len: u32 = proposal.using_encoded(|p| p.len() as u32);
	let hash = BlakeTwo256::hash_of(&proposal);
	(proposal, len, hash)
}

pub fn is_fellow(who: &AccountId) -> bool {
	Alliance::is_member_of(who, MemberRole::Fellow)
}
