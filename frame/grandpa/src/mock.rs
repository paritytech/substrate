// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

#![cfg(test)]

use crate::{
	equivocation::ValidateEquivocationReport, AuthorityId, AuthorityList, Call as GrandpaCall,
	ConsensusLog, Module, Trait,
};
use ::grandpa as finality_grandpa;
use codec::Encode;
use frame_support::{
	impl_outer_dispatch, impl_outer_event, impl_outer_origin, parameter_types,
	traits::{KeyOwnerProofSystem, OnFinalize, OnInitialize},
	weights::{DispatchInfo, Weight},
};
use pallet_staking::EraIndex;
use sp_core::{crypto::KeyTypeId, H256};
use sp_finality_grandpa::{RoundNumber, SetId, GRANDPA_ENGINE_ID};
use sp_io;
use sp_keyring::Ed25519Keyring;
use sp_runtime::{
	curve::PiecewiseLinear,
	impl_opaque_keys,
	testing::{Header, TestXt, UintAuthorityId},
	traits::{
		Convert, Extrinsic as ExtrinsicT, Header as _, IdentityLookup, OpaqueKeys,
		SaturatedConversion, SignedExtension,
	},
	transaction_validity::TransactionValidityError,
	DigestItem, Perbill,
};
use sp_staking::SessionIndex;

use frame_system as system;
use pallet_balances as balances;
use pallet_offences as offences;
use pallet_session as session;
use pallet_staking as staking;
use pallet_timestamp as timestamp;

impl_outer_origin! {
	pub enum Origin for Test {}
}

impl_outer_dispatch! {
	pub enum Call for Test where origin: Origin {
		grandpa::Grandpa,
		staking::Staking,
	}
}

impl_opaque_keys! {
	pub struct TestSessionKeys {
		pub grandpa_authority: super::Module<Test>,
	}
}

impl_outer_event! {
	pub enum TestEvent for Test {
		system<T>,
		balances<T>,
		grandpa,
		offences,
		session,
		staking<T>,
	}
}

#[derive(Clone, Eq, PartialEq)]
pub struct Test;

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}

impl frame_system::Trait for Test {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = Call;
	type Hash = H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = TestEvent;
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type DbWeight = ();
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = balances::AccountData<u128>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
}

impl<C> system::offchain::SendTransactionTypes<C> for Test
where
	Call: From<C>,
{
	type OverarchingCall = Call;
	type Extrinsic = TestXt<Call, ()>;
}

parameter_types! {
	pub const Period: u64 = 1;
	pub const Offset: u64 = 0;
	pub const DisabledValidatorsThreshold: Perbill = Perbill::from_percent(17);
}

/// Custom `SessionHandler` since we use `TestSessionKeys` as `Keys`.
impl session::Trait for Test {
	type Event = TestEvent;
	type ValidatorId = u64;
	type ValidatorIdOf = staking::StashOf<Self>;
	type ShouldEndSession = session::PeriodicSessions<Period, Offset>;
	type NextSessionRotation = session::PeriodicSessions<Period, Offset>;
	type SessionManager = session::historical::NoteHistoricalRoot<Self, Staking>;
	type SessionHandler = <TestSessionKeys as OpaqueKeys>::KeyTypeIdProviders;
	type Keys = TestSessionKeys;
	type DisabledValidatorsThreshold = DisabledValidatorsThreshold;
}

impl session::historical::Trait for Test {
	type FullIdentification = staking::Exposure<u64, u128>;
	type FullIdentificationOf = staking::ExposureOf<Self>;
}

parameter_types! {
	pub const ExistentialDeposit: u128 = 1;
}

impl balances::Trait for Test {
	type Balance = u128;
	type DustRemoval = ();
	type Event = TestEvent;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
}

parameter_types! {
	pub const MinimumPeriod: u64 = 3;
}

impl timestamp::Trait for Test {
	type Moment = u64;
	type OnTimestampSet = ();
	type MinimumPeriod = MinimumPeriod;
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
	pub const SlashDeferDuration: EraIndex = 0;
	pub const AttestationPeriod: u64 = 100;
	pub const RewardCurve: &'static PiecewiseLinear<'static> = &REWARD_CURVE;
	pub const MaxNominatorRewardedPerValidator: u32 = 64;
	pub const ElectionLookahead: u64 = 0;
	pub const StakingUnsignedPriority: u64 = u64::max_value() / 2;
}

pub struct CurrencyToVoteHandler;

impl Convert<u128, u128> for CurrencyToVoteHandler {
	fn convert(x: u128) -> u128 {
		x
	}
}

impl Convert<u128, u64> for CurrencyToVoteHandler {
	fn convert(x: u128) -> u64 {
		x.saturated_into()
	}
}

impl staking::Trait for Test {
	type RewardRemainder = ();
	type CurrencyToVote = CurrencyToVoteHandler;
	type Event = TestEvent;
	type Currency = Balances;
	type Slash = ();
	type Reward = ();
	type SessionsPerEra = SessionsPerEra;
	type BondingDuration = BondingDuration;
	type SlashDeferDuration = SlashDeferDuration;
	type SlashCancelOrigin = system::EnsureRoot<Self::AccountId>;
	type SessionInterface = Self;
	type UnixTime = timestamp::Module<Test>;
	type RewardCurve = RewardCurve;
	type MaxNominatorRewardedPerValidator = MaxNominatorRewardedPerValidator;
	type NextNewSession = Session;
	type ElectionLookahead = ElectionLookahead;
	type Call = Call;
	type UnsignedPriority = StakingUnsignedPriority;
	type MaxIterations = ();
}

impl offences::Trait for Test {
	type Event = TestEvent;
	type IdentificationTuple = session::historical::IdentificationTuple<Self>;
	type OnOffenceHandler = Staking;
}

impl Trait for Test {
	type Event = TestEvent;
	type Call = Call;

	type KeyOwnerProofSystem = Historical;

	type KeyOwnerProof =
		<Self::KeyOwnerProofSystem as KeyOwnerProofSystem<(KeyTypeId, AuthorityId)>>::Proof;

	type KeyOwnerIdentification = <Self::KeyOwnerProofSystem as KeyOwnerProofSystem<(
		KeyTypeId,
		AuthorityId,
	)>>::IdentificationTuple;

	type HandleEquivocation = super::EquivocationHandler<
		Self::KeyOwnerIdentification,
		reporting_keys::ReporterAppCrypto,
		Test,
		Offences,
	>;
}

pub mod reporting_keys {
	use sp_core::crypto::KeyTypeId;

	pub const KEY_TYPE: KeyTypeId = KeyTypeId(*b"test");

	mod app {
		use sp_application_crypto::{app_crypto, ed25519};
		app_crypto!(ed25519, super::KEY_TYPE);

		impl sp_runtime::traits::IdentifyAccount for Public {
			type AccountId = u64;
			fn into_account(self) -> Self::AccountId {
				super::super::Grandpa::grandpa_authorities()
					.iter()
					.map(|(k, _)| k)
					.position(|b| *b == self.0.clone().into())
					.unwrap() as u64
			}
		}
	}

	pub type ReporterId = app::Public;

	pub struct ReporterAppCrypto;
	impl frame_system::offchain::AppCrypto<ReporterId, sp_core::ed25519::Signature>
		for ReporterAppCrypto
	{
		type RuntimeAppPublic = ReporterId;
		type GenericSignature = sp_core::ed25519::Signature;
		type GenericPublic = sp_core::ed25519::Public;
	}
}

type Extrinsic = TestXt<Call, ()>;

impl<LocalCall> system::offchain::CreateSignedTransaction<LocalCall> for Test
where
	Call: From<LocalCall>,
{
	fn create_transaction<C: system::offchain::AppCrypto<Self::Public, Self::Signature>>(
		call: Call,
		_public: reporting_keys::ReporterId,
		_account: <Test as system::Trait>::AccountId,
		nonce: <Test as system::Trait>::Index,
	) -> Option<(Call, <Extrinsic as ExtrinsicT>::SignaturePayload)> {
		Some((call, (nonce, ())))
	}
}

impl frame_system::offchain::SigningTypes for Test {
	type Public = reporting_keys::ReporterId;
	type Signature = sp_core::ed25519::Signature;
}

mod grandpa {
	pub use crate::Event;
}

pub type Balances = pallet_balances::Module<Test>;
pub type Historical = pallet_session::historical::Module<Test>;
pub type Offences = pallet_offences::Module<Test>;
pub type Session = pallet_session::Module<Test>;
pub type Staking = pallet_staking::Module<Test>;
pub type System = frame_system::Module<Test>;
pub type Timestamp = pallet_timestamp::Module<Test>;
pub type Grandpa = Module<Test>;

pub fn grandpa_log(log: ConsensusLog<u64>) -> DigestItem<H256> {
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
	let mut t = frame_system::GenesisConfig::default()
		.build_storage::<Test>()
		.unwrap();

	// stashes are the index.
	let session_keys: Vec<_> = authorities
		.iter()
		.enumerate()
		.map(|(i, (k, _))| {
			(
				i as u64,
				i as u64,
				TestSessionKeys {
					grandpa_authority: AuthorityId::from(k.clone()),
				},
			)
		})
		.collect();

	// controllers are the index + 1000
	let stakers: Vec<_> = (0..authorities.len())
		.map(|i| {
			(
				i as u64,
				i as u64 + 1000,
				10_000,
				staking::StakerStatus::<u64>::Validator,
			)
		})
		.collect();

	let balances: Vec<_> = (0..authorities.len())
		.map(|i| (i as u64, 10_000_000))
		.collect();

	// NOTE: this will initialize the grandpa authorities
	// through OneSessionHandler::on_genesis_session
	session::GenesisConfig::<Test> { keys: session_keys }
		.assimilate_storage(&mut t)
		.unwrap();

	balances::GenesisConfig::<Test> { balances }
		.assimilate_storage(&mut t)
		.unwrap();

	let staking_config = staking::GenesisConfig::<Test> {
		stakers,
		validator_count: 8,
		force_era: staking::Forcing::ForceNew,
		minimum_validator_count: 0,
		invulnerables: vec![],
		..Default::default()
	};

	staking_config.assimilate_storage(&mut t).unwrap();

	t.into()
}

pub fn start_session(session_index: SessionIndex) {
	let mut parent_hash = System::parent_hash();

	for i in Session::current_index()..session_index {
		Staking::on_finalize(System::block_number());
		System::set_block_number((i + 1).into());
		Timestamp::set_timestamp(System::block_number() * 6000);

		// In order to be able to use `System::parent_hash()` in the tests
		// we need to first get it via `System::finalize` and then set it
		// the `System::initialize`. However, it is needed to be taken into
		// consideration that finalizing will prune some data in `System`
		// storage including old values `BlockHash` if that reaches above
		// `BlockHashCount` capacity.
		if System::block_number() > 1 {
			let hdr = System::finalize();
			parent_hash = hdr.hash();
		}

		System::initialize(
			&(i as u64 + 1),
			&parent_hash,
			&Default::default(),
			&Default::default(),
			Default::default(),
		);

		Session::on_initialize(System::block_number());
		System::on_initialize(System::block_number());
	}

	assert_eq!(Session::current_index(), session_index);
}

pub fn start_era(era_index: EraIndex) {
	start_session((era_index * 3).into());
	assert_eq!(Staking::current_era(), Some(era_index));
}

pub fn initialize_block(number: u64, parent_hash: H256) {
	System::initialize(
		&number,
		&parent_hash,
		&Default::default(),
		&Default::default(),
		Default::default(),
	);
}

pub fn report_equivocation(
	equivocation_proof: sp_finality_grandpa::EquivocationProof<H256, u64>,
	key_owner_proof: sp_session::MembershipProof,
) -> Result<GrandpaCall<Test>, TransactionValidityError> {
	let inner = GrandpaCall::report_equivocation(equivocation_proof, key_owner_proof);
	let call = Call::Grandpa(inner.clone());

	ValidateEquivocationReport::<Test>::new().validate(&0, &call, &DispatchInfo::default(), 0)?;

	Ok(inner)
}

pub fn generate_equivocation_proof(
	set_id: SetId,
	vote1: (RoundNumber, H256, u64, &Ed25519Keyring),
	vote2: (RoundNumber, H256, u64, &Ed25519Keyring),
) -> sp_finality_grandpa::EquivocationProof<H256, u64> {
	let signed_prevote = |round, hash, number, keyring: &Ed25519Keyring| {
		let prevote = finality_grandpa::Prevote {
			target_hash: hash,
			target_number: number,
		};

		let prevote_msg = finality_grandpa::Message::Prevote(prevote.clone());
		let payload = sp_finality_grandpa::localized_payload(round, set_id, &prevote_msg);
		let signed = keyring.sign(&payload).into();
		(prevote, signed)
	};

	let (prevote1, signed1) = signed_prevote(vote1.0, vote1.1, vote1.2, vote1.3);
	let (prevote2, signed2) = signed_prevote(vote2.0, vote2.1, vote2.2, vote2.3);

	sp_finality_grandpa::EquivocationProof::new(
		set_id,
		sp_finality_grandpa::Equivocation::Prevote(finality_grandpa::Equivocation {
			round_number: vote1.0,
			identity: vote1.3.public().into(),
			first: (prevote1, signed1),
			second: (prevote2, signed2),
		}),
	)
}
