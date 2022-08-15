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

//! # Sudo Offences Pallet
//! Pallet that allows the root to create an offence.

#![cfg_attr(not(feature = "std"), no_std)]

use pallet_session::historical::IdentificationTuple;
use pallet_staking::{BalanceOf, Exposure, ExposureOf, Pallet as Staking};
use sp_runtime::{traits::Convert, Perbill};
use sp_staking::offence::{DisableStrategy, OffenceDetails, OnOffenceHandler};

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config + pallet_staking::Config {
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		RootCreatedOffence { offenders: Vec<(T::AccountId, Perbill)> },
	}

	#[pallet::error]
	pub enum Error<T> {
		FailedToGetActiveEra,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T>
	where
		T: pallet_session::Config<ValidatorId = <T as frame_system::Config>::AccountId>,
		T: pallet_session::historical::Config<
			FullIdentification = Exposure<<T as frame_system::Config>::AccountId, BalanceOf<T>>,
			FullIdentificationOf = ExposureOf<T>,
		>,
		T::ValidatorIdOf: Convert<
			<T as frame_system::Config>::AccountId,
			Option<<T as frame_system::Config>::AccountId>,
		>,
	{
		/// Allows the `root` to create an offence.
		#[pallet::weight(10_000)]
		pub fn create_offence(
			origin: OriginFor<T>,
			offenders: Vec<(T::AccountId, Perbill)>,
		) -> DispatchResult {
			ensure_root(origin)?;

			let slash_fraction = offenders
				.clone()
				.into_iter()
				.map(|(_, fraction)| fraction)
				.collect::<Vec<Perbill>>();

			let offence_details = Self::get_offence_details(offenders.clone())?;

			Self::submit_offence(&offence_details, &slash_fraction);

			Self::deposit_event(Event::RootCreatedOffence { offenders });
			Ok(())
		}
	}

	impl<T: Config> Pallet<T>
	where
		T: pallet_session::Config<ValidatorId = <T as frame_system::Config>::AccountId>,
		T: pallet_session::historical::Config<
			FullIdentification = Exposure<<T as frame_system::Config>::AccountId, BalanceOf<T>>,
			FullIdentificationOf = ExposureOf<T>,
		>,
	{
		fn submit_offence(
			offenders: &[OffenceDetails<T::AccountId, IdentificationTuple<T>>],
			slash_fraction: &[Perbill],
		) {
			let session_index = <pallet_session::Pallet<T> as frame_support::traits::ValidatorSet<T::AccountId>>::session_index();

			<pallet_staking::Pallet<T> as OnOffenceHandler<
				T::AccountId,
				IdentificationTuple<T>,
				Weight,
			>>::on_offence(&offenders, &slash_fraction, session_index, DisableStrategy::WhenSlashed);
		}

		fn get_offence_details(
			offenders: Vec<(T::AccountId, Perbill)>,
		) -> Result<Vec<OffenceDetails<T::AccountId, IdentificationTuple<T>>>, DispatchError> {
			let active_era = Staking::<T>::active_era().ok_or(Error::<T>::FailedToGetActiveEra)?;
			let now = active_era.index;

			Ok(offenders
				.clone()
				.into_iter()
				.map(|(o, _)| OffenceDetails::<T::AccountId, IdentificationTuple<T>> {
					offender: (o.clone(), Staking::<T>::eras_stakers(now, o)),
					reporters: vec![],
				})
				.collect())
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate as root_offences;

	use frame_election_provider_support::{onchain, SequentialPhragmen};
	use frame_support::{
		assert_err, parameter_types,
		traits::{ConstU32, ConstU64},
	};
	use pallet_session::TestSessionHandler;
	use sp_core::H256;
	use sp_runtime::{
		curve::PiecewiseLinear,
		testing::Header,
		traits::{BlakeTwo256, IdentityLookup},
	};

	type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
	type Block = frame_system::mocking::MockBlock<Test>;
	type AccountId = u64;
	type Balance = u64;
	type BlockNumber = u64;

	frame_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
		{
			System: frame_system,
			Balances: pallet_balances,
			RootOffences: root_offences,
			Session: pallet_session,
			Staking: pallet_staking,
		}
	);

	parameter_types! {
		pub BlockWeights: frame_system::limits::BlockWeights =
			frame_system::limits::BlockWeights::simple_max(1024);
	}

	impl frame_system::Config for Test {
		type BaseCallFilter = frame_support::traits::Everything;
		type BlockWeights = ();
		type BlockLength = ();
		type DbWeight = ();
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Call = Call;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = Event;
		type BlockHashCount = ConstU64<250>;
		type Version = ();
		type PalletInfo = PalletInfo;
		type AccountData = pallet_balances::AccountData<u64>;
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
		type SS58Prefix = ();
		type OnSetCode = ();
		type MaxConsumers = ConstU32<16>;
	}

	impl pallet_balances::Config for Test {
		type MaxLocks = ();
		type MaxReserves = ();
		type ReserveIdentifier = [u8; 8];
		type Balance = Balance;
		type Event = Event;
		type DustRemoval = ();
		type ExistentialDeposit = ConstU64<1>;
		type AccountStore = System;
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

	pub struct OnChainSeqPhragmen;
	impl onchain::Config for OnChainSeqPhragmen {
		type System = Test;
		type Solver = SequentialPhragmen<AccountId, Perbill>;
		type DataProvider = Staking;
		type WeightInfo = ();
	}
	parameter_types! {
		pub const RewardCurve: &'static PiecewiseLinear<'static> = &REWARD_CURVE;
		pub static Offset: BlockNumber = 0;
		pub const Period: BlockNumber = 1;
	}

	impl pallet_staking::Config for Test {
		type MaxNominations = ConstU32<16>;
		type Currency = Balances;
		type CurrencyBalance = <Self as pallet_balances::Config>::Balance;
		type UnixTime = pallet_timestamp::Pallet<Self>;
		type CurrencyToVote = frame_support::traits::SaturatingCurrencyToVote;
		type RewardRemainder = ();
		type Event = Event;
		type Slash = ();
		type Reward = ();
		type SessionsPerEra = ();
		type SlashDeferDuration = ();
		type SlashCancelOrigin = frame_system::EnsureRoot<Self::AccountId>;
		type BondingDuration = ();
		type SessionInterface = Self;
		type EraPayout = pallet_staking::ConvertCurve<RewardCurve>;
		type NextNewSession = Session;
		type MaxNominatorRewardedPerValidator = ConstU32<64>;
		type OffendingValidatorsThreshold = ();
		type ElectionProvider = onchain::UnboundedExecution<OnChainSeqPhragmen>;
		type GenesisElectionProvider = Self::ElectionProvider;
		type MaxUnlockingChunks = ConstU32<32>;
		type VoterList = pallet_staking::UseNominatorsAndValidatorsMap<Self>;
		type OnStakerSlash = ();
		type BenchmarkingConfig = pallet_staking::TestBenchmarkingConfig;
		type WeightInfo = ();
	}

	impl pallet_session::historical::Config for Test {
		type FullIdentification = pallet_staking::Exposure<AccountId, Balance>;
		type FullIdentificationOf = pallet_staking::ExposureOf<Test>;
	}

	sp_runtime::impl_opaque_keys! {
		pub struct SessionKeys {
			pub foo: sp_runtime::testing::UintAuthorityId,
		}
	}

	impl pallet_session::Config for Test {
		type SessionManager = pallet_session::historical::NoteHistoricalRoot<Test, Staking>;
		type Keys = SessionKeys;
		type ShouldEndSession = pallet_session::PeriodicSessions<Period, Offset>;
		type NextSessionRotation = pallet_session::PeriodicSessions<Period, Offset>;
		type SessionHandler = TestSessionHandler;
		type Event = Event;
		type ValidatorId = AccountId;
		type ValidatorIdOf = pallet_staking::StashOf<Test>;
		type WeightInfo = ();
	}

	impl pallet_timestamp::Config for Test {
		type Moment = u64;
		type OnTimestampSet = ();
		type MinimumPeriod = ConstU64<5>;
		type WeightInfo = ();
	}

	impl Config for Test {
		type Event = Event;
	}

	fn new_test_ext() -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		pallet_balances::GenesisConfig::<Test> { balances: vec![(1, 10), (2, 10)] }
			.assimilate_storage(&mut t)
			.unwrap();
		t.into()
	}

	#[test]
	fn create_offence_fails_given_signed_origin() {
		use sp_runtime::traits::BadOrigin;
		new_test_ext().execute_with(|| {
			let offenders = (&[]).to_vec();
			assert_err!(RootOffences::create_offence(Origin::signed(1), offenders), BadOrigin);
		})
	}
}
