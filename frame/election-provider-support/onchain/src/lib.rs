// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

//! An implementation of [`ElectionProvider`] that uses an `NposSolver` to do the election.
//!
//! A simple on-chain implementation of the election provider trait.
//!
//! This will accept voting data on the fly and produce the results immediately.
//!
//! Finally, the [`ElectionProvider`] implementation of this type does not impose any dynamic limits
//! on the number of voters and targets that are fetched. However, one can impose bounds on it by
//! using the `MaxVotes` and `MaxTargets` bounds in the `Config` trait.
//!
//! On the other hand, the [`InstantElectionProvider`] implementation does limit these inputs
//! dynamically. If you use `elect_with_bounds` along with `InstantElectionProvider`, the bound that
//! would be used is the minimum of the 2 bounds.
//!
//! It is advisable to use the former ([`ElectionProvider::elect`]) only at genesis, or for testing,
//! the latter [`InstantElectionProvider::elect_with_bounds`] for onchain operations, with
//! thoughtful bounds.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::alloc::collections::BTreeMap;
use frame_election_provider_support::{
	ElectionDataProvider, ElectionProvider, InstantElectionProvider, NposSolver, PhragMMS,
	SequentialPhragmen,
};
use frame_support::{
	pallet_prelude::PhantomData,
	traits::Get,
	weights::{DispatchClass, Weight},
};
use sp_npos_elections::{
	assignment_ratio_to_staked_normalized, to_supports, ElectionResult, Supports, VoteWeight,
};

mod benchmarking;
#[cfg(feature = "runtime-benchmarks")]
pub use benchmarking::{set_up_data_provider, SEED};

pub mod weights;
pub use weights::WeightInfo;

/// `OnChainPhragmen` is a simple implementation of the `ElectionProvider` and
/// `InstantElectionProvider` traits, that uses the `SequentialPhragmen` algorithm to solve for the
/// solution.
pub type OnChainPhragmen<T, Accuracy, Balancing = ()> = BoundedExecution<
	T,
	SequentialPhragmen<<T as frame_system::Config>::AccountId, Accuracy, Balancing>,
>;

/// Similar to `OnChainPhragmen`, but uses the `PhragMMS` algorithm to solve for the solution.
pub type OnChainPhragMMS<T, Accuracy, Balancing = ()> =
	BoundedExecution<T, PhragMMS<<T as frame_system::Config>::AccountId, Accuracy, Balancing>>;

/// Errors of the on-chain election.
#[derive(Eq, PartialEq, Debug)]
pub enum Error {
	/// An internal error in the NPoS elections crate.
	NposElections(sp_npos_elections::Error),
	/// Errors from the data provider.
	DataProvider(&'static str),
}

impl From<sp_npos_elections::Error> for Error {
	fn from(e: sp_npos_elections::Error) -> Self {
		Error::NposElections(e)
	}
}

/// Configuration for the benchmarks of the pallet.
pub trait BenchmarkingConfig {
	/// Range of voters.
	const VOTERS: [u32; 2];
	/// Range of targets.
	const TARGETS: [u32; 2];
	/// Range of number of votes per voter.
	const VOTES_PER_VOTER: [u32; 2];
}

// Default values for ease.
impl BenchmarkingConfig for () {
	const VOTERS: [u32; 2] = [400, 600];
	const TARGETS: [u32; 2] = [200, 400];
	const VOTES_PER_VOTER: [u32; 2] = [1, 2];
}

/// Configuration for the weight measuring function of the `NposSolver`.
pub trait WeightConfig {
	fn weight<T: Config>(v: u32, t: u32, d: u32) -> Weight;
}

impl<AccountId, Accuracy, Balancing> WeightConfig
	for SequentialPhragmen<AccountId, Accuracy, Balancing>
{
	fn weight<T: Config>(v: u32, t: u32, d: u32) -> Weight {
		T::WeightInfo::phragmen(v, t, d)
	}
}

impl<AccountId, Accuracy, Balancing> WeightConfig for PhragMMS<AccountId, Accuracy, Balancing> {
	fn weight<T: Config>(v: u32, t: u32, d: u32) -> Weight {
		T::WeightInfo::phragmms(v, t, d)
	}
}

pub use pallet::*;
#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// Something that provides the data for election.
		type DataProvider: ElectionDataProvider<
			AccountId = Self::AccountId,
			BlockNumber = Self::BlockNumber,
		>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;

		/// Bounds the number of voters.
		type MaxVoters: Get<u32>;

		/// Bounds the number of targets.
		type MaxTargets: Get<u32>;

		/// The configuration of benchmarking.
		type BenchmarkingConfig: BenchmarkingConfig;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(PhantomData<T>);
}

/// `NposSolver` that should be used, an example would be `PhragMMS`.
/// It's advised to use the `OnChainPhragmen` or `OnChainPhragMMS` instead, as they implement the
/// `WeightConfig` trait.
pub struct BoundedExecution<
	T: Config,
	Solver: NposSolver<AccountId = T::AccountId, Error = sp_npos_elections::Error>,
>(PhantomData<(T, Solver)>);

impl<
		T: Config,
		Solver: NposSolver<AccountId = T::AccountId, Error = sp_npos_elections::Error> + WeightConfig,
	> BoundedExecution<T, Solver>
{
	fn elect_with(max_voters: usize, max_targets: usize) -> Result<Supports<T::AccountId>, Error> {
		let voters =
			T::DataProvider::electing_voters(Some(max_voters)).map_err(Error::DataProvider)?;
		let targets =
			T::DataProvider::electable_targets(Some(max_targets)).map_err(Error::DataProvider)?;
		let desired_targets = T::DataProvider::desired_targets().map_err(Error::DataProvider)?;

		let voters_len = voters.len() as u32;
		let targets_len = targets.len() as u32;

		let stake_map: BTreeMap<_, _> = voters
			.iter()
			.map(|(validator, vote_weight, _)| (validator.clone(), *vote_weight))
			.collect();

		let stake_of =
			|w: &T::AccountId| -> VoteWeight { stake_map.get(w).cloned().unwrap_or_default() };

		let ElectionResult { winners: _, assignments } =
			Solver::solve(desired_targets as usize, targets, voters).map_err(Error::from)?;

		let staked = assignment_ratio_to_staked_normalized(assignments, &stake_of)?;

		let weight = Solver::weight::<T>(
			voters_len,
			targets_len,
			<T::DataProvider as ElectionDataProvider>::MaxVotesPerVoter::get(),
		);
		frame_system::Pallet::<T>::register_extra_weight_unchecked(
			weight,
			DispatchClass::Mandatory,
		);

		Ok(to_supports(&staked))
	}
}

impl<
		T: Config,
		Solver: NposSolver<AccountId = T::AccountId, Error = sp_npos_elections::Error> + WeightConfig,
	> ElectionProvider for BoundedExecution<T, Solver>
{
	type AccountId = T::AccountId;
	type BlockNumber = T::BlockNumber;
	type Error = Error;
	type DataProvider = T::DataProvider;

	fn elect() -> Result<Supports<T::AccountId>, Self::Error> {
		Self::elect_with(T::MaxVoters::get() as usize, T::MaxTargets::get() as usize)
	}
}

impl<
		T: Config,
		Solver: NposSolver<AccountId = T::AccountId, Error = sp_npos_elections::Error> + WeightConfig,
	> InstantElectionProvider for BoundedExecution<T, Solver>
{
	fn elect_with_bounds(
		max_voters: usize,
		max_targets: usize,
	) -> Result<Supports<Self::AccountId>, Self::Error> {
		Self::elect_with(
			max_voters.min(T::MaxVoters::get() as usize),
			max_targets.min(T::MaxTargets::get() as usize),
		)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use frame_support::traits::ConstU32;
	use sp_npos_elections::Support;
	type AccountId = u64;
	type BlockNumber = u64;

	pub type Header = sp_runtime::generic::Header<BlockNumber, sp_runtime::traits::BlakeTwo256>;
	pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<AccountId, (), (), ()>;
	pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;

	frame_support::construct_runtime!(
		pub enum Runtime where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic
		{
			System: frame_system::{Pallet, Call, Event<T>},
		}
	);

	impl frame_system::Config for Runtime {
		type SS58Prefix = ();
		type BaseCallFilter = frame_support::traits::Everything;
		type Origin = Origin;
		type Index = AccountId;
		type BlockNumber = BlockNumber;
		type Call = Call;
		type Hash = sp_core::H256;
		type Hashing = sp_runtime::traits::BlakeTwo256;
		type AccountId = AccountId;
		type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
		type Header = sp_runtime::testing::Header;
		type Event = ();
		type BlockHashCount = ();
		type DbWeight = ();
		type BlockLength = ();
		type BlockWeights = ();
		type Version = ();
		type PalletInfo = PalletInfo;
		type AccountData = ();
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
		type OnSetCode = ();
		type MaxConsumers = ConstU32<16>;
	}

	pub struct ElectionProviderBenchmarkConfig;
	impl BenchmarkingConfig for ElectionProviderBenchmarkConfig {
		const VOTERS: [u32; 2] = [400, 600];
		const TARGETS: [u32; 2] = [200, 400];
		const VOTES_PER_VOTER: [u32; 2] = [1, 2];
	}

	impl Config for Runtime {
		type DataProvider = mock_data_provider::DataProvider;
		type MaxVoters = ConstU32<600>;
		type MaxTargets = ConstU32<400>;
		type BenchmarkingConfig = ElectionProviderBenchmarkConfig;
		type WeightInfo = ();
	}

	mod mock_data_provider {
		use frame_support::{bounded_vec, traits::ConstU32};

		use super::*;
		use frame_election_provider_support::{data_provider, VoterOf};

		pub struct DataProvider;
		impl ElectionDataProvider for DataProvider {
			type AccountId = AccountId;
			type BlockNumber = BlockNumber;
			type MaxVotesPerVoter = ConstU32<2>;
			fn electing_voters(_: Option<usize>) -> data_provider::Result<Vec<VoterOf<Self>>> {
				Ok(vec![
					(1, 10, bounded_vec![10, 20]),
					(2, 20, bounded_vec![30, 20]),
					(3, 30, bounded_vec![10, 30]),
				])
			}

			fn electable_targets(_: Option<usize>) -> data_provider::Result<Vec<AccountId>> {
				Ok(vec![10, 20, 30])
			}

			fn desired_targets() -> data_provider::Result<u32> {
				Ok(2)
			}

			fn next_election_prediction(_: BlockNumber) -> BlockNumber {
				0
			}
		}
	}

	#[test]
	fn onchain_seq_phragmen_works() {
		sp_io::TestExternalities::new_empty().execute_with(|| {
			assert_eq!(
				OnChainPhragmen::<Runtime, sp_runtime::Perbill>::elect().unwrap(),
				vec![
					(10, Support { total: 25, voters: vec![(1, 10), (3, 15)] }),
					(30, Support { total: 35, voters: vec![(2, 20), (3, 15)] })
				]
			);
		})
	}

	#[test]
	fn onchain_phragmms_works() {
		sp_io::TestExternalities::new_empty().execute_with(|| {
			assert_eq!(
				OnChainPhragMMS::<Runtime, sp_runtime::Perbill>::elect().unwrap(),
				vec![
					(10, Support { total: 25, voters: vec![(1, 10), (3, 15)] }),
					(30, Support { total: 35, voters: vec![(2, 20), (3, 15)] })
				]
			);
		})
	}
}
