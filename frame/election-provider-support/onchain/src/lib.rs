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

#![cfg_attr(not(feature = "std"), no_std)]

use codec::alloc::collections::BTreeMap;
use frame_election_provider_support::{
	ElectionDataProvider, ElectionProvider, InstantElectionProvider, NposSolver,
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

pub trait WeightInfo {
	fn phragmen() -> Weight;
	fn phragmms() -> Weight;
}

impl WeightInfo for () {
	fn phragmen() -> Weight {
		0
	}

	fn phragmms() -> Weight {
		0
	}
}

pub use pallet::*;
#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The weight of the pallet.
		type WeightInfo: WeightInfo;
		/// `NposSolver` that should be used, an example would be `PhragMMS`.
		type Solver: NposSolver<AccountId = Self::AccountId, Error = sp_npos_elections::Error>;
		/// Something that provides the data for election.
		type DataProvider: ElectionDataProvider<
			AccountId = Self::AccountId,
			BlockNumber = Self::BlockNumber,
		>;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(PhantomData<T>);
}

impl<T: Config> Pallet<T> {
	fn elect_with(
		maybe_max_voters: Option<usize>,
		maybe_max_targets: Option<usize>,
	) -> Result<Supports<T::AccountId>, Error> {
		let voters =
			T::DataProvider::electing_voters(maybe_max_voters).map_err(Error::DataProvider)?;
		let targets =
			T::DataProvider::electable_targets(maybe_max_targets).map_err(Error::DataProvider)?;
		let desired_targets = T::DataProvider::desired_targets().map_err(Error::DataProvider)?;

		let stake_map: BTreeMap<_, _> = voters
			.iter()
			.map(|(validator, vote_weight, _)| (validator.clone(), *vote_weight))
			.collect();

		let stake_of =
			|w: &T::AccountId| -> VoteWeight { stake_map.get(w).cloned().unwrap_or_default() };

		let ElectionResult { winners: _, assignments } =
			T::Solver::solve(desired_targets as usize, targets, voters).map_err(Error::from)?;

		let staked = assignment_ratio_to_staked_normalized(assignments, &stake_of)?;

		let weight = T::BlockWeights::get().max_block;
		frame_system::Pallet::<T>::register_extra_weight_unchecked(
			weight,
			DispatchClass::Mandatory,
		);

		Ok(to_supports(&staked))
	}
}

/// A simple on-chain implementation of the election provider trait.
///
/// This will accept voting data on the fly and produce the results immediately.
///
/// Finally, the [`ElectionProvider`] implementation of this type does not impose any limits on the
/// number of voters and targets that are fetched. This could potentially make this unsuitable for
/// execution onchain. One could, however, impose bounds on it by using for example
/// `BoundedExecution` which will the bounds provided in the configuration.
///
/// On the other hand, the [`InstantElectionProvider`] implementation does limit these inputs,
/// either via using `BoundedExecution` and imposing the bounds there, or dynamically via calling
/// `elect_with_bounds` providing these bounds. If you use `elect_with_bounds` along with
/// `InstantElectionProvider`, the bound that would be used is the minimum of the 2 bounds.
///
/// It is advisable to use the former ([`ElectionProvider::elect`]) only at genesis, or for testing,
/// the latter [`InstantElectionProvider::elect_with_bounds`] for onchain operations, with
/// thoughtful bounds.
///
/// Please use `BoundedExecution` at all times except at genesis or for testing, with thoughtful
/// bounds in order to bound the potential execution time. Limit the use `UnboundedExecution` at
/// genesis or for testing, as it does not bound the inputs. However, this can be used with
/// `[InstantElectionProvider::elect_with_bounds`] that dynamically imposes limits.
/// `VotersBound`: Bounds the number of voters.
/// `TargetsBound`: Bounds the number of targets.
pub struct BoundedExecution<T: Config, VotersBound: Get<u32>, TargetsBound: Get<u32>>(
	PhantomData<(T, VotersBound, TargetsBound)>,
);

/// An unbounded variant of [`BoundedExecution`].
///
/// ### Warning
///
/// This can be very expensive to run frequently on-chain. Use with care. Moreover, this
/// implementation ignores the additional data of the election data provider and gives no insight on
/// how much weight was consumed.
pub struct UnboundedExecution<T: Config>(PhantomData<T>);

impl<T: Config> ElectionProvider for UnboundedExecution<T> {
	type AccountId = T::AccountId;
	type BlockNumber = T::BlockNumber;
	type Error = Error;
	type DataProvider = T::DataProvider;

	fn elect() -> Result<Supports<T::AccountId>, Self::Error> {
		// This should not be called if not in `std` mode (and therefore neither in genesis nor in
		// testing)
		if cfg!(not(feature = "std")) {
			frame_support::log::error!(
				"Please use `InstantElectionProvider` instead to provide bounds on election if not in \
				genesis or testing mode"
			);
		}

		Pallet::<T>::elect_with(None, None)
	}
}

impl<T: Config> InstantElectionProvider for UnboundedExecution<T> {
	fn elect_with_bounds(
		max_voters: usize,
		max_targets: usize,
	) -> Result<Supports<Self::AccountId>, Self::Error> {
		Pallet::<T>::elect_with(Some(max_voters), Some(max_targets))
	}
}

impl<T: Config, VotersBound: Get<u32>, TargetsBound: Get<u32>> ElectionProvider
	for BoundedExecution<T, VotersBound, TargetsBound>
{
	type AccountId = T::AccountId;
	type BlockNumber = T::BlockNumber;
	type Error = Error;
	type DataProvider = T::DataProvider;

	fn elect() -> Result<Supports<T::AccountId>, Self::Error> {
		Pallet::<T>::elect_with(
			Some(VotersBound::get() as usize),
			Some(TargetsBound::get() as usize),
		)
	}
}

impl<T: Config, VotersBound: Get<u32>, TargetsBound: Get<u32>> InstantElectionProvider
	for BoundedExecution<T, VotersBound, TargetsBound>
{
	fn elect_with_bounds(
		max_voters: usize,
		max_targets: usize,
	) -> Result<Supports<Self::AccountId>, Self::Error> {
		Pallet::<T>::elect_with(
			Some(max_voters.min(VotersBound::get() as usize)),
			Some(max_targets.min(TargetsBound::get() as usize)),
		)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use frame_election_provider_support::SequentialPhragmen;
	use sp_npos_elections::Support;
	use sp_runtime::Perbill;
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
		type MaxConsumers = frame_support::traits::ConstU32<16>;
	}

	impl Config for Runtime {
		type Solver = SequentialPhragmen<AccountId, Perbill>;
		type DataProvider = mock_data_provider::DataProvider;
		type WeightInfo = ();
	}

	type OnChainPhragmen = UnboundedExecution<Runtime>;

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
				OnChainPhragmen::elect().unwrap(),
				vec![
					(10, Support { total: 25, voters: vec![(1, 10), (3, 15)] }),
					(30, Support { total: 35, voters: vec![(2, 20), (3, 15)] })
				]
			);
		})
	}
}
