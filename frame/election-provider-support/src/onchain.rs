// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use crate::{ElectionDataProvider, ElectionProvider, InstantElectionProvider, NposSolver};
use frame_support::{traits::Get, weights::DispatchClass};
use sp_npos_elections::*;
use sp_std::{collections::btree_map::BTreeMap, marker::PhantomData, prelude::*};

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

/// A simple on-chain implementation of the election provider trait.
///
/// This will accept voting data on the fly and produce the results immediately.
///
/// ### Warning
///
/// This can be very expensive to run frequently on-chain. Use with care. Moreover, this
/// implementation ignores the additional data of the election data provider and gives no insight on
/// how much weight was consumed.
///
/// Finally, the [`ElectionProvider`] implementation of this type does not impose any limits on the
/// number of voters and targets that are fetched. This could potentially make this unsuitable for
/// execution onchain. On the other hand, the [`InstantElectionProvider`] implementation does limit
/// these inputs.
///
/// It is advisable to use the former ([`ElectionProvider::elect`]) only at genesis, or for testing,
/// the latter [`InstantElectionProvider::instant_elect`] for onchain operations, with thoughtful
/// bounds.
///
/// Please use `BoundedOnchainExecution` at all times except at genesis or for testing,
/// with thoughtful bounds in order to bound the potential execution time.
/// Only use `UnboundedOnchainExecution` at genesis or for testing, as it does not
/// bound the inputs.
pub struct BoundedOnchainExecution<T: BoundedExecutionConfig>(PhantomData<T>);

#[cfg_attr(not(feature = "std"), deprecated(note = "use `BoundedOnchainExecution` instead"))]
pub struct UnboundedOnchainExecution<T: ExecutionConfig>(PhantomData<T>);

/// Configuration trait of [`UnboundedOnchainExecution`]Ì.
pub trait ExecutionConfig {
	/// This is to enable to register extra weight
	type System: frame_system::Config;
	/// `NposSolver` that should be used, an example would be `PhragMMS`.
	type Solver: NposSolver<
		AccountId = <Self::System as frame_system::Config>::AccountId,
		Error = sp_npos_elections::Error,
	>;
	/// Something that provides the data for election.
	type DataProvider: ElectionDataProvider<
		AccountId = <Self::System as frame_system::Config>::AccountId,
		BlockNumber = <Self::System as frame_system::Config>::BlockNumber,
	>;
}

/// Configuration trait of [`BoundedOnchainExecution`].
pub trait BoundedExecutionConfig: ExecutionConfig {
	/// Bounds the number of voters.
	type VotersBound: Get<u32>;
	/// Bounds the number of targets.
	type TargetsBound: Get<u32>;
}

fn elect_with<T: ExecutionConfig>(
	maybe_max_voters: Option<usize>,
	maybe_max_targets: Option<usize>,
) -> Result<Supports<<T::System as frame_system::Config>::AccountId>, Error> {
	let voters = T::DataProvider::electing_voters(maybe_max_voters).map_err(Error::DataProvider)?;
	let targets =
		T::DataProvider::electable_targets(maybe_max_targets).map_err(Error::DataProvider)?;
	let desired_targets = T::DataProvider::desired_targets().map_err(Error::DataProvider)?;

	let stake_map: BTreeMap<_, _> = voters
		.iter()
		.map(|(validator, vote_weight, _)| (validator.clone(), *vote_weight))
		.collect();

	let stake_of = |w: &<T::System as frame_system::Config>::AccountId| -> VoteWeight {
		stake_map.get(w).cloned().unwrap_or_default()
	};

	let ElectionResult { winners: _, assignments } =
		T::Solver::solve(desired_targets as usize, targets, voters).map_err(Error::from)?;

	let staked = assignment_ratio_to_staked_normalized(assignments, &stake_of)?;

	let weight = <T::System as frame_system::Config>::BlockWeights::get().max_block;
	frame_system::Pallet::<T::System>::register_extra_weight_unchecked(
		weight,
		DispatchClass::Mandatory,
	);

	Ok(to_supports(&staked))
}

impl<T: ExecutionConfig> ElectionProvider for UnboundedOnchainExecution<T> {
	type AccountId = <T::System as frame_system::Config>::AccountId;
	type BlockNumber = <T::System as frame_system::Config>::BlockNumber;
	type Error = Error;
	type DataProvider = T::DataProvider;

	fn elect() -> Result<Supports<<T::System as frame_system::Config>::AccountId>, Self::Error> {
		elect_with::<T>(None, None)
	}
}

impl<T: ExecutionConfig> InstantElectionProvider for UnboundedOnchainExecution<T> {
	fn instant_elect(
		maybe_max_voters: Option<usize>,
		maybe_max_targets: Option<usize>,
	) -> Result<Supports<Self::AccountId>, Self::Error> {
		elect_with::<T>(maybe_max_voters, maybe_max_targets)
	}
}

impl<T: BoundedExecutionConfig> ElectionProvider for BoundedOnchainExecution<T> {
	type AccountId = <T::System as frame_system::Config>::AccountId;
	type BlockNumber = <T::System as frame_system::Config>::BlockNumber;
	type Error = Error;
	type DataProvider = T::DataProvider;

	fn elect() -> Result<Supports<<T::System as frame_system::Config>::AccountId>, Self::Error> {
		elect_with::<T>(
			Some(T::VotersBound::get().try_into().unwrap_or(0)),
			Some(T::TargetsBound::get().try_into().unwrap_or(0)),
		)
	}
}

impl<T: BoundedExecutionConfig> InstantElectionProvider for BoundedOnchainExecution<T> {
	fn instant_elect(
		maybe_max_voters: Option<usize>,
		maybe_max_targets: Option<usize>,
	) -> Result<Supports<Self::AccountId>, Self::Error> {
		elect_with::<T>(
			Some(maybe_max_voters.unwrap_or(0).max(T::VotersBound::get().try_into().unwrap_or(0))),
			Some(
				maybe_max_targets
					.unwrap_or(0)
					.max(T::TargetsBound::get().try_into().unwrap_or(0)),
			),
		)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
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

	impl ExecutionConfig for Runtime {
		type System = Self;
		type Solver = crate::SequentialPhragmen<AccountId, Perbill>;
		type DataProvider = mock_data_provider::DataProvider;
	}

	type OnChainPhragmen = UnboundedOnchainExecution<Runtime>;

	mod mock_data_provider {
		use frame_support::{bounded_vec, traits::ConstU32};

		use super::*;
		use crate::{data_provider, VoterOf};

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
