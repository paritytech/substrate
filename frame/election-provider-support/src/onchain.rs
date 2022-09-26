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

//! An implementation of [`ElectionProvider`] that uses an `NposSolver` to do the election. As the
//! name suggests, this is meant to be used onchain. Given how heavy the calculations are, please be
//! careful when using it onchain.

use crate::{
	Debug, ElectionDataProvider, ElectionProvider, ElectionProviderBase, InstantElectionProvider,
	NposSolver, WeightInfo,
};
use frame_support::{dispatch::DispatchClass, traits::Get};
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
/// The [`ElectionProvider`] implementation of this type does not impose any dynamic limits on the
/// number of voters and targets that are fetched. This could potentially make this unsuitable for
/// execution onchain. One could, however, impose bounds on it by using `BoundedExecution` using the
/// `MaxVoters` and `MaxTargets` bonds in the `BoundedConfig` trait.
///
/// On the other hand, the [`InstantElectionProvider`] implementation does limit these inputs
/// dynamically. If you use `elect_with_bounds` along with `InstantElectionProvider`, the bound that
/// would be used is the minimum of the dynamic bounds given as arguments to `elect_with_bounds` and
/// the trait bounds (`MaxVoters` and `MaxTargets`).
///
/// Please use `BoundedExecution` at all times except at genesis or for testing, with thoughtful
/// bounds in order to bound the potential execution time. Limit the use `UnboundedExecution` at
/// genesis or for testing, as it does not bound the inputs. However, this can be used with
/// `[InstantElectionProvider::elect_with_bounds`] that dynamically imposes limits.
pub struct BoundedExecution<T: BoundedConfig>(PhantomData<T>);

/// An unbounded variant of [`BoundedExecution`].
///
/// ### Warning
///
/// This can be very expensive to run frequently on-chain. Use with care.
pub struct UnboundedExecution<T: Config>(PhantomData<T>);

/// Configuration trait for an onchain election execution.
pub trait Config {
	/// Needed for weight registration.
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
	/// Weight information for extrinsics in this pallet.
	type WeightInfo: WeightInfo;
}

pub trait BoundedConfig: Config {
	/// Bounds the number of voters.
	type VotersBound: Get<u32>;
	/// Bounds the number of targets.
	type TargetsBound: Get<u32>;
}

fn elect_with<T: Config>(
	maybe_max_voters: Option<usize>,
	maybe_max_targets: Option<usize>,
) -> Result<Supports<<T::System as frame_system::Config>::AccountId>, Error> {
	let voters = T::DataProvider::electing_voters(maybe_max_voters).map_err(Error::DataProvider)?;
	let targets =
		T::DataProvider::electable_targets(maybe_max_targets).map_err(Error::DataProvider)?;
	let desired_targets = T::DataProvider::desired_targets().map_err(Error::DataProvider)?;

	let voters_len = voters.len() as u32;
	let targets_len = targets.len() as u32;

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

	let weight = T::Solver::weight::<T::WeightInfo>(
		voters_len,
		targets_len,
		<T::DataProvider as ElectionDataProvider>::MaxVotesPerVoter::get(),
	);
	frame_system::Pallet::<T::System>::register_extra_weight_unchecked(
		weight,
		DispatchClass::Mandatory,
	);

	Ok(to_supports(&staked))
}

impl<T: Config> ElectionProvider for UnboundedExecution<T> {
	fn elect() -> Result<Supports<Self::AccountId>, Self::Error> {
		// This should not be called if not in `std` mode (and therefore neither in genesis nor in
		// testing)
		if cfg!(not(feature = "std")) {
			frame_support::log::error!(
				"Please use `InstantElectionProvider` instead to provide bounds on election if not in \
				genesis or testing mode"
			);
		}

		elect_with::<T>(None, None)
	}
}

impl<T: Config> ElectionProviderBase for UnboundedExecution<T> {
	type AccountId = <T::System as frame_system::Config>::AccountId;
	type BlockNumber = <T::System as frame_system::Config>::BlockNumber;
	type Error = Error;
	type DataProvider = T::DataProvider;

	fn ongoing() -> bool {
		false
	}
}

impl<T: Config> InstantElectionProvider for UnboundedExecution<T> {
	fn elect_with_bounds(
		max_voters: usize,
		max_targets: usize,
	) -> Result<Supports<Self::AccountId>, Self::Error> {
		elect_with::<T>(Some(max_voters), Some(max_targets))
	}
}

impl<T: BoundedConfig> ElectionProviderBase for BoundedExecution<T> {
	type AccountId = <T::System as frame_system::Config>::AccountId;
	type BlockNumber = <T::System as frame_system::Config>::BlockNumber;
	type Error = Error;
	type DataProvider = T::DataProvider;

	fn ongoing() -> bool {
		false
	}
}

impl<T: BoundedConfig> ElectionProvider for BoundedExecution<T> {
	fn elect() -> Result<Supports<Self::AccountId>, Self::Error> {
		elect_with::<T>(Some(T::VotersBound::get() as usize), Some(T::TargetsBound::get() as usize))
	}
}

impl<T: BoundedConfig> InstantElectionProvider for BoundedExecution<T> {
	fn elect_with_bounds(
		max_voters: usize,
		max_targets: usize,
	) -> Result<Supports<Self::AccountId>, Self::Error> {
		elect_with::<T>(
			Some(max_voters.min(T::VotersBound::get() as usize)),
			Some(max_targets.min(T::TargetsBound::get() as usize)),
		)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{PhragMMS, SequentialPhragmen};
	use frame_support::traits::ConstU32;
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
		type RuntimeOrigin = RuntimeOrigin;
		type Index = AccountId;
		type BlockNumber = BlockNumber;
		type RuntimeCall = RuntimeCall;
		type Hash = sp_core::H256;
		type Hashing = sp_runtime::traits::BlakeTwo256;
		type AccountId = AccountId;
		type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
		type Header = sp_runtime::testing::Header;
		type RuntimeEvent = ();
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

	struct PhragmenParams;
	struct PhragMMSParams;

	impl Config for PhragmenParams {
		type System = Runtime;
		type Solver = SequentialPhragmen<AccountId, Perbill>;
		type DataProvider = mock_data_provider::DataProvider;
		type WeightInfo = ();
	}

	impl BoundedConfig for PhragmenParams {
		type VotersBound = ConstU32<600>;
		type TargetsBound = ConstU32<400>;
	}

	impl Config for PhragMMSParams {
		type System = Runtime;
		type Solver = PhragMMS<AccountId, Perbill>;
		type DataProvider = mock_data_provider::DataProvider;
		type WeightInfo = ();
	}

	impl BoundedConfig for PhragMMSParams {
		type VotersBound = ConstU32<600>;
		type TargetsBound = ConstU32<400>;
	}

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
				BoundedExecution::<PhragmenParams>::elect().unwrap(),
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
				BoundedExecution::<PhragMMSParams>::elect().unwrap(),
				vec![
					(10, Support { total: 25, voters: vec![(1, 10), (3, 15)] }),
					(30, Support { total: 35, voters: vec![(2, 20), (3, 15)] })
				]
			);
		})
	}
}
