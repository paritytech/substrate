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

//! An implementation of [`ElectionProvider`] that uses an `NposSolver` to do the election. As the
//! name suggests, this is meant to be used onchain. Given how heavy the calculations are, please be
//! careful when using it onchain.

use crate::{
	BoundedSupportsOf, Debug, ElectionDataProvider, ElectionProvider, ElectionProviderBase,
	InstantElectionProvider, NposSolver, WeightInfo,
};
use frame_support::{dispatch::DispatchClass, traits::Get};
use sp_npos_elections::{
	assignment_ratio_to_staked_normalized, to_supports, BoundedSupports, ElectionResult, VoteWeight,
};
use sp_std::{collections::btree_map::BTreeMap, marker::PhantomData, prelude::*};

/// Errors of the on-chain election.
#[derive(Eq, PartialEq, Debug)]
pub enum Error {
	/// An internal error in the NPoS elections crate.
	NposElections(sp_npos_elections::Error),
	/// Errors from the data provider.
	DataProvider(&'static str),
	/// Configurational error caused by `desired_targets` requested by data provider exceeding
	/// `MaxWinners`.
	TooManyWinners,
}

impl From<sp_npos_elections::Error> for Error {
	fn from(e: sp_npos_elections::Error) -> Self {
		Error::NposElections(e)
	}
}

/// A simple on-chain implementation of the election provider trait.
///
/// This implements both `ElectionProvider` and `InstantElectionProvider`.
///
/// This type has some utilities to make it safe. Nonetheless, it should be used with utmost care. A
/// thoughtful value must be set as [`Config::VotersBound`] and [`Config::TargetsBound`] to ensure
/// the size of the input is sensible.
pub struct OnChainExecution<T: Config>(PhantomData<T>);

#[deprecated(note = "use OnChainExecution, which is bounded by default")]
pub type BoundedExecution<T> = OnChainExecution<T>;

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
		BlockNumber = frame_system::pallet_prelude::BlockNumberFor<Self::System>,
	>;

	/// Weight information for extrinsics in this pallet.
	type WeightInfo: WeightInfo;

	/// Upper bound on maximum winners from electable targets.
	///
	/// As noted in the documentation of [`ElectionProviderBase::MaxWinners`], this value should
	/// always be more than `DataProvider::desired_target`.
	type MaxWinners: Get<u32>;

	/// Bounds the number of voters, when calling into [`Config::DataProvider`]. It might be
	/// overwritten in the `InstantElectionProvider` impl.
	type VotersBound: Get<u32>;

	/// Bounds the number of targets, when calling into [`Config::DataProvider`]. It might be
	/// overwritten in the `InstantElectionProvider` impl.
	type TargetsBound: Get<u32>;
}

/// Same as `BoundedSupportsOf` but for `onchain::Config`.
pub type OnChainBoundedSupportsOf<E> = BoundedSupports<
	<<E as Config>::System as frame_system::Config>::AccountId,
	<E as Config>::MaxWinners,
>;

fn elect_with_input_bounds<T: Config>(
	maybe_max_voters: Option<usize>,
	maybe_max_targets: Option<usize>,
) -> Result<OnChainBoundedSupportsOf<T>, Error> {
	let voters = T::DataProvider::electing_voters(maybe_max_voters).map_err(Error::DataProvider)?;
	let targets =
		T::DataProvider::electable_targets(maybe_max_targets).map_err(Error::DataProvider)?;
	let desired_targets = T::DataProvider::desired_targets().map_err(Error::DataProvider)?;

	if desired_targets > T::MaxWinners::get() {
		// early exit
		return Err(Error::TooManyWinners)
	}

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

	// defensive: Since npos solver returns a result always bounded by `desired_targets`, this is
	// never expected to happen as long as npos solver does what is expected for it to do.
	let supports: OnChainBoundedSupportsOf<T> =
		to_supports(&staked).try_into().map_err(|_| Error::TooManyWinners)?;

	Ok(supports)
}

impl<T: Config> ElectionProviderBase for OnChainExecution<T> {
	type AccountId = <T::System as frame_system::Config>::AccountId;
	type BlockNumber = frame_system::pallet_prelude::BlockNumberFor<T::System>;
	type Error = Error;
	type MaxWinners = T::MaxWinners;
	type DataProvider = T::DataProvider;
}

impl<T: Config> InstantElectionProvider for OnChainExecution<T> {
	fn instant_elect(
		forced_input_voters_bound: Option<u32>,
		forced_input_target_bound: Option<u32>,
	) -> Result<BoundedSupportsOf<Self>, Self::Error> {
		elect_with_input_bounds::<T>(
			Some(T::VotersBound::get().min(forced_input_voters_bound.unwrap_or(u32::MAX)) as usize),
			Some(T::TargetsBound::get().min(forced_input_target_bound.unwrap_or(u32::MAX)) as usize),
		)
	}
}

impl<T: Config> ElectionProvider for OnChainExecution<T> {
	fn ongoing() -> bool {
		false
	}

	fn elect() -> Result<BoundedSupportsOf<Self>, Self::Error> {
		elect_with_input_bounds::<T>(
			Some(T::VotersBound::get() as usize),
			Some(T::TargetsBound::get() as usize),
		)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{ElectionProvider, PhragMMS, SequentialPhragmen};
	use frame_support::{assert_noop, parameter_types, traits::ConstU32};
	use sp_npos_elections::Support;
	use sp_runtime::Perbill;
	type AccountId = u64;
	type Nonce = u64;
	type BlockNumber = u64;

	pub type Header = sp_runtime::generic::Header<BlockNumber, sp_runtime::traits::BlakeTwo256>;
	pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<AccountId, (), (), ()>;
	pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;

	frame_support::construct_runtime!(
		pub struct Runtime
		{
			System: frame_system::{Pallet, Call, Event<T>},
		}
	);

	impl frame_system::Config for Runtime {
		type SS58Prefix = ();
		type BaseCallFilter = frame_support::traits::Everything;
		type RuntimeOrigin = RuntimeOrigin;
		type Nonce = Nonce;
		type RuntimeCall = RuntimeCall;
		type Hash = sp_core::H256;
		type Hashing = sp_runtime::traits::BlakeTwo256;
		type AccountId = AccountId;
		type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
		type Block = Block;
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

	parameter_types! {
		pub static MaxWinners: u32 = 10;
		pub static DesiredTargets: u32 = 2;
	}

	impl Config for PhragmenParams {
		type System = Runtime;
		type Solver = SequentialPhragmen<AccountId, Perbill>;
		type DataProvider = mock_data_provider::DataProvider;
		type WeightInfo = ();
		type MaxWinners = MaxWinners;
		type VotersBound = ConstU32<600>;
		type TargetsBound = ConstU32<400>;
	}

	impl Config for PhragMMSParams {
		type System = Runtime;
		type Solver = PhragMMS<AccountId, Perbill>;
		type DataProvider = mock_data_provider::DataProvider;
		type WeightInfo = ();
		type MaxWinners = MaxWinners;
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
				Ok(DesiredTargets::get())
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
				<OnChainExecution::<PhragmenParams> as ElectionProvider>::elect().unwrap(),
				vec![
					(10, Support { total: 25, voters: vec![(1, 10), (3, 15)] }),
					(30, Support { total: 35, voters: vec![(2, 20), (3, 15)] })
				]
			);
		})
	}

	#[test]
	fn too_many_winners_when_desired_targets_exceed_max_winners() {
		sp_io::TestExternalities::new_empty().execute_with(|| {
			// given desired targets larger than max winners
			DesiredTargets::set(10);
			MaxWinners::set(9);

			assert_noop!(
				<OnChainExecution::<PhragmenParams> as ElectionProvider>::elect(),
				Error::TooManyWinners,
			);
		})
	}

	#[test]
	fn onchain_phragmms_works() {
		sp_io::TestExternalities::new_empty().execute_with(|| {
			assert_eq!(
				<OnChainExecution::<PhragMMSParams> as ElectionProvider>::elect().unwrap(),
				vec![
					(10, Support { total: 25, voters: vec![(1, 10), (3, 15)] }),
					(30, Support { total: 35, voters: vec![(2, 20), (3, 15)] })
				]
			);
		})
	}
}
