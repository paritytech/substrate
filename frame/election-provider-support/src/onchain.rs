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

//! An implementation of [`ElectionProvider`] that does an on-chain sequential phragmen.

use crate::{
	BoundedSupportsOf, ElectionDataProvider, ElectionProvider, InstantElectionProvider, PageIndex,
	TruncateIntoBoundedSupports,
};
use frame_support::{
	traits::{ConstU32, Get},
	weights::DispatchClass,
};
use sp_npos_elections::*;
use sp_std::{collections::btree_map::BTreeMap, marker::PhantomData, prelude::*};

/// Errors of the on-chain election.
#[derive(Eq, PartialEq, Debug)]
pub enum Error {
	/// An internal error in the NPoS elections crate.
	NposElections(sp_npos_elections::Error),
	/// Errors from the data provider.
	DataProvider(&'static str),
	/// The remaining pages expected are more than one, and the onchain seq-phragmen does not
	/// support that.
	NoMoreThenSinglePageExpected,
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
/// The amount of voters and targets that is fetched from [`Config::DataProvider`] is configurable
/// via [`Config::VoterPageSize`] and [`Config::TargetPageSize`].
///
/// The bounds of the returning results is determined by [`Config::MaxBackersPerWinner`] and
/// [`Config::MaxWinnersPerPage`]. Note that this implementation will simply TRUNCATE the results to
/// fit into this size.
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
pub struct OnChainSequentialPhragmen<T: Config>(PhantomData<T>);

/// Configuration trait of [`OnChainSequentialPhragmen`].
///
/// Note that this is similar to a pallet traits, but [`OnChainSequentialPhragmen`] is not a pallet.
///
/// WARNING: the user of this pallet must ensure that the `Accuracy` type will work nicely with the
/// normalization operation done inside `seq_phragmen`. See
/// [`sp_npos_elections::Assignment::try_normalize`] for more info.
pub trait Config: frame_system::Config {
	/// The accuracy used to compute the election:
	type Accuracy: PerThing128;

	/// Something that provides the data for election.
	type DataProvider: ElectionDataProvider<
		AccountId = Self::AccountId,
		BlockNumber = Self::BlockNumber,
	>;

	/// Maximum targets to get from the data provider.
	type TargetPageSize: Get<Option<usize>>;

	/// Maximum voters to get from the data provider.
	type VoterPageSize: Get<Option<usize>>;

	/// Maximum number of backers allowed per target.
	///
	/// This implementation will naively trim some of the backers, without any sorting.
	type MaxBackersPerWinner: Get<u32>;

	/// Maximum number of supports that can be returned per page.
	///
	/// Similarly, if this is less than `DataProvider`'s `desired_targets`, then it will naively
	/// trim the winners without any sorting.
	type MaxWinnersPerPage: Get<u32>;
}

impl<T: Config> OnChainSequentialPhragmen<T> {
	fn elect_with(
		maybe_max_voters: Option<usize>,
		maybe_max_targets: Option<usize>,
		remaining: PageIndex,
	) -> Result<BoundedSupportsOf<Self>, Error> {
		let voters = <Self as ElectionProvider>::DataProvider::voters(maybe_max_voters, remaining)
			.map_err(Error::DataProvider)?;
		let targets =
			<Self as ElectionProvider>::DataProvider::targets(maybe_max_targets, remaining)
				.map_err(Error::DataProvider)?;
		let desired_targets = <Self as ElectionProvider>::DataProvider::desired_targets()
			.map_err(Error::DataProvider)?;

		let stake_map: BTreeMap<T::AccountId, VoteWeight> = voters
			.iter()
			.map(|(validator, vote_weight, _)| (validator.clone(), *vote_weight))
			.collect();

		let stake_of =
			|w: &T::AccountId| -> VoteWeight { stake_map.get(w).cloned().unwrap_or_default() };

		let ElectionResult::<_, T::Accuracy> { winners: _, assignments } =
			seq_phragmen(desired_targets as usize, targets, voters, None).map_err(Error::from)?;

		let staked = assignment_ratio_to_staked_normalized(assignments, &stake_of)?;

		let weight = T::BlockWeights::get().max_block;
		frame_system::Pallet::<T>::register_extra_weight_unchecked(
			weight,
			DispatchClass::Mandatory,
		);

		// TODO: a sort impl as well would be good.
		let supports = to_supports(&staked);
		let bounded_supports = supports.truncate_into_bounded_supports();
		Ok(bounded_supports.into())
	}
}

impl<T: Config> ElectionProvider for OnChainSequentialPhragmen<T> {
	type Error = Error;
	type AccountId = T::AccountId;
	type BlockNumber = T::BlockNumber;
	type Pages = ConstU32<1>;
	type DataProvider = T::DataProvider;
	type MaxBackersPerWinner = T::MaxBackersPerWinner;
	type MaxWinnersPerPage = T::MaxWinnersPerPage;

	fn elect(remaining: PageIndex) -> Result<BoundedSupportsOf<Self>, Self::Error> {
		if remaining != 0 {
			return Err(Error::NoMoreThenSinglePageExpected)
		}

		Self::elect_with(None, None, remaining)
	}
}

impl<T: Config> InstantElectionProvider for OnChainSequentialPhragmen<T> {
	fn instant_elect(
		maybe_max_voters: Option<usize>,
		maybe_max_targets: Option<usize>,
		remaining: PageIndex,
	) -> Result<BoundedSupportsOf<Self>, Self::Error> {
		Self::elect_with(maybe_max_voters, maybe_max_targets, remaining)
	}
}

#[cfg(test)]
mod tests {
	use crate::TryIntoBoundedSupports;

	use super::*;
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

	impl Config for Runtime {
		type Accuracy = Perbill;
		type DataProvider = mock_data_provider::DataProvider;
		type TargetPageSize = ();
		type VoterPageSize = ();
		type MaxBackersPerWinner = ConstU32<16>;
		type MaxWinnersPerPage = ConstU32<16>;
	}

	type OnChainPhragmen = OnChainSequentialPhragmen<Runtime>;

	mod mock_data_provider {
		use frame_support::{bounded_vec, traits::ConstU32};

		use super::*;
		use crate::{data_provider, PageIndex, VoterOf};

		pub struct DataProvider;
		impl ElectionDataProvider for DataProvider {
			type AccountId = AccountId;
			type BlockNumber = BlockNumber;
			type MaxVotesPerVoter = ConstU32<2>;
			fn voters(_: Option<usize>, _: PageIndex) -> data_provider::Result<Vec<VoterOf<Self>>> {
				Ok(vec![
					(1, 10, bounded_vec![10, 20]),
					(2, 20, bounded_vec![30, 20]),
					(3, 30, bounded_vec![10, 30]),
				])
			}

			fn targets(_: Option<usize>, _: PageIndex) -> data_provider::Result<Vec<AccountId>> {
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
			let rhs: BoundedSupportsOf<OnChainPhragmen> = vec![
				(
					10 as AccountId,
					Support { total: 25, voters: vec![(1 as AccountId, 10), (3, 15)] },
				),
				(30, Support { total: 35, voters: vec![(2, 20), (3, 15)] }),
			]
			.try_into_bounded_supports()
			.unwrap();
			assert_eq!(OnChainPhragmen::elect(0).unwrap(), rhs);
		});
	}

	#[test]
	fn only_supports_single_page() {
		sp_io::TestExternalities::new_empty().execute_with(|| {
			assert_eq!(
				OnChainPhragmen::elect(1).unwrap_err(),
				super::Error::NoMoreThenSinglePageExpected
			);
		})
	}
}
