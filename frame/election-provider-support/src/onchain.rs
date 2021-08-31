// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

use crate::{ElectionDataProvider, ElectionProvider, PageIndex};
use frame_support::traits::Get;
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
/// ### Warning
///
/// This can be very expensive to run frequently on-chain. Use with care. Moreover, this
/// implementation ignores the additional data of the election data provider and gives no insight on
/// how much weight was consumed.
///
/// Finally, this implementation does not impose any limits on the number of voters and targets that
/// are provided.
pub struct OnChainSequentialPhragmen<T: Config>(PhantomData<T>);

/// Configuration trait of [`OnChainSequentialPhragmen`].
///
/// Note that this is similar to a pallet traits, but [`OnChainSequentialPhragmen`] is not a pallet.
pub trait Config {
	/// The account identifier type.
	type AccountId: IdentifierT;
	/// The block number type.
	type BlockNumber;
	/// The accuracy used to compute the election:
	type Accuracy: PerThing128;
	/// Something that provides the data for election.
	type DataProvider: ElectionDataProvider<Self::AccountId, Self::BlockNumber>;
	/// Maximum targets to get from the data provider.
	type TargetsPageSize: Get<Option<usize>>;
	/// Maximum voters to get from the data provider.
	type VoterPageSize: Get<Option<usize>>;
}

impl<T: Config> ElectionProvider<T::AccountId, T::BlockNumber> for OnChainSequentialPhragmen<T> {
	type Error = Error;
	type DataProvider = T::DataProvider;
	type Pages = frame_support::traits::ConstU8<1>;

	fn elect(remaining: PageIndex) -> Result<Supports<T::AccountId>, Self::Error> {
		if remaining != 0 {
			return Err(Error::NoMoreThenSinglePageExpected)
		}
		let voters = Self::DataProvider::voters(T::TargetsPageSize::get(), 0)
			.map_err(Error::DataProvider)?;
		let targets =
			Self::DataProvider::targets(T::VoterPageSize::get(), 0).map_err(Error::DataProvider)?;
		let desired_targets = Self::DataProvider::desired_targets().map_err(Error::DataProvider)?;

		let stake_map: BTreeMap<T::AccountId, VoteWeight> = voters
			.iter()
			.map(|(validator, vote_weight, _)| (validator.clone(), *vote_weight))
			.collect();

		let stake_of =
			|w: &T::AccountId| -> VoteWeight { stake_map.get(w).cloned().unwrap_or_default() };

		let ElectionResult { winners, assignments } =
			seq_phragmen::<_, T::Accuracy>(desired_targets as usize, targets, voters, None)
				.map_err(Error::from)?;

		let staked = assignment_ratio_to_staked_normalized(assignments, &stake_of)?;
		let winners = to_without_backing(winners);

		to_supports(&winners, &staked).map_err(Error::from)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_npos_elections::Support;
	use sp_runtime::Perbill;

	type AccountId = u64;
	type BlockNumber = u32;
	struct Runtime;
	impl Config for Runtime {
		type AccountId = AccountId;
		type BlockNumber = BlockNumber;
		type Accuracy = Perbill;
		type DataProvider = mock_data_provider::DataProvider;
		type TargetsPageSize = ();
		type VoterPageSize = ();
	}

	type OnChainPhragmen = OnChainSequentialPhragmen<Runtime>;

	mod mock_data_provider {
		use super::*;
		use crate::{data_provider, PageIndex};

		pub struct DataProvider;
		impl ElectionDataProvider<AccountId, BlockNumber> for DataProvider {
			const MAXIMUM_VOTES_PER_VOTER: u32 = 2;
			fn voters(
				_: Option<usize>,
				_: PageIndex,
			) -> data_provider::Result<Vec<(AccountId, VoteWeight, Vec<AccountId>)>> {
				Ok((vec![(1, 10, vec![10, 20]), (2, 20, vec![30, 20]), (3, 30, vec![10, 30])], 0))
			}

			fn targets(
				_: Option<usize>,
				_: PageIndex,
			) -> data_provider::Result<(Vec<AccountId>, Weight)> {
				Ok((vec![10, 20, 30], 0))
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
		assert_eq!(
			OnChainPhragmen::elect().unwrap(),
			vec![
				(10, Support { total: 25, voters: vec![(1, 10), (3, 15)] }),
				(30, Support { total: 35, voters: vec![(2, 20), (3, 15)] })
			]
		);
	}
}
