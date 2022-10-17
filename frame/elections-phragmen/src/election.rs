use sp_std::{marker::PhantomData, prelude::*};

use frame_election_provider_support::{
	weights::WeightInfo, BoundedVec, ElectionDataProvider, ElectionProvider, ElectionProviderBase,
	InstantElectionProvider, NposSolver, VoterOf,
};
use frame_support::traits::Get;
use sp_npos_elections::*;

type AccountId<T> = <T as frame_system::Config>::AccountId;
type BlockNumber<T> = <T as frame_system::Config>::BlockNumber;
type Balance = u64; // TODO(gpestana): draft for now; abstract

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

pub trait DataProviderConfig {
	type System: frame_system::Config;
	type MaxVotesPerVoter: Get<u32>;

	fn candidates() -> Vec<AccountId<Self::System>>;
	fn votes_with_stake(
	) -> Vec<(AccountId<Self::System>, crate::Voter<AccountId<Self::System>, Balance>)>;
}

pub struct DataProvider<T: DataProviderConfig>(PhantomData<T>);
impl<T: DataProviderConfig> ElectionDataProvider for DataProvider<T> {
	type AccountId = AccountId<T::System>;
	type BlockNumber = BlockNumber<T::System>;
	type MaxVotesPerVoter = T::MaxVotesPerVoter;

	fn electable_targets(
		maybe_max_len: Option<usize>,
	) -> frame_election_provider_support::data_provider::Result<Vec<Self::AccountId>> {
		Ok(T::candidates())
	}

	fn electing_voters(
		maybe_max_len: Option<usize>,
	) -> frame_election_provider_support::data_provider::Result<Vec<VoterOf<Self>>> {
		let max_votes_per_voter = T::MaxVotesPerVoter::get() as usize;
		let mut voters_and_stakes = Vec::new();

		match T::votes_with_stake().into_iter().try_for_each(
			|(voter, crate::Voter { stake, votes, .. })| {
				if let Some(max_voters) = maybe_max_len {
					if voters_and_stakes.len() > max_voters {
						return Err(());
					}
				}
				let bounded_votes: BoundedVec<_, T::MaxVotesPerVoter> =
					BoundedVec::try_from(votes).map_err(|_| ())?; // TODO(gpestana): ref to proper err

				voters_and_stakes.push((voter, stake, bounded_votes));
				Ok(())
			},
		) {
			Ok(_) => (),
			Err(_) => return Err(""), // TODO(gpestana): ref proper err
		}

		Ok(voters_and_stakes)
	}

	fn desired_targets() -> frame_election_provider_support::data_provider::Result<u32> {
		// TODO(gpestana): fill in
		Ok(10)
	}

	fn next_election_prediction(now: Self::BlockNumber) -> Self::BlockNumber {
		// TODO(gpestana): fill in
		<frame_system::Pallet<T::System>>::block_number()
	}
}

pub trait ElectionConfig {
	type System: frame_system::Config;
	type DataProvider: ElectionDataProvider<
		AccountId = AccountId<Self::System>,
		BlockNumber = BlockNumber<Self::System>,
	>;
	type Solver: NposSolver<AccountId = AccountId<Self::System>, Error = sp_npos_elections::Error>;
	type WeightInfo: WeightInfo;
}

pub struct BoundedExecution<T: ElectionConfig>(PhantomData<T>);

fn elect_with_bounds<T: ElectionConfig>(
	maybe_max_voters: Option<usize>,
	maybe_max_targets: Option<usize>,
) -> Result<Supports<AccountId<T::System>>, Error> {
	// TODO(gpestana): finsh impl

	// TODO(gpestana): handle unwraps()
	let num_to_elect = T::DataProvider::desired_targets().unwrap();
	let candidate_ids = T::DataProvider::electable_targets(maybe_max_targets).unwrap();
	let voters_and_votes = T::DataProvider::electing_voters(maybe_max_voters).unwrap();

	T::Solver::solve(num_to_elect as usize, candidate_ids, voters_and_votes)
		.map(|election_result| {});

	Ok(vec![])
}

impl<T: ElectionConfig> ElectionProviderBase for BoundedExecution<T> {
	type AccountId = AccountId<T::System>;
	type BlockNumber = BlockNumber<T::System>;
	type Error = Error;
	type DataProvider = T::DataProvider;

	fn ongoing() -> bool {
		return false;
	}
}

impl<T: ElectionConfig> ElectionProvider for BoundedExecution<T> {
	fn elect() -> Result<frame_election_provider_support::Supports<Self::AccountId>, Self::Error> {
		// This should not be called if not in `std` mode (and therefore neither in genesis nor in
		// testing)
		if cfg!(not(feature = "std")) {
			frame_support::log::error!(
				"Please use `InstantElectionProvider` instead to provide bounds on election if not in \
				genesis or testing mode"
			);
		}

		elect_with_bounds::<T>(None, None)
	}
}

impl<T: ElectionConfig> InstantElectionProvider for BoundedExecution<T> {
	fn elect_with_bounds(
		max_voters: usize,
		max_targets: usize,
	) -> Result<Supports<Self::AccountId>, Self::Error> {
		elect_with_bounds::<T>(Some(max_voters), Some(max_targets))
	}
}
