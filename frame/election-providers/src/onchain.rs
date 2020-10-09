use crate::{ElectionProvider, FlatSupportMap, FlattenSupportMap};
use sp_arithmetic::PerThing;
use sp_npos_elections::{ElectionResult, ExtendedBalance, IdentifierT, PerThing128, VoteWeight};
use sp_runtime::RuntimeDebug;
use sp_std::{collections::btree_map::BTreeMap, prelude::*};

/// Errors of the on-chain election.
#[derive(RuntimeDebug, Eq, PartialEq)]
pub enum Error {
	/// An internal error in the NPoS elections crate.
	NposElections(sp_npos_elections::Error),
}

impl From<sp_npos_elections::Error> for Error {
	fn from(e: sp_npos_elections::Error) -> Self {
		Error::NposElections(e)
	}
}

pub struct OnChainSequentialPhragmen;
impl<AccountId: IdentifierT> ElectionProvider<AccountId> for OnChainSequentialPhragmen {
	type Error = Error;

	const NEEDS_ELECT_DATA: bool = true;

	fn elect<P: PerThing128>(
		to_elect: usize,
		targets: Vec<AccountId>,
		voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)>,
	) -> Result<FlatSupportMap<AccountId>, Self::Error>
	where
		ExtendedBalance: From<<P as PerThing>::Inner>,
	{
		let mut stake_map: BTreeMap<AccountId, VoteWeight> = BTreeMap::new();
		voters.iter().for_each(|(v, s, _)| {
			stake_map.insert(v.clone(), *s);
		});
		let stake_of = Box::new(|w: &AccountId| -> VoteWeight {
			stake_map.get(w).cloned().unwrap_or_default()
		});

		sp_npos_elections::seq_phragmen::<_, P>(to_elect, targets, voters, None)
			.and_then(|e| {
				// these could use potential simplifications.
				let ElectionResult {
					winners,
					assignments,
				} = e;
				let staked = sp_npos_elections::assignment_ratio_to_staked_normalized(
					assignments,
					&stake_of,
				)?;
				let winners = sp_npos_elections::to_without_backing(winners);

				sp_npos_elections::build_support_map(&winners, &staked)
					.map(|s| s.flatten())
			})
			.map_err(From::from)
	}

	fn ongoing() -> bool {
		false
	}
}
