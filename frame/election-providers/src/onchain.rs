use crate::{ElectionProvider, Error};
use sp_arithmetic::PerThing;
use sp_npos_elections::{
	ElectionResult, ExtendedBalance, FlatSupportMap, IdentifierT, SupportMap, VoteWeight,
};
use sp_std::{collections::btree_map::BTreeMap, prelude::*};

pub struct OnChainSequentialPhragmen;
impl<AccountId: IdentifierT> ElectionProvider<AccountId> for OnChainSequentialPhragmen {
	fn elect<P: sp_arithmetic::PerThing>(
		to_elect: usize,
		targets: Vec<AccountId>,
		voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)>,
	) -> Result<FlatSupportMap<AccountId>, Error>
	where
		ExtendedBalance: From<<P as PerThing>::Inner>,
		P: sp_std::ops::Mul<ExtendedBalance, Output = ExtendedBalance>,
	{
		// TODO: we really don't need to do this conversion all the time. With
		// https://github.com/paritytech/substrate/pull/6685 merged, we should make variants of
		// seq_phragmen and others that return a different return type. In fact, I think I should
		// rebase this branch there and just build there as well.
		// TODO: Okay even if not the above, then def. make the extension traits for converting
		// between validator Major and Nominator Major result types, and make the conversions be
		// lossless and painless to happen.
		let mut stake_map: BTreeMap<AccountId, VoteWeight> = BTreeMap::new();
		voters.iter().for_each(|(v, s, _)| {
			stake_map.insert(v.clone(), *s);
		});
		let stake_of = Box::new(|w: &AccountId| -> VoteWeight {
			stake_map.get(w).cloned().unwrap_or_default()
		});

		sp_npos_elections::seq_phragmen::<_, P>(to_elect, targets, voters, None)
			.and_then(|e| {
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
					.map(|s| s.into_iter().map(|(k, v)| (k, v)).collect::<Vec<_>>())
			})
			.map_err(From::from)
	}

	fn ongoing() -> bool {
		false
	}
}
