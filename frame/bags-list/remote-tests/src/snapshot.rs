// Copyright 2021 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Test to execute the snapshot using the voter bag.

use frame_support::traits::PalletInfoAccess;
use remote_externalities::{Builder, Mode, OnlineConfig};
use sp_runtime::traits::Block as BlockT;

/// Execute create a snapshot from pallet-staking.
pub async fn execute<Runtime: crate::RuntimeT, Block: BlockT>(
	voter_limit: Option<usize>,
	currency_unit: u64,
	ws_url: String,
) {
	use frame_support::storage::generator::StorageMap;
	let mut ext = Builder::<Block>::new()
		.mode(Mode::Online(OnlineConfig {
			transport: ws_url.to_string().into(),
			// NOTE: we don't scrape pallet-staking, this kinda ensures that the source of the data
			// is bags-list.
			pallets: vec![pallet_bags_list::Pallet::<Runtime>::name().to_string()],
			at: None,
			state_snapshot: None,
		}))
		.inject_hashed_prefix(&<pallet_staking::Bonded<Runtime>>::prefix_hash())
		.inject_hashed_prefix(&<pallet_staking::Ledger<Runtime>>::prefix_hash())
		.inject_hashed_prefix(&<pallet_staking::Validators<Runtime>>::prefix_hash())
		.inject_hashed_prefix(&<pallet_staking::Nominators<Runtime>>::prefix_hash())
		.inject_hashed_key(&<pallet_staking::CounterForNominators<Runtime>>::hashed_key())
		.inject_hashed_key(&<pallet_staking::CounterForValidators<Runtime>>::hashed_key())
		.build()
		.await
		.unwrap();

	ext.execute_with(|| {
		use frame_election_provider_support::{ElectionDataProvider, SortedListProvider};
		log::info!(
			target: crate::LOG_TARGET,
			"{} nodes in bags list.",
			<Runtime as pallet_staking::Config>::SortedListProvider::count(),
		);

		let voters = <pallet_staking::Pallet<Runtime> as ElectionDataProvider<
			Runtime::AccountId,
			Runtime::BlockNumber,
		>>::voters(voter_limit)
		.unwrap();

		let mut voters_nominator_only = voters
			.iter()
			.filter(|(v, _, _)| pallet_staking::Nominators::<Runtime>::contains_key(v))
			.cloned()
			.collect::<Vec<_>>();
		voters_nominator_only.sort_by_key(|(_, w, _)| *w);

		let currency_unit = currency_unit as f64;
		let min_voter = voters_nominator_only
			.first()
			.map(|(x, y, _)| (x.clone(), *y as f64 / currency_unit));
		let max_voter = voters_nominator_only
			.last()
			.map(|(x, y, _)| (x.clone(), *y as f64 / currency_unit));
		log::info!(
			target: crate::LOG_TARGET,
			"a snapshot with limit {:?} has been created, {} voters are taken. min nominator: {:?}, max: {:?}",
			voter_limit,
			voters.len(),
			min_voter,
			max_voter
		);
	});
}
