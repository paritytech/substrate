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

use frame_election_provider_support::{ElectionDataProvider, SortedListProvider};
use frame_support::{storage::generator::StorageMap, traits::PalletInfoAccess};
use pallet_staking::Pallet as Staking;
use remote_externalities::{Builder, Mode, OnlineConfig};
use sp_runtime::{traits::Block as BlockT, DeserializeOwned};

/// Execute create a snapshot from pallet-staking.
pub async fn execute<Runtime: crate::RuntimeT, Block: BlockT + DeserializeOwned>(
	page_limit: Option<usize>,
	pages: usize,
	currency_unit: u64,
	ws_url: String,
) {
	let mut ext = Builder::<Block>::new()
		.mode(Mode::Online(OnlineConfig {
			transport: ws_url.to_string().into(),
			// NOTE: we don't scrape pallet-staking, this kinda ensures that the source of the data
			// is bags-list.
			pallets: vec![pallet_bags_list::Pallet::<Runtime>::name().to_string()],
			at: None,
			..Default::default()
		}))
		.inject_hashed_prefix(&<pallet_staking::Bonded<Runtime>>::prefix_hash())
		.inject_hashed_prefix(&<pallet_staking::Ledger<Runtime>>::prefix_hash())
		.inject_hashed_prefix(&<pallet_staking::Validators<Runtime>>::map_storage_final_prefix())
		.inject_hashed_prefix(&<pallet_staking::Nominators<Runtime>>::map_storage_final_prefix())
		.inject_hashed_key(&<pallet_staking::Validators<Runtime>>::counter_storage_final_key())
		.inject_hashed_key(&<pallet_staking::Nominators<Runtime>>::counter_storage_final_key())
		.build()
		.await
		.unwrap();

	ext.execute_with(|| {
		log::info!(
			target: crate::LOG_TARGET,
			"{} nodes in bags list.",
			<Runtime as pallet_staking::Config>::VoterList::count(),
		);
		log::info!(
			target: crate::LOG_TARGET,
			"generating {} pages of snapshot, ranging {:?}",
			pages,
			<Staking<Runtime>>::range(pages as u32).collect::<Vec<_>>(),
		);

		assert!(Staking::<Runtime>::last_iterated_nominator().is_none());

		for page in <Staking<Runtime>>::range(pages as u32) {
			let page_voters =
				<pallet_staking::Pallet<Runtime> as ElectionDataProvider>::electing_voters_paged(
					page_limit, page,
				)
				.unwrap();

			let currency_unit = currency_unit as f64;
			let min_voter =
				page_voters.last().map(|(x, y, _)| (x.clone(), *y as f64 / currency_unit));
			let max_voter =
				page_voters.first().map(|(x, y, _)| (x.clone(), *y as f64 / currency_unit));
			assert!(
				page == 0 ||
					Staking::<Runtime>::last_iterated_nominator() ==
						page_voters.last().map(|(x, _, _)| x.clone()),
			);

			log::info!(
				target: crate::LOG_TARGET,
				"took snapshot page {:?} with limit {:?}, {} voters are taken. min voter: {:?}, max: {:?}",
				page,
				page_limit,
				page_voters.len(),
				min_voter,
				max_voter
			);
		}

		assert!(Staking::<Runtime>::last_iterated_nominator().is_none());
	});
}
