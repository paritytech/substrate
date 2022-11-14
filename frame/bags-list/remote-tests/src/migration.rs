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

//! Test to check the migration of the voter bag.

use crate::{RuntimeT, LOG_TARGET};
use frame_support::traits::PalletInfoAccess;
use pallet_staking::Nominators;
use remote_externalities::{Builder, Mode, OnlineConfig};
use sp_runtime::{traits::Block as BlockT, DeserializeOwned};

/// Test voter bags migration. `currency_unit` is the number of planks per the the runtimes `UNITS`
/// (i.e. number of decimal places per DOT, KSM etc)
pub async fn execute<Runtime: RuntimeT, Block: BlockT + DeserializeOwned>(
	currency_unit: u64,
	currency_name: &'static str,
	ws_url: String,
) {
	let mut ext = Builder::<Block>::new()
		.mode(Mode::Online(OnlineConfig {
			transport: ws_url.to_string().into(),
			pallets: vec![pallet_staking::Pallet::<Runtime>::name().to_string()],
			..Default::default()
		}))
		.build()
		.await
		.unwrap();

	ext.execute_with(|| {
		// get the nominator & validator count prior to migrating; these should be invariant.
		let pre_migrate_nominator_count = <Nominators<Runtime>>::iter().count() as u32;
		log::info!(target: LOG_TARGET, "Nominator count: {}", pre_migrate_nominator_count);

		use frame_election_provider_support::SortedListProvider;
		// run the actual migration
		let moved = <Runtime as pallet_staking::Config>::VoterList::unsafe_regenerate(
			pallet_staking::Nominators::<Runtime>::iter().map(|(n, _)| n),
			pallet_staking::Pallet::<Runtime>::weight_of_fn(),
		);
		log::info!(target: LOG_TARGET, "Moved {} nominators", moved);

		let voter_list_len = <Runtime as pallet_staking::Config>::VoterList::iter().count() as u32;
		let voter_list_count = <Runtime as pallet_staking::Config>::VoterList::count();
		// and confirm it is equal to the length of the `VoterList`.
		assert_eq!(pre_migrate_nominator_count, voter_list_len);
		assert_eq!(pre_migrate_nominator_count, voter_list_count);

		crate::display_and_check_bags::<Runtime>(currency_unit, currency_name);
	});
}
