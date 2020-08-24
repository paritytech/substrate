// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use sp_runtime::traits::{Block as BlockT, NumberFor, Saturating, One};
use sp_blockchain::HeaderBackend;
use std::sync::Arc;
use sp_runtime::generic::BlockId;
use sc_client_api::ProvideChtRoots;

/// Build a `LightSyncState` from the CHT roots stored in a backend.
pub fn build_light_sync_state<TBl, TCl, TBackend>(
	client: Arc<TCl>,
	backend: Arc<TBackend>,
) -> Result<sc_chain_spec::LightSyncState<TBl>, sp_blockchain::Error>
	where
		TBl: BlockT,
		TCl: HeaderBackend<TBl>,
		TBackend: sc_client_api::Backend<TBl>,
		<TBackend as sc_client_api::Backend<TBl>>::Blockchain: ProvideChtRoots<TBl>,
{
	let cht_root_provider = backend.blockchain();

	let finalized_hash = client.info().finalized_hash;
	let finalized_number = client.info().finalized_number;

	use sc_client_api::cht;

	let mut chts = Vec::new();

	// We can't fetch a CHT root later than `finalized_number - 2 * cht_size`.
	let cht_size_x_2 = cht::size::<NumberFor::<TBl>>() * NumberFor::<TBl>::from(2);

	let mut number = NumberFor::<TBl>::one();

	while number <= finalized_number.saturating_sub(cht_size_x_2) {
		match cht_root_provider.header_cht_root(cht::size(), number)? {
			Some(cht_root) => chts.push(cht_root),
			None => log::error!("No CHT found for block {}", number),
		}

		number += cht::size();
	}

	Ok(sc_chain_spec::LightSyncState {
		header: client.header(BlockId::Hash(finalized_hash))?.unwrap(),
		chts,
	})
}
