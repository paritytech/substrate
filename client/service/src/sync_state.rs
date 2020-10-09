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

use sp_runtime::traits::{Block as BlockT, NumberFor};
use sp_blockchain::HeaderBackend;
use std::sync::Arc;
use sp_runtime::generic::BlockId;

/// Build a `LightSyncState` from the CHT roots stored in a backend.
pub fn build_light_sync_state<TBl, TCl>(
	client: Arc<TCl>,
	shared_authority_set: grandpa::SharedAuthoritySet<<TBl as BlockT>::Hash, NumberFor<TBl>>,
	shared_epoch_changes: sc_consensus_epochs::SharedEpochChanges<TBl, sc_consensus_babe::Epoch>,
) -> Result<sc_chain_spec::LightSyncState<TBl>, sp_blockchain::Error>
	where
		TBl: BlockT,
		TCl: HeaderBackend<TBl>,
{
	let finalized_hash = client.info().finalized_hash;
	let finalized_header = client.header(BlockId::Hash(finalized_hash))?.unwrap();

	Ok(sc_chain_spec::LightSyncState {
		finalized_block_header: finalized_header,
		babe_epoch_changes: shared_epoch_changes.lock().clone(),
		grandpa_authority_set: shared_authority_set.inner().read().clone(),
	})
}
