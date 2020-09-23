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

use sp_runtime::traits::Block as BlockT;
use sp_runtime::traits::One;
use sp_blockchain::HeaderBackend;
use std::sync::Arc;
use sp_runtime::generic::BlockId;
use sp_api::NumberFor;

/// Build a `LightSyncState` from the CHT roots stored in a backend.
pub fn build_light_sync_state<TBl, TCl>(
	client: Arc<TCl>,
) -> Result<sc_chain_spec::LightSyncState<TBl>, sp_blockchain::Error>
	where
		TBl: BlockT,
		TCl: HeaderBackend<TBl> + sp_api::ProvideRuntimeApi<TBl> + sc_client_api::AuxStore,
		<TCl as sp_api::ProvideRuntimeApi<TBl>>::Api:
			sc_consensus_babe::BabeApi<TBl, Error=sp_blockchain::Error>,
{
	let finalized_number = client.info().finalized_number;
	let finalized_hash = client.info().finalized_hash;
	let finalized_header = client.header(BlockId::Hash(finalized_hash))?.unwrap();

	let babe_config = sc_consensus_babe::Config::get_or_compute(&*client)?;

	let babe_epoch_changes =
		sc_consensus_babe::aux_schema::load_epoch_changes::<TBl, _>(&*client, &babe_config)?;

	let block1_number = NumberFor::<TBl>::one();
	let block1_hash = client.hash(block1_number)?.unwrap();

	let babe_epoch_changes_lock = babe_epoch_changes.lock();

	let epoch_1 = babe_epoch_changes_lock.epoch(&sc_consensus_epochs::EpochIdentifier {
		position: sc_consensus_epochs::EpochIdentifierPosition::Genesis0,
		number: block1_number,
		hash: block1_hash,
	}).unwrap();

	let finalized_epoch = babe_epoch_changes_lock.epoch(&sc_consensus_epochs::EpochIdentifier {
		position: sc_consensus_epochs::EpochIdentifierPosition::Regular,
		number: finalized_number,
		hash: finalized_hash
	}).unwrap().clone();

	let authorities =
		grandpa::load_authorities::<_, <TBl as BlockT>::Hash, NumberFor<TBl>>(&*client).unwrap();

	Ok(sc_chain_spec::LightSyncState {
		header: finalized_header,
		babe_finalized_block1_slot_number: epoch_1.start_slot,
		babe_finalized_block_epoch_information: finalized_epoch.clone(),
		babe_finalized_next_epoch_transition: finalized_epoch,
		grandpa_finalized_triggered_authorities: authorities.current_authorities,
		grandpa_after_finalized_block_authorities_set_id: authorities.set_id,
	})
}
