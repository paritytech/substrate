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

use sp_runtime::traits::{Block as BlockT, Header as HeaderT, NumberFor, One};
use sp_blockchain::HeaderBackend;
use std::sync::Arc;
use sp_runtime::ConsensusEngineId;
use sp_runtime::generic::BlockId;
use sc_client_api::{CallExecutor, ExecutorProvider};

fn backwards_consensus_log_iter<'a, TBl, TCl, CL, FN, T>(
	client: Arc<TCl>, mut number: NumberFor<TBl>, engine_id: &'a ConsensusEngineId, func: FN,
) -> impl Iterator<Item = Result<T, sp_blockchain::Error>> + 'a
	where
		TBl: BlockT,
		TCl: HeaderBackend<TBl> + 'a,
		CL: codec::Decode,
		FN: Fn(CL) -> Option<T> + 'a,
{
	let id = sp_runtime::generic::OpaqueDigestItemId::Consensus(engine_id);

	std::iter::from_fn(move || {
		let header = match client.header(BlockId::Number(number)) {
			Ok(Some(header)) => header,
			Ok(None) => return Some(Some(Err(sp_blockchain::Error::Msg("Missing header".into())))),
			Err(err) => return Some(Some(Err(err))),
		};

		let change = header.digest()
			.convert_first(|l| l.try_to(id).and_then(&func));

		number -= NumberFor::<TBl>::one();
		Some(change.map(Ok))
	}).filter_map(|optional_log_item| optional_log_item)
}

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

	let mut scheduled_changes = backwards_consensus_log_iter(
		client.clone(), finalized_number, &grandpa_primitives::GRANDPA_ENGINE_ID,
		|log| match log {
			grandpa_primitives::ConsensusLog::<NumberFor<TBl>>::ScheduledChange(change) => Some(change),
			grandpa_primitives::ConsensusLog::<NumberFor<TBl>>::ForcedChange(_, change) => Some(change),
			_ => None
		}
	);
	let future_change = scheduled_changes.next().unwrap()?;
	let current_authorities = scheduled_changes.next().unwrap()?.next_authorities;

	let mut babe_epoch_descriptors = backwards_consensus_log_iter(
		client.clone(), finalized_number, &sp_consensus_babe::BABE_ENGINE_ID,
		|log| match log {
			sp_consensus_babe::ConsensusLog::NextEpochData(descriptor)=> Some(descriptor),
			_ => None
		}
	);

	let next_desc = babe_epoch_descriptors.next().unwrap()?;
	let current_desc = babe_epoch_descriptors.next().unwrap()?;

	Ok(sc_chain_spec::LightSyncState {
		finalized_block_header: finalized_header,
		babe_finalized_block1_slot_number: 0,
		babe_finalized_block_epoch_information: current_desc,
		babe_finalized_next_epoch_transition: next_desc,
		grandpa_finalized_triggered_authorities: current_authorities,
		grandpa_after_finalized_block_authorities_set_id: 0,
		grandpa_finalized_scheduled_change: future_change,
	})
}
