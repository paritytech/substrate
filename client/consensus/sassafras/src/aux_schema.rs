// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Schema for auxiliary data persistence.
//!
//! TODO-SASS-P2 : RENAME FROM aux_schema.rs => aux_data.rs

use std::{collections::HashSet, sync::Arc};

use scale_codec::{Decode, Encode};

use sc_client_api::backend::AuxStore;
use sc_consensus_epochs::{EpochChangesFor, SharedEpochChanges};

use sc_client_api::{blockchain::Backend as _, Backend as BackendT};
use sp_blockchain::{Error as ClientError, HeaderBackend, HeaderMetadata, Result as ClientResult};
use sp_consensus_sassafras::SassafrasBlockWeight;
use sp_runtime::traits::{Block as BlockT, NumberFor, SaturatedConversion, Zero};

use crate::Epoch;

const SASSAFRAS_EPOCH_CHANGES_KEY: &[u8] = b"sassafras_epoch_changes";

/// The aux storage key used to store the block weight of the given block hash.
fn block_weight_key<H: Encode>(block_hash: H) -> Vec<u8> {
	(b"sassafras_block_weight", block_hash).encode()
}

fn load_decode<B, T>(backend: &B, key: &[u8]) -> ClientResult<Option<T>>
where
	B: AuxStore,
	T: Decode,
{
	match backend.get_aux(key)? {
		Some(t) => T::decode(&mut &t[..]).map(Some).map_err(|e| {
			ClientError::Backend(format!("Sassafras db is corrupted, Decode error: {}", e))
		}),
		None => Ok(None),
	}
}

/// Update the epoch changes on disk after a change.
pub fn write_epoch_changes<Block: BlockT, F, R>(
	epoch_changes: &EpochChangesFor<Block, Epoch>,
	write_aux: F,
) -> R
where
	F: FnOnce(&[(&'static [u8], &[u8])]) -> R,
{
	epoch_changes.using_encoded(|s| write_aux(&[(SASSAFRAS_EPOCH_CHANGES_KEY, s)]))
}

/// Load or initialize persistent epoch change data from backend.
pub fn load_epoch_changes<B: BlockT, AS: AuxStore>(
	backend: &AS,
) -> ClientResult<SharedEpochChanges<B, Epoch>> {
	let maybe_epoch_changes =
		load_decode::<_, EpochChangesFor<B, Epoch>>(backend, SASSAFRAS_EPOCH_CHANGES_KEY)?;

	let epoch_changes = SharedEpochChanges::<B, Epoch>::new(
		maybe_epoch_changes.unwrap_or_else(|| EpochChangesFor::<B, Epoch>::default()),
	);

	// Rebalance the tree after deserialization. this isn't strictly necessary
	// since the tree is now rebalanced on every update operation. but since the
	// tree wasn't rebalanced initially it's useful to temporarily leave it here
	// to avoid having to wait until an import for rebalancing.
	epoch_changes.shared_data().rebalance();

	Ok(epoch_changes)
}

/// Write the cumulative chain-weight of a block ot aux storage.
pub fn write_block_weight<H: Encode, F, R>(
	block_hash: H,
	block_weight: SassafrasBlockWeight,
	write_aux: F,
) -> R
where
	F: FnOnce(&[(Vec<u8>, &[u8])]) -> R,
{
	let key = block_weight_key(block_hash);
	block_weight.using_encoded(|s| write_aux(&[(key, s)]))
}

/// Load the cumulative chain-weight associated with a block.
pub fn load_block_weight<H: Encode, B: AuxStore>(
	backend: &B,
	block_hash: H,
) -> ClientResult<Option<SassafrasBlockWeight>> {
	load_decode(backend, block_weight_key(block_hash).as_slice())
}

/// Reverts protocol aux data from the best block to at most the last finalized block.
///
/// Epoch-changes and block weights announced after the revert point are removed.
pub fn revert<Block, Backend>(backend: Arc<Backend>, blocks: NumberFor<Block>) -> ClientResult<()>
where
	Block: BlockT,
	Backend: BackendT<Block>,
{
	let blockchain = backend.blockchain();
	let best_number = blockchain.info().best_number;
	let finalized = blockchain.info().finalized_number;

	let revertible = blocks.min(best_number - finalized);
	if revertible == Zero::zero() {
		return Ok(())
	}

	let revert_up_to_number = best_number - revertible;
	let revert_up_to_hash = blockchain.hash(revert_up_to_number)?.ok_or(ClientError::Backend(
		format!("Unexpected hash lookup failure for block number: {}", revert_up_to_number),
	))?;

	// Revert epoch changes tree.

	// This config is only used on-genesis.
	let epoch_changes = load_epoch_changes::<Block, _>(&*backend)?;
	let mut epoch_changes = epoch_changes.shared_data();

	if revert_up_to_number == Zero::zero() {
		// Special case, no epoch changes data were present on genesis.
		*epoch_changes = EpochChangesFor::<Block, Epoch>::new();
	} else {
		let descendent_query = sc_consensus_epochs::descendent_query(blockchain);
		epoch_changes.revert(descendent_query, revert_up_to_hash, revert_up_to_number);
	}

	// Remove block weights added after the revert point.

	let mut weight_keys = HashSet::with_capacity(revertible.saturated_into());

	let leaves = backend.blockchain().leaves()?.into_iter().filter(|&leaf| {
		sp_blockchain::tree_route(blockchain, revert_up_to_hash, leaf)
			.map(|route| route.retracted().is_empty())
			.unwrap_or_default()
	});

	for mut hash in leaves {
		loop {
			let meta = blockchain.header_metadata(hash)?;
			if meta.number <= revert_up_to_number || !weight_keys.insert(block_weight_key(hash)) {
				// We've reached the revert point or an already processed branch, stop here.
				break
			}
			hash = meta.parent;
		}
	}

	let weight_keys: Vec<_> = weight_keys.iter().map(|val| val.as_slice()).collect();

	// Write epoch changes and remove weights in one shot.
	write_epoch_changes::<Block, _, _>(&epoch_changes, |values| {
		AuxStore::insert_aux(&*backend, values, weight_keys.iter())
	})
}
