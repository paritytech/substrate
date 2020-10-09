// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Schema for BABE epoch changes in the aux-db.

use std::sync::Arc;
use parking_lot::Mutex;
use log::info;
use codec::{Decode, Encode};

use sc_client_api::backend::AuxStore;
use sp_blockchain::{Result as ClientResult, Error as ClientError};
use sp_runtime::traits::Block as BlockT;
use sp_consensus_babe::{BabeBlockWeight, BabeGenesisConfiguration};
use sc_consensus_epochs::{EpochChangesFor, SharedEpochChanges, migration::EpochChangesForV0};
use crate::{Epoch, migration::EpochV0};

const BABE_EPOCH_CHANGES_VERSION: &[u8] = b"babe_epoch_changes_version";
const BABE_EPOCH_CHANGES_KEY: &[u8] = b"babe_epoch_changes";
const BABE_EPOCH_CHANGES_CURRENT_VERSION: u32 = 2;

fn block_weight_key<H: Encode>(block_hash: H) -> Vec<u8> {
	(b"block_weight", block_hash).encode()
}

fn load_decode<B, T>(backend: &B, key: &[u8]) -> ClientResult<Option<T>>
	where
		B: AuxStore,
		T: Decode,
{
	let corrupt = |e: codec::Error| {
		ClientError::Backend(format!("BABE DB is corrupted. Decode error: {}", e.what()))
	};
	match backend.get_aux(key)? {
		None => Ok(None),
		Some(t) => T::decode(&mut &t[..]).map(Some).map_err(corrupt)
	}
}

/// Load or initialize persistent epoch change data from backend.
pub fn load_epoch_changes<Block: BlockT, B: AuxStore>(
	backend: &B,
	config: &BabeGenesisConfiguration,
) -> ClientResult<SharedEpochChanges<Block, Epoch>> {
	let version = load_decode::<_, u32>(backend, BABE_EPOCH_CHANGES_VERSION)?;

	let maybe_epoch_changes = match version {
		None => load_decode::<_, EpochChangesForV0<Block, EpochV0>>(
			backend,
			BABE_EPOCH_CHANGES_KEY,
		)?.map(|v0| v0.migrate().map(|_, _, epoch| epoch.migrate(config))),
		Some(1) => load_decode::<_, EpochChangesFor<Block, EpochV0>>(
			backend,
			BABE_EPOCH_CHANGES_KEY,
		)?.map(|v1| v1.map(|_, _, epoch| epoch.migrate(config))),
		Some(BABE_EPOCH_CHANGES_CURRENT_VERSION) => load_decode::<_, EpochChangesFor<Block, Epoch>>(
			backend,
			BABE_EPOCH_CHANGES_KEY,
		)?,
		Some(other) => {
			return Err(ClientError::Backend(
				format!("Unsupported BABE DB version: {:?}", other)
			))
		},
	};

	let epoch_changes = Arc::new(Mutex::new(maybe_epoch_changes.unwrap_or_else(|| {
		info!(target: "babe",
			  "👶 Creating empty BABE epoch changes on what appears to be first startup."
		);
		EpochChangesFor::<Block, Epoch>::default()
	})));

	// rebalance the tree after deserialization. this isn't strictly necessary
	// since the tree is now rebalanced on every update operation. but since the
	// tree wasn't rebalanced initially it's useful to temporarily leave it here
	// to avoid having to wait until an import for rebalancing.
	epoch_changes.lock().rebalance();

	Ok(epoch_changes)
}

/// Update the epoch changes on disk after a change.
pub(crate) fn write_epoch_changes<Block: BlockT, F, R>(
	epoch_changes: &EpochChangesFor<Block, Epoch>,
	write_aux: F,
) -> R where
	F: FnOnce(&[(&'static [u8], &[u8])]) -> R,
{
	BABE_EPOCH_CHANGES_CURRENT_VERSION.using_encoded(|version| {
		let encoded_epoch_changes = epoch_changes.encode();
		write_aux(
			&[(BABE_EPOCH_CHANGES_KEY, encoded_epoch_changes.as_slice()),
			  (BABE_EPOCH_CHANGES_VERSION, version)],
		)
	})
}

/// Write the cumulative chain-weight of a block ot aux storage.
pub(crate) fn write_block_weight<H: Encode, F, R>(
	block_hash: H,
	block_weight: BabeBlockWeight,
	write_aux: F,
) -> R where
	F: FnOnce(&[(Vec<u8>, &[u8])]) -> R,
{
	let key = block_weight_key(block_hash);
	block_weight.using_encoded(|s|
		write_aux(
			&[(key, s)],
		)
	)
}

/// Load the cumulative chain-weight associated with a block.
pub(crate) fn load_block_weight<H: Encode, B: AuxStore>(
	backend: &B,
	block_hash: H,
) -> ClientResult<Option<BabeBlockWeight>> {
	load_decode(backend, block_weight_key(block_hash).as_slice())
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::migration::EpochV0;
	use fork_tree::ForkTree;
	use substrate_test_runtime_client;
	use sp_core::H256;
	use sp_runtime::traits::NumberFor;
	use sp_consensus_babe::{AllowedSlots, BabeGenesisConfiguration};
	use sc_consensus_epochs::{PersistedEpoch, PersistedEpochHeader, EpochHeader};
	use sp_consensus::Error as ConsensusError;
	use sc_network_test::Block as TestBlock;

	#[test]
	fn load_decode_from_v0_epoch_changes() {
		let epoch = EpochV0 {
			start_slot: 0,
			authorities: vec![],
			randomness: [0; 32],
			epoch_index: 1,
			duration: 100,
		};
		let client = substrate_test_runtime_client::new();
		let mut v0_tree = ForkTree::<H256, NumberFor<TestBlock>, _>::new();
		v0_tree.import::<_, ConsensusError>(
			Default::default(),
			Default::default(),
			PersistedEpoch::Regular(epoch),
			&|_, _| Ok(false), // Test is single item only so this can be set to false.
		).unwrap();

		client.insert_aux(
			&[(BABE_EPOCH_CHANGES_KEY,
			   &EpochChangesForV0::<TestBlock, EpochV0>::from_raw(v0_tree).encode()[..])],
			&[],
		).unwrap();

		assert_eq!(
			load_decode::<_, u32>(&client, BABE_EPOCH_CHANGES_VERSION).unwrap(),
			None,
		);

		let epoch_changes = load_epoch_changes::<TestBlock, _>(
			&client, &BabeGenesisConfiguration {
				slot_duration: 10,
				epoch_length: 4,
				c: (3, 10),
				genesis_authorities: Vec::new(),
				randomness: Default::default(),
				allowed_slots: AllowedSlots::PrimaryAndSecondaryPlainSlots,
			},
		).unwrap();

		assert!(
			epoch_changes.lock()
				.tree()
				.iter()
				.map(|(_, _, epoch)| epoch.clone())
				.collect::<Vec<_>>() ==
				vec![PersistedEpochHeader::Regular(EpochHeader {
					start_slot: 0,
					end_slot: 100,
				})],
		); // PersistedEpochHeader does not implement Debug, so we use assert! directly.

		write_epoch_changes::<TestBlock, _, _>(
			&epoch_changes.lock(),
			|values| {
				client.insert_aux(values, &[]).unwrap();
			},
		);

		assert_eq!(
			load_decode::<_, u32>(&client, BABE_EPOCH_CHANGES_VERSION).unwrap(),
			Some(2),
		);
	}
}
