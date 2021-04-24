// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// Copyright (C) 2021 Subpace Labs, Inc.
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

//! Schema for PoC epoch changes in the aux-db.

use log::info;
use codec::{Decode, Encode};

use sc_client_api::backend::AuxStore;
use sp_blockchain::{Result as ClientResult, Error as ClientError};
use sp_runtime::traits::Block as BlockT;
use sp_consensus_poc::{PoCBlockWeight, PoCGenesisConfiguration};
use sc_consensus_epochs::{EpochChangesFor, SharedEpochChanges};
use crate::Epoch;

const POC_EPOCH_CHANGES_VERSION: &[u8] = b"poc_epoch_changes_version";
const POC_EPOCH_CHANGES_KEY: &[u8] = b"poc_epoch_changes";
const POC_EPOCH_CHANGES_CURRENT_VERSION: u32 = 1;

fn block_weight_key<H: Encode>(block_hash: H) -> Vec<u8> {
	(b"block_weight", block_hash).encode()
}

fn load_decode<B, T>(backend: &B, key: &[u8]) -> ClientResult<Option<T>>
	where
		B: AuxStore,
		T: Decode,
{
	let corrupt = |e: codec::Error| {
		ClientError::Backend(format!("PoC DB is corrupted. Decode error: {}", e))
	};
	match backend.get_aux(key)? {
		None => Ok(None),
		Some(t) => T::decode(&mut &t[..]).map(Some).map_err(corrupt)
	}
}

/// Load or initialize persistent epoch change data from backend.
pub fn load_epoch_changes<Block: BlockT, B: AuxStore>(
	backend: &B,
	_config: &PoCGenesisConfiguration,
) -> ClientResult<SharedEpochChanges<Block, Epoch>> {
	let version = load_decode::<_, u32>(backend, POC_EPOCH_CHANGES_VERSION)?;

	let maybe_epoch_changes = match version {
		Some(POC_EPOCH_CHANGES_CURRENT_VERSION) => load_decode::<_, EpochChangesFor<Block, Epoch>>(
			backend,
			POC_EPOCH_CHANGES_KEY,
		)?,
		Some(other) => {
			return Err(ClientError::Backend(
				format!("Unsupported PoC DB version: {:?}", other)
			))
		},
		None => None,
	};

	let epoch_changes = SharedEpochChanges::<Block, Epoch>::new(maybe_epoch_changes.unwrap_or_else(|| {
		info!(
			target: "poc",
			"🧑‍🌾 Creating empty PoC epoch changes on what appears to be first startup.",
		);
		EpochChangesFor::<Block, Epoch>::default()
	}));

	// rebalance the tree after deserialization. this isn't strictly necessary
	// since the tree is now rebalanced on every update operation. but since the
	// tree wasn't rebalanced initially it's useful to temporarily leave it here
	// to avoid having to wait until an import for rebalancing.
	epoch_changes.shared_data().rebalance();

	Ok(epoch_changes)
}

/// Update the epoch changes on disk after a change.
pub(crate) fn write_epoch_changes<Block: BlockT, F, R>(
	epoch_changes: &EpochChangesFor<Block, Epoch>,
	write_aux: F,
) -> R where
	F: FnOnce(&[(&'static [u8], &[u8])]) -> R,
{
	POC_EPOCH_CHANGES_CURRENT_VERSION.using_encoded(|version| {
		let encoded_epoch_changes = epoch_changes.encode();
		write_aux(
			&[(POC_EPOCH_CHANGES_KEY, encoded_epoch_changes.as_slice()),
			  (POC_EPOCH_CHANGES_VERSION, version)],
		)
	})
}

/// Write the cumulative chain-weight of a block ot aux storage.
pub(crate) fn write_block_weight<H: Encode, F, R>(
	block_hash: H,
	block_weight: PoCBlockWeight,
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
pub fn load_block_weight<H: Encode, B: AuxStore>(
	backend: &B,
	block_hash: H,
) -> ClientResult<Option<PoCBlockWeight>> {
	load_decode(backend, block_weight_key(block_hash).as_slice())
}

// TODO: fix tests

// #[cfg(test)]
// mod test {
// 	use super::*;
// 	use crate::migration::EpochV0;
// 	use fork_tree::ForkTree;
// 	use substrate_test_runtime_client;
// 	use sp_core::H256;
// 	use sp_runtime::traits::NumberFor;
// 	use sp_consensus_poc::{AllowedSlots, BabeGenesisConfiguration};
// 	use sc_consensus_epochs::{PersistedEpoch, PersistedEpochHeader, EpochHeader};
// 	use sp_consensus::Error as ConsensusError;
// 	use sc_network_test::Block as TestBlock;
//
// 	#[test]
// 	fn load_decode_from_v0_epoch_changes() {
// 		let epoch = EpochV0 {
// 			start_slot: 0.into(),
// 			authorities: vec![],
// 			randomness: [0; 32],
// 			epoch_index: 1,
// 			duration: 100,
// 		};
// 		let client = substrate_test_runtime_client::new();
// 		let mut v0_tree = ForkTree::<H256, NumberFor<TestBlock>, _>::new();
// 		v0_tree.import::<_, ConsensusError>(
// 			Default::default(),
// 			Default::default(),
// 			PersistedEpoch::Regular(epoch),
// 			&|_, _| Ok(false), // Test is single item only so this can be set to false.
// 		).unwrap();
//
// 		client.insert_aux(
// 			&[(POC_EPOCH_CHANGES_KEY,
// 			   &EpochChangesForV0::<TestBlock, EpochV0>::from_raw(v0_tree).encode()[..])],
// 			&[],
// 		).unwrap();
//
// 		assert_eq!(
// 			load_decode::<_, u32>(&client, POC_EPOCH_CHANGES_VERSION).unwrap(),
// 			None,
// 		);
//
// 		let epoch_changes = load_epoch_changes::<TestBlock, _>(
// 			&client, &BabeGenesisConfiguration {
// 				slot_duration: 10,
// 				epoch_length: 4,
// 				c: (3, 10),
// 				genesis_authorities: Vec::new(),
// 				randomness: Default::default(),
// 				allowed_slots: AllowedSlots::PrimaryAndSecondaryPlainSlots,
// 			},
// 		).unwrap();
//
// 		assert!(
// 			epoch_changes.shared_data()
// 				.tree()
// 				.iter()
// 				.map(|(_, _, epoch)| epoch.clone())
// 				.collect::<Vec<_>>() ==
// 				vec![PersistedEpochHeader::Regular(EpochHeader {
// 					start_slot: 0.into(),
// 					end_slot: 100.into(),
// 				})],
// 		); // PersistedEpochHeader does not implement Debug, so we use assert! directly.
//
// 		write_epoch_changes::<TestBlock, _, _>(
// 			&epoch_changes.shared_data(),
// 			|values| {
// 				client.insert_aux(values, &[]).unwrap();
// 			},
// 		);
//
// 		assert_eq!(
// 			load_decode::<_, u32>(&client, POC_EPOCH_CHANGES_VERSION).unwrap(),
// 			Some(2),
// 		);
// 	}
// }
