// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Schema for BABE session changes in the aux-db.

use codec::{Decode, Encode};
use log::info;

use crate::{migration::SessionV0, Session};
use sc_client_api::backend::AuxStore;
use sc_consensus_sessions::{
	migration::{SessionChangesV0For, SessionChangesV1For},
	SessionChangesFor, SharedSessionChanges,
};
use sp_blockchain::{Error as ClientError, Result as ClientResult};
use sp_consensus_babe::{BabeBlockWeight, BabeGenesisConfiguration};
use sp_runtime::traits::Block as BlockT;

const BABE_EPOCH_CHANGES_VERSION: &[u8] = b"babe_session_changes_version";
const BABE_EPOCH_CHANGES_KEY: &[u8] = b"babe_session_changes";
const BABE_EPOCH_CHANGES_CURRENT_VERSION: u32 = 3;

/// The aux storage key used to store the block weight of the given block hash.
pub fn block_weight_key<H: Encode>(block_hash: H) -> Vec<u8> {
	(b"block_weight", block_hash).encode()
}

fn load_decode<B, T>(backend: &B, key: &[u8]) -> ClientResult<Option<T>>
where
	B: AuxStore,
	T: Decode,
{
	let corrupt = |e: codec::Error| {
		ClientError::Backend(format!("BABE DB is corrupted. Decode error: {}", e))
	};
	match backend.get_aux(key)? {
		None => Ok(None),
		Some(t) => T::decode(&mut &t[..]).map(Some).map_err(corrupt),
	}
}

/// Load or initialize persistent session change data from backend.
pub fn load_session_changes<Block: BlockT, B: AuxStore>(
	backend: &B,
	config: &BabeGenesisConfiguration,
) -> ClientResult<SharedSessionChanges<Block, Session>> {
	let version = load_decode::<_, u32>(backend, BABE_EPOCH_CHANGES_VERSION)?;

	let maybe_session_changes = match version {
		None =>
			load_decode::<_, SessionChangesV0For<Block, SessionV0>>(backend, BABE_EPOCH_CHANGES_KEY)?
				.map(|v0| v0.migrate().map(|_, _, session| session.migrate(config))),
		Some(1) =>
			load_decode::<_, SessionChangesV1For<Block, SessionV0>>(backend, BABE_EPOCH_CHANGES_KEY)?
				.map(|v1| v1.migrate().map(|_, _, session| session.migrate(config))),
		Some(2) => {
			// v2 still uses `SessionChanges` v1 format but with a different `Session` type.
			load_decode::<_, SessionChangesV1For<Block, Session>>(backend, BABE_EPOCH_CHANGES_KEY)?
				.map(|v2| v2.migrate())
		},
		Some(BABE_EPOCH_CHANGES_CURRENT_VERSION) =>
			load_decode::<_, SessionChangesFor<Block, Session>>(backend, BABE_EPOCH_CHANGES_KEY)?,
		Some(other) =>
			return Err(ClientError::Backend(format!("Unsupported BABE DB version: {:?}", other))),
	};

	let session_changes =
		SharedSessionChanges::<Block, Session>::new(maybe_session_changes.unwrap_or_else(|| {
			info!(
				target: "babe",
				"👶 Creating empty BABE session changes on what appears to be first startup.",
			);
			SessionChangesFor::<Block, Session>::default()
		}));

	// rebalance the tree after deserialization. this isn't strictly necessary
	// since the tree is now rebalanced on every update operation. but since the
	// tree wasn't rebalanced initially it's useful to temporarily leave it here
	// to avoid having to wait until an import for rebalancing.
	session_changes.shared_data().rebalance();

	Ok(session_changes)
}

/// Update the session changes on disk after a change.
pub(crate) fn write_session_changes<Block: BlockT, F, R>(
	session_changes: &SessionChangesFor<Block, Session>,
	write_aux: F,
) -> R
where
	F: FnOnce(&[(&'static [u8], &[u8])]) -> R,
{
	BABE_EPOCH_CHANGES_CURRENT_VERSION.using_encoded(|version| {
		let encoded_session_changes = session_changes.encode();
		write_aux(&[
			(BABE_EPOCH_CHANGES_KEY, encoded_session_changes.as_slice()),
			(BABE_EPOCH_CHANGES_VERSION, version),
		])
	})
}

/// Write the cumulative chain-weight of a block ot aux storage.
pub(crate) fn write_block_weight<H: Encode, F, R>(
	block_hash: H,
	block_weight: BabeBlockWeight,
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
) -> ClientResult<Option<BabeBlockWeight>> {
	load_decode(backend, block_weight_key(block_hash).as_slice())
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::migration::SessionV0;
	use fork_tree::ForkTree;
	use sc_consensus_sessions::{SessionHeader, PersistedSession, PersistedSessionHeader};
	use sc_network_test::Block as TestBlock;
	use sp_consensus::Error as ConsensusError;
	use sp_consensus_babe::{AllowedSlots, BabeGenesisConfiguration};
	use sp_core::H256;
	use sp_runtime::traits::NumberFor;
	use substrate_test_runtime_client;

	#[test]
	fn load_decode_from_v0_session_changes() {
		let session = SessionV0 {
			start_slot: 0.into(),
			authorities: vec![],
			randomness: [0; 32],
			session_index: 1,
			duration: 100,
		};
		let client = substrate_test_runtime_client::new();
		let mut v0_tree = ForkTree::<H256, NumberFor<TestBlock>, _>::new();
		v0_tree
			.import::<_, ConsensusError>(
				Default::default(),
				Default::default(),
				PersistedSession::Regular(session),
				&|_, _| Ok(false), // Test is single item only so this can be set to false.
			)
			.unwrap();

		client
			.insert_aux(
				&[(
					BABE_EPOCH_CHANGES_KEY,
					&SessionChangesV0For::<TestBlock, SessionV0>::from_raw(v0_tree).encode()[..],
				)],
				&[],
			)
			.unwrap();

		assert_eq!(load_decode::<_, u32>(&client, BABE_EPOCH_CHANGES_VERSION).unwrap(), None);

		let session_changes = load_session_changes::<TestBlock, _>(
			&client,
			&BabeGenesisConfiguration {
				slot_duration: 10,
				session_length: 4,
				c: (3, 10),
				genesis_authorities: Vec::new(),
				randomness: Default::default(),
				allowed_slots: AllowedSlots::PrimaryAndSecondaryPlainSlots,
			},
		)
		.unwrap();

		assert!(
			session_changes
				.shared_data()
				.tree()
				.iter()
				.map(|(_, _, session)| session.clone())
				.collect::<Vec<_>>() ==
				vec![PersistedSessionHeader::Regular(SessionHeader {
					start_slot: 0.into(),
					end_slot: 100.into(),
				})],
		); // PersistedSessionHeader does not implement Debug, so we use assert! directly.

		write_session_changes::<TestBlock, _, _>(&session_changes.shared_data(), |values| {
			client.insert_aux(values, &[]).unwrap();
		});

		assert_eq!(load_decode::<_, u32>(&client, BABE_EPOCH_CHANGES_VERSION).unwrap(), Some(3));
	}
}
