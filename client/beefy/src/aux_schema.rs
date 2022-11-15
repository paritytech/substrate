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

//! Schema for BEEFY state persisted in the aux-db.

use crate::worker::PersistedState;
use beefy_primitives::{
	crypto::AuthorityId, BeefyApi, ValidatorSet, BEEFY_ENGINE_ID, GENESIS_AUTHORITY_SET_ID,
};
use codec::{Decode, Encode};
use futures::{stream::Fuse, StreamExt};
use log::{debug, info, trace};
use sc_client_api::{backend::AuxStore, Backend, FinalityNotifications};
use sc_network_gossip::GossipEngine;
use sp_api::{BlockId, HeaderT, ProvideRuntimeApi};
use sp_blockchain::{
	Backend as BlockBackend, Error as ClientError, HeaderBackend, Result as ClientResult,
};
use sp_runtime::traits::{Block as BlockT, Zero};

const VERSION_KEY: &[u8] = b"beefy_auxschema_version";
const WORKER_STATE: &[u8] = b"beefy_voter_state";

const CURRENT_VERSION: u32 = 1;

/// Write voter state.
pub(crate) fn write_voter_state<Block: BlockT, B: AuxStore>(
	backend: &B,
	state: &PersistedState<Block>,
) -> ClientResult<()> {
	backend.insert_aux(&[(WORKER_STATE, state.encode().as_slice())], &[])
}

fn load_decode<B: AuxStore, T: Decode>(backend: &B, key: &[u8]) -> ClientResult<Option<T>> {
	match backend.get_aux(key)? {
		None => Ok(None),
		Some(t) => T::decode(&mut &t[..])
			.map_err(|e| ClientError::Backend(format!("BEEFY DB is corrupted: {}", e)))
			.map(Some),
	}
}

/// Load or initialize persistent data from backend.
pub(crate) async fn load_persistent<B, BE, R>(
	backend: &BE,
	runtime: &R,
	gossip_engine: &mut GossipEngine<B>,
	finality: &mut Fuse<FinalityNotifications<B>>,
	min_block_delta: u32,
) -> ClientResult<PersistedState<B>>
where
	B: BlockT,
	BE: Backend<B>,
	R: ProvideRuntimeApi<B>,
	R::Api: BeefyApi<B>,
{
	let version: Option<u32> = load_decode(backend, VERSION_KEY)?;

	match version {
		None => (),
		Some(1) =>
			if let Some(mut state) = load_decode::<_, PersistedState<B>>(backend, WORKER_STATE)? {
				// Overwrite persisted data with newly provided `min_block_delta`.
				state.set_min_block_delta(min_block_delta);
				return Ok(state)
			},
		other =>
			return Err(ClientError::Backend(format!("Unsupported BEEFY DB version: {:?}", other))),
	}

	// If no persisted state present, start at the latest session boundary with BEEFY finality.
	// TODO: we should actually start at pallet-beefy "genesis", but we don't know when that was,
	// so we walk back the chain up to a session length.
	migrate_from_version0(backend, runtime, gossip_engine, finality, min_block_delta).await
}

async fn migrate_from_version0<B, BE, R>(
	backend: &BE,
	runtime: &R,
	gossip_engine: &mut GossipEngine<B>,
	finality: &mut Fuse<FinalityNotifications<B>>,
	min_block_delta: u32,
) -> ClientResult<PersistedState<B>>
where
	B: BlockT,
	BE: Backend<B>,
	R: ProvideRuntimeApi<B>,
	R::Api: BeefyApi<B>,
{
	AuxStore::insert_aux(backend, &[(VERSION_KEY, CURRENT_VERSION.encode().as_slice())], &[])?;

	let (active, mut header) = wait_for_runtime_pallet(runtime.clone(), gossip_engine, finality)
		.await
		.ok_or_else(|| ClientError::Backend("Gossip engine has terminated.".into()))?;

	if active.id() == GENESIS_AUTHORITY_SET_ID {
		info!(
			target: "beefy",
			"🥩 Loading BEEFY voter state from genesis on what appears to be first startup. \
			Starting voting rounds at block {:?}.",
			*header.number()
		);
		return Ok(PersistedState::initialize(
			header.clone(),
			Zero::zero(),
			*header.number(),
			active,
			min_block_delta,
		))
	}

	// Walk back the imported blocks and initialize voter either, at the last block with
	// a BEEFY justification, or at current session's boundary; voter will resume from there.
	let blockchain = backend.blockchain();
	let state = loop {
		if let Some(true) = blockchain
			.justifications(header.hash())
			.ok()
			.flatten()
			.map(|justifs| justifs.get(BEEFY_ENGINE_ID).is_some())
		{
			info!(
				target: "beefy",
				"🥩 Initialize BEEFY voter at last BEEFY finalized block: {:?}.",
				*header.number()
			);
			let mut state = PersistedState::initialize(
				header.clone(),
				*header.number(),
				*header.number(),
				active,
				min_block_delta,
			);
			// Mark the round as already finalized.
			if let Some(round) = state.active_round_mut() {
				round.conclude(*header.number());
			}
			break state
		}

		if let Some(active) = crate::worker::find_authorities_change::<B>(&header) {
			info!(
				target: "beefy",
				"🥩 Initialize BEEFY voter at current session boundary: {:?}.",
				*header.number()
			);
			let state = PersistedState::initialize(
				header.clone(),
				Zero::zero(),
				*header.number(),
				active,
				min_block_delta,
			);
			break state
		}

		// Move up the chain.
		header = blockchain.expect_header(BlockId::Hash(*header.parent_hash()))?;
	};

	write_voter_state(backend, &state)?;
	Ok(state)
}

/// Wait for BEEFY runtime pallet to be available, return active validator set.
/// Should be called only once during worker initialization.
async fn wait_for_runtime_pallet<B, R>(
	runtime: &R,
	mut gossip_engine: &mut GossipEngine<B>,
	finality: &mut Fuse<FinalityNotifications<B>>,
) -> Option<(ValidatorSet<AuthorityId>, <B as BlockT>::Header)>
where
	B: BlockT,
	R: ProvideRuntimeApi<B>,
	R::Api: BeefyApi<B>,
{
	loop {
		futures::select! {
			notif = finality.next() => {
				let notif = match notif {
					Some(notif) => notif,
					None => break
				};
				let at = BlockId::hash(notif.header.hash());
				if let Some(active) = runtime.runtime_api().validator_set(&at).ok().flatten() {
					// TODO (issue #XXX):
					// Beefy pallet available, return active validator set.
					return Some((active, notif.header))
				} else {
					trace!(target: "beefy", "🥩 Finality notification: {:?}", notif);
					debug!(target: "beefy", "🥩 Waiting for BEEFY pallet to become available...");
				}
			},
			_ = gossip_engine => {
				break
			}
		}
	}
	None
}

#[cfg(test)]
pub(crate) mod tests {
	// #[test]
	// fn should_initialize_voter_correctly() {
	// 	let keys = &[Keyring::Alice];
	// 	let validator_set = ValidatorSet::new(make_beefy_ids(keys), 1).unwrap();
	// 	let mut net = BeefyTestNet::new(1);
	// 	let backend = net.peer(0).client().as_backend();
	//
	// 	// push 15 blocks with `AuthorityChange` digests every 10 blocks
	// 	net.generate_blocks_and_sync(15, 10, &validator_set, false);
	// 	// finalize 13 without justifications
	// 	let hashof13 =
	// 		backend.blockchain().expect_block_hash_from_id(&BlockId::Number(13)).unwrap();
	// 	net.peer(0).client().as_client().finalize_block(hashof13, None).unwrap();
	//
	// 	// Test initialization at session boundary.
	// 	{
	// 		let mut worker = create_beefy_worker(&net.peer(0), &keys[0], 1);
	//
	// 		// initialize voter at block 13, expect rounds initialized at session_start = 10
	// 		let header = backend.blockchain().header(BlockId::number(13)).unwrap().unwrap();
	// 		worker.initialize_voter(&header, validator_set.clone());
	//
	// 		// verify voter initialized with single session starting at block 10
	// 		assert_eq!(worker.voting_oracle().sessions.len(), 1);
	// 		let rounds = worker.active_round().unwrap();
	// 		assert_eq!(rounds.session_start(), 10);
	// 		assert_eq!(rounds.validator_set_id(), validator_set.id());
	//
	// 		// verify next vote target is mandatory block 10
	// 		assert_eq!(worker.best_beefy_block(), 0);
	// 		assert_eq!(worker.best_grandpa_block(), 13);
	// 		assert_eq!(
	// 			worker.voting_oracle().voting_target(worker.best_beefy_block(), 13),
	// 			Some(10)
	// 		);
	// 	}
	//
	// 	// Test corner-case where session boundary == last beefy finalized.
	// 	{
	// 		let mut worker = create_beefy_worker(&net.peer(0), &keys[0], 1);
	//
	// 		// import/append BEEFY justification for session boundary block 10
	// 		let commitment = Commitment {
	// 			payload: Payload::from_single_entry(known_payloads::MMR_ROOT_ID, vec![]),
	// 			block_number: 10,
	// 			validator_set_id: validator_set.id(),
	// 		};
	// 		let justif = VersionedFinalityProof::<_, Signature>::V1(SignedCommitment {
	// 			commitment,
	// 			signatures: vec![None],
	// 		});
	// 		let hashof10 =
	// 			backend.blockchain().expect_block_hash_from_id(&BlockId::Number(10)).unwrap();
	// 		backend
	// 			.append_justification(hashof10, (BEEFY_ENGINE_ID, justif.encode()))
	// 			.unwrap();
	//
	// 		// initialize voter at block 13, expect rounds initialized at last beefy finalized 10
	// 		let header = backend.blockchain().header(BlockId::number(13)).unwrap().unwrap();
	// 		worker.initialize_voter(&header, validator_set.clone());
	//
	// 		// verify voter initialized with single session starting at block 10
	// 		assert_eq!(worker.voting_oracle().sessions.len(), 1);
	// 		let rounds = worker.active_round().unwrap();
	// 		assert_eq!(rounds.session_start(), 10);
	// 		assert_eq!(rounds.validator_set_id(), validator_set.id());
	//
	// 		// verify next vote target is mandatory block 10
	// 		assert_eq!(worker.best_beefy_block(), 10);
	// 		assert_eq!(worker.best_grandpa_block(), 13);
	// 		assert_eq!(
	// 			worker.voting_oracle().voting_target(worker.best_beefy_block(), 13),
	// 			Some(12)
	// 		);
	// 	}
	//
	// 	// Test initialization at last BEEFY finalized.
	// 	{
	// 		let mut worker = create_beefy_worker(&net.peer(0), &keys[0], 1);
	//
	// 		// import/append BEEFY justification for block 12
	// 		let commitment = Commitment {
	// 			payload: Payload::from_single_entry(known_payloads::MMR_ROOT_ID, vec![]),
	// 			block_number: 12,
	// 			validator_set_id: validator_set.id(),
	// 		};
	// 		let justif = VersionedFinalityProof::<_, Signature>::V1(SignedCommitment {
	// 			commitment,
	// 			signatures: vec![None],
	// 		});
	// 		let hashof12 =
	// 			backend.blockchain().expect_block_hash_from_id(&BlockId::Number(12)).unwrap();
	// 		backend
	// 			.append_justification(hashof12, (BEEFY_ENGINE_ID, justif.encode()))
	// 			.unwrap();
	//
	// 		// initialize voter at block 13, expect rounds initialized at last beefy finalized 12
	// 		let header = backend.blockchain().header(BlockId::number(13)).unwrap().unwrap();
	// 		worker.initialize_voter(&header, validator_set.clone());
	//
	// 		// verify voter initialized with single session starting at block 12
	// 		assert_eq!(worker.voting_oracle().sessions.len(), 1);
	// 		let rounds = worker.active_round().unwrap();
	// 		assert_eq!(rounds.session_start(), 12);
	// 		assert_eq!(rounds.validator_set_id(), validator_set.id());
	//
	// 		// verify next vote target is 13
	// 		assert_eq!(worker.best_beefy_block(), 12);
	// 		assert_eq!(worker.best_grandpa_block(), 13);
	// 		assert_eq!(
	// 			worker.voting_oracle().voting_target(worker.best_beefy_block(), 13),
	// 			Some(13)
	// 		);
	// 	}
	// }
}
