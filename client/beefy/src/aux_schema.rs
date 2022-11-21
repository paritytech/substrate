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
use codec::{Decode, Encode};
use log::{info, trace};
use sc_client_api::{backend::AuxStore, Backend};
use sp_blockchain::{Error as ClientError, Result as ClientResult};
use sp_runtime::traits::Block as BlockT;

const VERSION_KEY: &[u8] = b"beefy_auxschema_version";
const WORKER_STATE: &[u8] = b"beefy_voter_state";

const CURRENT_VERSION: u32 = 1;

pub(crate) fn write_current_version<B: AuxStore>(backend: &B) -> ClientResult<()> {
	info!(target: "beefy", "🥩 write aux schema version {:?}", CURRENT_VERSION);
	AuxStore::insert_aux(backend, &[(VERSION_KEY, CURRENT_VERSION.encode().as_slice())], &[])
}

/// Write voter state.
pub(crate) fn write_voter_state<Block: BlockT, B: AuxStore>(
	backend: &B,
	state: &PersistedState<Block>,
) -> ClientResult<()> {
	trace!(target: "beefy", "🥩 persisting {:?}", state);
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
pub(crate) fn load_persistent<B, BE>(backend: &BE) -> ClientResult<Option<PersistedState<B>>>
where
	B: BlockT,
	BE: Backend<B>,
{
	let version: Option<u32> = load_decode(backend, VERSION_KEY)?;

	match version {
		None => (),
		Some(1) => return load_decode::<_, PersistedState<B>>(backend, WORKER_STATE),
		other =>
			return Err(ClientError::Backend(format!("Unsupported BEEFY DB version: {:?}", other))),
	}

	// No persistent state found in DB.
	Ok(None)
}

#[cfg(test)]
pub(crate) mod tests {
	use super::*;
	use crate::{
		keystore::tests::Keyring,
		tests::{make_beefy_ids, BeefyTestNet},
		KnownPeers,
	};
	use beefy_primitives::{
		crypto::Signature, known_payloads, Commitment, Payload, SignedCommitment,
		VersionedFinalityProof,
	};
	use futures::executor::block_on;
	use parking_lot::Mutex;
	use sc_client_api::{Backend as BackendT, BlockchainEvents, HeaderBackend};
	use sc_network_test::TestNetFactory;
	use std::sync::Arc;
	use substrate_test_runtime_client::{runtime::Block, ClientExt};

	fn load_persistent_helper(
		net: &mut BeefyTestNet,
		finality: &mut Fuse<FinalityNotifications<Block>>,
	) -> PersistedState<Block> {
		let backend = net.peer(0).client().as_backend();
		let api = Arc::new(crate::tests::two_validators::TestApi {});
		let known_peers = Arc::new(Mutex::new(KnownPeers::new()));
		let gossip_validator =
			Arc::new(crate::communication::gossip::GossipValidator::new(known_peers));
		let mut gossip_engine = sc_network_gossip::GossipEngine::new(
			net.peer(0).network_service().clone(),
			"/beefy/whatever",
			gossip_validator,
			None,
		);

		block_on(load_persistent(&*backend, &*api, &mut gossip_engine, finality, 1)).unwrap()
	}

	#[test]
	fn should_initialize_voter_at_genesis() {
		let keys = &[Keyring::Alice];
		let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
		let mut net = BeefyTestNet::new(1);
		let backend = net.peer(0).client().as_backend();

		// push 15 blocks with `AuthorityChange` digests every 10 blocks
		net.generate_blocks_and_sync(15, 10, &validator_set, false);

		let mut finality = net.peer(0).client().as_client().finality_notification_stream().fuse();

		// finalize 13 without justifications
		let hashof13 =
			backend.blockchain().expect_block_hash_from_id(&BlockId::Number(13)).unwrap();
		net.peer(0).client().as_client().finalize_block(hashof13, None).unwrap();

		// load persistent state - nothing in DB, should init at session boundary
		let persisted_state = load_persistent_helper(&mut net, &mut finality);

		// Test initialization at session boundary.
		// verify voter initialized with two sessions starting at blocks 1 and 10
		let sessions = persisted_state.voting_oracle().sessions();
		assert_eq!(sessions.len(), 2);
		assert_eq!(sessions[0].session_start(), 1);
		assert_eq!(sessions[1].session_start(), 10);
		let rounds = persisted_state.active_round().unwrap();
		assert_eq!(rounds.session_start(), 1);
		assert_eq!(rounds.validator_set_id(), validator_set.id());

		// verify next vote target is mandatory block 1
		assert_eq!(persisted_state.best_beefy_block(), 0);
		assert_eq!(persisted_state.best_grandpa_block(), 13);
		assert_eq!(
			persisted_state
				.voting_oracle()
				.voting_target(persisted_state.best_beefy_block(), 13),
			Some(1)
		);

		// verify state also saved to db
		let version: u32 = load_decode(&*backend, VERSION_KEY).unwrap().unwrap();
		assert_eq!(version, CURRENT_VERSION);
		let state = load_decode::<_, PersistedState<Block>>(&*backend, WORKER_STATE)
			.unwrap()
			.unwrap();
		assert_eq!(state, persisted_state);
	}

	#[test]
	fn should_initialize_voter_when_last_final_is_session_boundary() {
		let keys = &[Keyring::Alice];
		let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
		let mut net = BeefyTestNet::new(1);
		let backend = net.peer(0).client().as_backend();

		// push 15 blocks with `AuthorityChange` digests every 10 blocks
		net.generate_blocks_and_sync(15, 10, &validator_set, false);

		let mut finality = net.peer(0).client().as_client().finality_notification_stream().fuse();

		// finalize 13 without justifications
		let hashof13 =
			backend.blockchain().expect_block_hash_from_id(&BlockId::Number(13)).unwrap();
		net.peer(0).client().as_client().finalize_block(hashof13, None).unwrap();

		// import/append BEEFY justification for session boundary block 10
		let commitment = Commitment {
			payload: Payload::from_single_entry(known_payloads::MMR_ROOT_ID, vec![]),
			block_number: 10,
			validator_set_id: validator_set.id(),
		};
		let justif = VersionedFinalityProof::<_, Signature>::V1(SignedCommitment {
			commitment,
			signatures: vec![None],
		});
		let hashof10 =
			backend.blockchain().expect_block_hash_from_id(&BlockId::Number(10)).unwrap();
		backend
			.append_justification(hashof10, (BEEFY_ENGINE_ID, justif.encode()))
			.unwrap();

		// Test corner-case where session boundary == last beefy finalized,
		// expect rounds initialized at last beefy finalized 10.

		// load persistent state - nothing in DB, should init at session boundary
		let persisted_state = load_persistent_helper(&mut net, &mut finality);

		// verify voter initialized with single session starting at block 10
		assert_eq!(persisted_state.voting_oracle().sessions().len(), 1);
		let rounds = persisted_state.active_round().unwrap();
		assert_eq!(rounds.session_start(), 10);
		assert_eq!(rounds.validator_set_id(), validator_set.id());

		// verify block 10 is correctly marked as finalized
		assert_eq!(persisted_state.best_beefy_block(), 10);
		assert_eq!(persisted_state.best_grandpa_block(), 13);
		// verify next vote target is diff-power-of-two block 12
		assert_eq!(
			persisted_state
				.voting_oracle()
				.voting_target(persisted_state.best_beefy_block(), 13),
			Some(12)
		);

		// verify state also saved to db
		let version: u32 = load_decode(&*backend, VERSION_KEY).unwrap().unwrap();
		assert_eq!(version, CURRENT_VERSION);
		let state = load_decode::<_, PersistedState<Block>>(&*backend, WORKER_STATE)
			.unwrap()
			.unwrap();
		assert_eq!(state, persisted_state);
	}

	#[test]
	fn should_initialize_voter_at_latest_finalized() {
		let keys = &[Keyring::Alice];
		let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
		let mut net = BeefyTestNet::new(1);
		let backend = net.peer(0).client().as_backend();

		// push 15 blocks with `AuthorityChange` digests every 10 blocks
		net.generate_blocks_and_sync(15, 10, &validator_set, false);

		let mut finality = net.peer(0).client().as_client().finality_notification_stream().fuse();

		// finalize 13 without justifications
		let hashof13 =
			backend.blockchain().expect_block_hash_from_id(&BlockId::Number(13)).unwrap();
		net.peer(0).client().as_client().finalize_block(hashof13, None).unwrap();

		// import/append BEEFY justification for block 12
		let commitment = Commitment {
			payload: Payload::from_single_entry(known_payloads::MMR_ROOT_ID, vec![]),
			block_number: 12,
			validator_set_id: validator_set.id(),
		};
		let justif = VersionedFinalityProof::<_, Signature>::V1(SignedCommitment {
			commitment,
			signatures: vec![None],
		});
		let hashof12 =
			backend.blockchain().expect_block_hash_from_id(&BlockId::Number(12)).unwrap();
		backend
			.append_justification(hashof12, (BEEFY_ENGINE_ID, justif.encode()))
			.unwrap();

		// Test initialization at last BEEFY finalized.

		// load persistent state - nothing in DB, should init at last BEEFY finalized
		let persisted_state = load_persistent_helper(&mut net, &mut finality);

		// verify voter initialized with single session starting at block 12
		assert_eq!(persisted_state.voting_oracle().sessions().len(), 1);
		let rounds = persisted_state.active_round().unwrap();
		assert_eq!(rounds.session_start(), 12);
		assert_eq!(rounds.validator_set_id(), validator_set.id());

		// verify next vote target is 13
		assert_eq!(persisted_state.best_beefy_block(), 12);
		assert_eq!(persisted_state.best_grandpa_block(), 13);
		assert_eq!(
			persisted_state
				.voting_oracle()
				.voting_target(persisted_state.best_beefy_block(), 13),
			Some(13)
		);

		// verify state also saved to db
		let version: u32 = load_decode(&*backend, VERSION_KEY).unwrap().unwrap();
		assert_eq!(version, CURRENT_VERSION);
		let state = load_decode::<_, PersistedState<Block>>(&*backend, WORKER_STATE)
			.unwrap()
			.unwrap();
		assert_eq!(state, persisted_state);
	}
}
