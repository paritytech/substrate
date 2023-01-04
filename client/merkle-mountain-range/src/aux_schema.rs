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

//! Schema for MMR-gadget state persisted in the aux-db.

use crate::LOG_TARGET;
use codec::{Decode, Encode};
use log::{info, trace};
use sc_client_api::backend::AuxStore;
use sp_blockchain::{Error as ClientError, Result as ClientResult};
use sp_runtime::traits::{Block, NumberFor};

const VERSION_KEY: &[u8] = b"mmr_auxschema_version";
const GADGET_STATE: &[u8] = b"mmr_gadget_state";

const CURRENT_VERSION: u32 = 1;
pub(crate) type PersistedState<B> = NumberFor<B>;

pub(crate) fn write_current_version<B: AuxStore>(backend: &B) -> ClientResult<()> {
	info!(target: LOG_TARGET, "write aux schema version {:?}", CURRENT_VERSION);
	AuxStore::insert_aux(backend, &[(VERSION_KEY, CURRENT_VERSION.encode().as_slice())], &[])
}

/// Write gadget state.
pub(crate) fn write_gadget_state<B: Block, BE: AuxStore>(
	backend: &BE,
	state: &PersistedState<B>,
) -> ClientResult<()> {
	trace!(target: LOG_TARGET, "persisting {:?}", state);
	backend.insert_aux(&[(GADGET_STATE, state.encode().as_slice())], &[])
}

fn load_decode<B: AuxStore, T: Decode>(backend: &B, key: &[u8]) -> ClientResult<Option<T>> {
	match backend.get_aux(key)? {
		None => Ok(None),
		Some(t) => T::decode(&mut &t[..])
			.map_err(|e| ClientError::Backend(format!("MMR aux DB is corrupted: {}", e)))
			.map(Some),
	}
}

/// Load persistent data from backend.
pub(crate) fn load_state<B, BE>(backend: &BE) -> ClientResult<Option<PersistedState<B>>>
where
	B: Block,
	BE: AuxStore,
{
	let version: Option<u32> = load_decode(backend, VERSION_KEY)?;

	match version {
		None => (),
		Some(1) => return load_decode::<_, PersistedState<B>>(backend, GADGET_STATE),
		other =>
			return Err(ClientError::Backend(format!("Unsupported MMR aux DB version: {:?}", other))),
	}

	// No persistent state found in DB.
	Ok(None)
}

/// Load or initialize persistent data from backend.
pub(crate) fn load_or_init_state<B, BE>(
	backend: &BE,
	default: NumberFor<B>,
) -> sp_blockchain::Result<NumberFor<B>>
where
	B: Block,
	BE: AuxStore,
{
	// Initialize gadget best_canon from AUX DB or from pallet genesis.
	if let Some(best) = load_state::<B, BE>(backend)? {
		info!(target: LOG_TARGET, "Loading MMR best canonicalized state from db: {:?}.", best);
		Ok(best)
	} else {
		info!(
			target: LOG_TARGET,
			"Loading MMR from pallet genesis on what appears to be the first startup: {:?}.",
			default
		);
		write_current_version(backend)?;
		write_gadget_state::<B, BE>(backend, &default)?;
		Ok(default)
	}
}

#[cfg(test)]
pub(crate) mod tests {
	use super::*;
	use crate::test_utils::{run_test_with_mmr_gadget_pre_post_using_client, MmrBlock, MockClient};
	use parking_lot::Mutex;
	use sp_runtime::generic::BlockId;
	use std::{sync::Arc, time::Duration};
	use substrate_test_runtime_client::{runtime::Block, Backend};

	#[test]
	fn should_load_persistent_sanity_checks() {
		let client = MockClient::new();
		let backend = &*client.backend;

		// version not available in db -> None
		assert_eq!(load_state::<Block, Backend>(backend).unwrap(), None);

		// populate version in db
		write_current_version(backend).unwrap();
		// verify correct version is retrieved
		assert_eq!(load_decode(backend, VERSION_KEY).unwrap(), Some(CURRENT_VERSION));

		// version is available in db but state isn't -> None
		assert_eq!(load_state::<Block, Backend>(backend).unwrap(), None);
	}

	#[test]
	fn should_persist_progress_across_runs() {
		sp_tracing::try_init_simple();

		let client = Arc::new(MockClient::new());
		let backend = client.backend.clone();

		// version not available in db -> None
		assert_eq!(load_decode::<Backend, Option<u32>>(&*backend, VERSION_KEY).unwrap(), None);
		// state not available in db -> None
		assert_eq!(load_state::<Block, Backend>(&*backend).unwrap(), None);
		// run the gadget while importing and finalizing 3 blocks
		run_test_with_mmr_gadget_pre_post_using_client(
			client.clone(),
			|_| async {},
			|client| async move {
				let a1 = client.import_block(&BlockId::Number(0), b"a1", Some(0)).await;
				let a2 = client.import_block(&BlockId::Number(1), b"a2", Some(1)).await;
				let a3 = client.import_block(&BlockId::Number(2), b"a3", Some(2)).await;
				client.finalize_block(a3.hash(), Some(3));
				tokio::time::sleep(Duration::from_millis(200)).await;
				// a1, a2, a3 were canonicalized
				client.assert_canonicalized(&[&a1, &a2, &a3]);
			},
		);

		// verify previous progress was persisted and run the gadget again
		run_test_with_mmr_gadget_pre_post_using_client(
			client.clone(),
			|client| async move {
				let backend = &*client.backend;
				// check there is both version and best canon available in db before running gadget
				assert_eq!(load_decode(backend, VERSION_KEY).unwrap(), Some(CURRENT_VERSION));
				assert_eq!(load_state::<Block, Backend>(backend).unwrap(), Some(3));
			},
			|client| async move {
				let a4 = client.import_block(&BlockId::Number(3), b"a4", Some(3)).await;
				let a5 = client.import_block(&BlockId::Number(4), b"a5", Some(4)).await;
				let a6 = client.import_block(&BlockId::Number(5), b"a6", Some(5)).await;
				client.finalize_block(a6.hash(), Some(6));
				tokio::time::sleep(Duration::from_millis(200)).await;

				// a4, a5, a6 were canonicalized
				client.assert_canonicalized(&[&a4, &a5, &a6]);
				// check persisted best canon was updated
				assert_eq!(load_state::<Block, Backend>(&*client.backend).unwrap(), Some(6));
			},
		);
	}

	#[test]
	fn should_resume_from_persisted_state() {
		sp_tracing::try_init_simple();

		let client = Arc::new(MockClient::new());
		let blocks = Arc::new(Mutex::new(Vec::<MmrBlock>::new()));
		let blocks_clone = blocks.clone();

		// run the gadget while importing and finalizing 3 blocks
		run_test_with_mmr_gadget_pre_post_using_client(
			client.clone(),
			|_| async {},
			|client| async move {
				let mut blocks = blocks_clone.lock();
				blocks.push(client.import_block(&BlockId::Number(0), b"a1", Some(0)).await);
				blocks.push(client.import_block(&BlockId::Number(1), b"a2", Some(1)).await);
				blocks.push(client.import_block(&BlockId::Number(2), b"a3", Some(2)).await);
				client.finalize_block(blocks.last().unwrap().hash(), Some(3));
				tokio::time::sleep(Duration::from_millis(200)).await;
				// a1, a2, a3 were canonicalized
				let slice: Vec<&MmrBlock> = blocks.iter().collect();
				client.assert_canonicalized(&slice);

				// now manually move them back to non-canon/temp location
				for mmr_block in slice {
					client.undo_block_canonicalization(mmr_block)
				}
			},
		);

		let blocks_clone = blocks.clone();
		// verify new gadget continues from block 4 and ignores 1, 2, 3 based on persisted state
		run_test_with_mmr_gadget_pre_post_using_client(
			client.clone(),
			|client| async move {
				let blocks = blocks_clone.lock();
				let slice: Vec<&MmrBlock> = blocks.iter().collect();

				// verify persisted state says a1, a2, a3 were canonicalized,
				assert_eq!(load_state::<Block, Backend>(&*client.backend).unwrap(), Some(3));
				// but actually they are NOT canon (we manually reverted them earlier).
				client.assert_not_canonicalized(&slice);
			},
			|client| async move {
				let a4 = client.import_block(&BlockId::Number(3), b"a4", Some(3)).await;
				let a5 = client.import_block(&BlockId::Number(4), b"a5", Some(4)).await;
				let a6 = client.import_block(&BlockId::Number(5), b"a6", Some(5)).await;
				client.finalize_block(a6.hash(), Some(6));
				tokio::time::sleep(Duration::from_millis(200)).await;

				let block_1_to_3 = blocks.lock();
				let slice: Vec<&MmrBlock> = block_1_to_3.iter().collect();
				// verify a1, a2, a3 are still NOT canon (skipped by gadget based on data in aux db)
				client.assert_not_canonicalized(&slice);
				// but a4, a5, a6 were canonicalized
				client.assert_canonicalized(&[&a4, &a5, &a6]);
				// check persisted best canon was updated
				assert_eq!(load_state::<Block, Backend>(&*client.backend).unwrap(), Some(6));
			},
		);
	}
}
