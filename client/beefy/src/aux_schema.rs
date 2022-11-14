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
use beefy_primitives::{crypto::AuthorityId, ValidatorSet};
use codec::{Decode, Encode};
use log::info;
use sc_client_api::{backend::AuxStore, Backend};
use sp_blockchain::{Error as ClientError, Result as ClientResult};
use sp_runtime::traits::{Block as BlockT, NumberFor, One};

const VERSION_KEY: &[u8] = b"beefy_auxschema_version";
const WORKER_STATE: &[u8] = b"beefy_voter_state";
// const BEST_JUSTIFICATION: &[u8] = b"beefy_best_justification";

const CURRENT_VERSION: u32 = 1;

/// Write BEEFY DB aux schema version.
pub(crate) fn set_db_version<BE: AuxStore>(backend: &BE) -> ClientResult<()> {
	backend.insert_aux(&[(VERSION_KEY, CURRENT_VERSION.encode().as_slice())], &[])
}

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
pub(crate) fn load_persistent<Block: BlockT, BE, G>(
	backend: &BE,
	best_grandpa_header: <Block as BlockT>::Header,
	genesis_number: NumberFor<Block>,
	genesis_validator_set: G,
	min_block_delta: u32,
) -> ClientResult<PersistedState<Block>>
where
	BE: Backend<Block>,
	G: FnOnce() -> ClientResult<ValidatorSet<AuthorityId>>,
{
	let version: Option<u32> = load_decode(backend, VERSION_KEY)?;

	match version {
		None => set_db_version(backend)?,
		Some(1) => {
			if let Some(state) = load_decode::<_, PersistedState<Block>>(backend, WORKER_STATE)? {
				return Ok(state)
			}
		},
		other =>
			return Err(ClientError::Backend(format!("Unsupported BEEFY DB version: {:?}", other))),
	}

	// genesis.
	info!(target: "beefy", "🥩 Loading BEEFY voter state \
		from genesis on what appears to be first startup.");

	// TODO: use these to initialize voter rounds
	let _genesis_session_start = genesis_number.max(One::one());
	let _genesis_set = genesis_validator_set()?;

	Ok(PersistedState::new(best_grandpa_header, genesis_number, min_block_delta))
}
