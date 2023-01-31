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

use crate::{worker::PersistedState, LOG_TARGET};
use codec::{Decode, Encode};
use log::{info, trace};
use sc_client_api::{backend::AuxStore, Backend};
use sp_blockchain::{Error as ClientError, Result as ClientResult};
use sp_runtime::traits::Block as BlockT;

const VERSION_KEY: &[u8] = b"beefy_auxschema_version";
const WORKER_STATE: &[u8] = b"beefy_voter_state";

const CURRENT_VERSION: u32 = 1;

pub(crate) fn write_current_version<B: AuxStore>(backend: &B) -> ClientResult<()> {
	info!(target: LOG_TARGET, "🥩 write aux schema version {:?}", CURRENT_VERSION);
	AuxStore::insert_aux(backend, &[(VERSION_KEY, CURRENT_VERSION.encode().as_slice())], &[])
}

/// Write voter state.
pub(crate) fn write_voter_state<Block: BlockT, B: AuxStore>(
	backend: &B,
	state: &PersistedState<Block>,
) -> ClientResult<()> {
	trace!(target: LOG_TARGET, "🥩 persisting {:?}", state);
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
	use crate::tests::BeefyTestNet;
	use sc_network_test::TestNetFactory;

	// also used in tests.rs
	pub fn verify_persisted_version<B: BlockT, BE: Backend<B>>(backend: &BE) -> bool {
		let version: u32 = load_decode(backend, VERSION_KEY).unwrap().unwrap();
		version == CURRENT_VERSION
	}

	#[tokio::test]
	async fn should_load_persistent_sanity_checks() {
		let mut net = BeefyTestNet::new(1);
		let backend = net.peer(0).client().as_backend();

		// version not available in db -> None
		assert_eq!(load_persistent(&*backend).unwrap(), None);

		// populate version in db
		write_current_version(&*backend).unwrap();
		// verify correct version is retrieved
		assert_eq!(load_decode(&*backend, VERSION_KEY).unwrap(), Some(CURRENT_VERSION));

		// version is available in db but state isn't -> None
		assert_eq!(load_persistent(&*backend).unwrap(), None);

		// full `PersistedState` load is tested in `tests.rs`.
	}
}
