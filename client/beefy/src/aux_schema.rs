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
const WORKER_STATE_KEY: &[u8] = b"beefy_voter_state";

const CURRENT_VERSION: u32 = 2;

pub(crate) fn write_current_version<BE: AuxStore>(backend: &BE) -> ClientResult<()> {
	info!(target: "beefy", "🥩 write aux schema version {:?}", CURRENT_VERSION);
	AuxStore::insert_aux(backend, &[(VERSION_KEY, CURRENT_VERSION.encode().as_slice())], &[])
}

/// Write voter state.
pub(crate) fn write_voter_state<B: BlockT, BE: AuxStore>(
	backend: &BE,
	state: &PersistedState<B>,
) -> ClientResult<()> {
	trace!(target: "beefy", "🥩 persisting {:?}", state);
	AuxStore::insert_aux(backend, &[(WORKER_STATE_KEY, state.encode().as_slice())], &[])
}

fn load_decode<BE: AuxStore, T: Decode>(backend: &BE, key: &[u8]) -> ClientResult<Option<T>> {
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
		Some(1) => return v1::migrate_from_version1::<B, _>(backend),
		Some(2) => return load_decode::<_, PersistedState<B>>(backend, WORKER_STATE_KEY),
		other =>
			return Err(ClientError::Backend(format!("Unsupported BEEFY DB version: {:?}", other))),
	}

	// No persistent state found in DB.
	Ok(None)
}

mod v1 {
	use super::*;
	use crate::{round::RoundTracker, worker::PersistedState, Rounds};
	use beefy_primitives::{
		crypto::{Public, Signature},
		Payload, ValidatorSet,
	};
	use sp_runtime::traits::NumberFor;
	use std::collections::{BTreeMap, VecDeque};

	#[derive(Decode)]
	struct V1RoundTracker {
		self_vote: bool,
		votes: BTreeMap<Public, Signature>,
	}

	impl Into<RoundTracker> for V1RoundTracker {
		fn into(self) -> RoundTracker {
			// make the compiler happy by using this deprecated field
			let _ = self.self_vote;
			RoundTracker::new(self.votes)
		}
	}

	#[derive(Decode)]
	struct V1Rounds<B: BlockT> {
		rounds: BTreeMap<(Payload, NumberFor<B>), V1RoundTracker>,
		session_start: NumberFor<B>,
		validator_set: ValidatorSet<Public>,
		mandatory_done: bool,
		best_done: Option<NumberFor<B>>,
	}

	impl<B> Into<Rounds<Payload, B>> for V1Rounds<B>
	where
		B: BlockT,
	{
		fn into(self) -> Rounds<Payload, B> {
			let rounds = self.rounds.into_iter().map(|it| (it.0, it.1.into())).collect();
			Rounds::<Payload, B>::new_manual(
				rounds,
				self.session_start,
				self.validator_set,
				self.mandatory_done,
				self.best_done,
			)
		}
	}

	#[derive(Decode)]
	pub(crate) struct V1VoterOracle<B: BlockT> {
		sessions: VecDeque<V1Rounds<B>>,
		min_block_delta: u32,
	}

	#[derive(Decode)]
	pub(crate) struct V1PersistedState<B: BlockT> {
		/// Best block we received a GRANDPA finality for.
		best_grandpa_block_header: <B as BlockT>::Header,
		/// Best block a BEEFY voting round has been concluded for.
		best_beefy_block: NumberFor<B>,
		/// Chooses which incoming votes to accept and which votes to generate.
		/// Keeps track of voting seen for current and future rounds.
		voting_oracle: V1VoterOracle<B>,
	}

	impl<B> TryInto<PersistedState<B>> for V1PersistedState<B>
	where
		B: BlockT,
	{
		type Error = ();
		fn try_into(self) -> Result<PersistedState<B>, Self::Error> {
			let Self { best_grandpa_block_header, best_beefy_block, voting_oracle } = self;
			let V1VoterOracle { sessions, min_block_delta } = voting_oracle;
			let sessions = sessions
				.into_iter()
				.map(<V1Rounds<B> as Into<Rounds<Payload, B>>>::into)
				.collect();
			PersistedState::checked_new(
				best_grandpa_block_header,
				best_beefy_block,
				sessions,
				min_block_delta,
			)
			.ok_or(())
		}
	}

	pub(super) fn migrate_from_version1<B: BlockT, BE>(
		backend: &BE,
	) -> ClientResult<Option<PersistedState<B>>>
	where
		B: BlockT,
		BE: Backend<B>,
	{
		write_current_version(backend)?;
		if let Some(new_state) = load_decode::<_, V1PersistedState<B>>(backend, WORKER_STATE_KEY)?
			.and_then(|old_state| old_state.try_into().ok())
		{
			write_voter_state(backend, &new_state)?;
			return Ok(Some(new_state))
		}
		Ok(None)
	}
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
