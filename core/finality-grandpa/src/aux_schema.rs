// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Schema for stuff in the aux-db.

use codec::{Encode, Decode};
use client::backend::AuxStore;
use client::error::{Result as ClientResult, ErrorKind as ClientErrorKind};
use grandpa::round::State as RoundState;
use substrate_primitives::Ed25519AuthorityId;

use authorities::{AuthoritySet, SharedAuthoritySet, PendingChange, DelayKind};
use consensus_changes::{SharedConsensusChanges, ConsensusChanges};
use std::sync::Arc;

pub(crate) const VERSION_KEY: &[u8] = b"grandpa_schema_version";
pub(crate) const LAST_COMPLETED_KEY: &[u8] = b"grandpa_completed_round";
pub(crate) const AUTHORITY_SET_KEY: &[u8] = b"grandpa_voters";
pub(crate) const CONSENSUS_CHANGES_KEY: &[u8] = b"grandpa_consensus_changes";

const CURRENT_VERSION: u32 = 1;
const INITIAL_VERSION: u32 = 0;

/// The voter set state.
#[derive(Clone, Encode, Decode)]
pub enum VoterSetState<H, N> {
	/// The voter set state, currently paused.
	Paused(u64, RoundState<H, N>),
	/// The voter set state, currently live.
	Live(u64, RoundState<H, N>),
}

type V0VoterSetState<H, N> = (u64, RoundState<H, N>);

#[derive(Debug, Clone, Encode, Decode, PartialEq)]
struct V0PendingChange<H, N> {
	next_authorities: Vec<(Ed25519AuthorityId, u64)>,
	delay: N,
	canon_height: N,
	canon_hash: H,
}

#[derive(Debug, Clone, Encode, Decode, PartialEq)]
struct V0AuthoritySet<H, N> {
	current_authorities: Vec<(Ed25519AuthorityId, u64)>,
	set_id: u64,
	pending_changes: Vec<V0PendingChange<H, N>>,
}

impl<H, N> Into<AuthoritySet<H, N>> for V0AuthoritySet<H, N> {
	fn into(self) -> AuthoritySet<H, N> {
		AuthoritySet {
			current_authorities: self.current_authorities,
			paused: false,
			set_id: self.set_id,
			pending_changes: self.pending_changes.into_iter().map(|old_change| PendingChange {
				next_authorities: old_change.next_authorities,
				delay: old_change.delay,
				canon_height: old_change.canon_height,
				canon_hash: old_change.canon_hash,
				delay_kind: DelayKind::Finalized,
			}).collect()
		}
	}
}

fn load_decode<B: AuxStore, T: Decode>(backend: &B, key: &[u8]) -> ClientResult<Option<T>> {
	match backend.get_aux(key)? {
		None => Ok(None),
		Some(t) => T::decode(&mut &t[..])
			.ok_or_else(
				|| ClientErrorKind::Backend(format!("GRANDPA DB is corrupted.")).into(),
			)
			.map(Some)
	}
}

/// Persistent data kept between runs.
pub(crate) struct PersistentData<H, N> {
	pub(crate) authority_set: SharedAuthoritySet<H, N>,
	pub(crate) consensus_changes: SharedConsensusChanges<H, N>,
	pub(crate) set_state: VoterSetState<H, N>,
}

/// Load or initialize persistent data from backend.
pub(crate) fn load_persistent<B, H, N, G>(
	backend: &B,
	genesis_hash: H,
	genesis_number: N,
	genesis_authorities: G,
)
	-> ClientResult<PersistentData<H, N>>
	where
		B: AuxStore,
		H: Decode + Encode + Clone,
		N: Decode + Encode + Clone,
		G: FnOnce() -> ClientResult<Vec<(Ed25519AuthorityId, u64)>>
{
	let version: Option<u64> = load_decode(backend, VERSION_KEY)?;
	let consensus_changes = load_decode(backend, CONSENSUS_CHANGES_KEY)?
		.unwrap_or_else(ConsensusChanges::<H, N>::empty);

	let make_genesis_round = move || RoundState::genesis((genesis_hash, genesis_number));

	match version {
		None => {
			CURRENT_VERSION.using_encoded(|s|
				backend.insert_aux(&[(VERSION_KEY, s)], &[])
			)?;

			if let Some(old_set) = load_decode::<_, V0AuthoritySet<H, N>>(backend, AUTHORITY_SET_KEY)? {
				let new_set: AuthoritySet<H, N> = old_set.into();
				backend.insert_aux(&[(AUTHORITY_SET_KEY, new_set.encode().as_slice())], &[])?;

				let set_state = match load_decode::<_, V0VoterSetState<H, N>>(backend, LAST_COMPLETED_KEY)? {
					Some((number, state)) => VoterSetState::Live(number, state),
					None => VoterSetState::Live(0, make_genesis_round()),
				};

				return Ok(PersistentData {
					authority_set: new_set.into(),
					consensus_changes: Arc::new(consensus_changes.into()),
					set_state,
				});
			}
		}
		Some(1) => {
			if let Some(set) = load_decode::<_, AuthoritySet<H, N>>(backend, AUTHORITY_SET_KEY)? {
				let set_state = match load_decode::<_, VoterSetState<H, N>>(backend, LAST_COMPLETED_KEY)? {
					Some(state) => state,
					None => VoterSetState::Live(0, make_genesis_round()),
				};

				return Ok(PersistentData {
					authority_set: set.into(),
					consensus_changes: Arc::new(consensus_changes.into()),
					set_state,
				});
			}
		}
		Some(other) => return Err(ClientErrorKind::Backend(
			format!("Unsupported GRANDPA DB version: {:?}", other)
		).into()),
	}

	// genesis.
	info!(target: "afg", "Loading GRANDPA authority set \
		from genesis on what appears to be first startup.");

	let genesis_set = AuthoritySet::genesis(genesis_authorities()?);
	let genesis_state = VoterSetState::Live(0, make_genesis_round());
	backend.insert_aux(
		&[
			(AUTHORITY_SET_KEY, genesis_set.encode().as_slice()),
			(LAST_COMPLETED_KEY, genesis_state.encode().as_slice()),
		],
		&[],
	)?;

	Ok(PersistentData {
		authority_set: genesis_set.into(),
		set_state: genesis_state,
		consensus_changes: Arc::new(consensus_changes.into()),
	})
}

/// Execute a closure with the
pub(crate) fn authority_set_update<H: Encode, N: Encode, F>(set: &AuthoritySet<H, N>, f: F)
	where F: FnOnce(&[u8], &[u8])
{
	f(AUTHORITY_SET_KEY, set.encode().as_slice())
}

pub(crate) fn set_state_update<H: Encode, N: Encode, F>(set_state: &VoterSetState<H, N>, f: F)
	where F: FnOnce(&[u8], &[u8])
{
	f(LAST_COMPLETED_KEY, set_state.encode().as_slice())
}
