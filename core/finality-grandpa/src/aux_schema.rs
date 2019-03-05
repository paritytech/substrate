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

use parity_codec::{Encode, Decode};
use client::backend::AuxStore;
use client::error::{Result as ClientResult, Error as ClientError, ErrorKind as ClientErrorKind};
use fork_tree::ForkTree;
use grandpa::round::State as RoundState;
use substrate_primitives::Ed25519AuthorityId;
use log::{info, warn};

use crate::authorities::{AuthoritySet, SharedAuthoritySet, PendingChange, DelayKind};
use crate::consensus_changes::{SharedConsensusChanges, ConsensusChanges};
use crate::NewAuthoritySet;

use std::fmt::Debug;
use std::sync::Arc;

const VERSION_KEY: &[u8] = b"grandpa_schema_version";
const SET_STATE_KEY: &[u8] = b"grandpa_completed_round";
const AUTHORITY_SET_KEY: &[u8] = b"grandpa_voters";
const CONSENSUS_CHANGES_KEY: &[u8] = b"grandpa_consensus_changes";

const CURRENT_VERSION: u32 = 1;

/// The voter set state.
#[derive(Clone, Encode, Decode)]
pub enum VoterSetState<H, N> {
	/// The voter set state, currently paused.
	Paused(u64, RoundState<H, N>),
	/// The voter set state, currently live.
	Live(u64, RoundState<H, N>),
}

impl<H: Clone, N: Clone> VoterSetState<H, N> {
	/// Yields the current state.
	pub(crate) fn round(&self) -> (u64, RoundState<H, N>) {
		match *self {
			VoterSetState::Paused(n, ref s) => (n, s.clone()),
			VoterSetState::Live(n, ref s) => (n, s.clone()),
		}
	}
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

impl<H, N> Into<AuthoritySet<H, N>> for V0AuthoritySet<H, N>
where H: Clone + Debug + PartialEq,
	  N: Clone + Debug + Ord,
{
	fn into(self) -> AuthoritySet<H, N> {
		let mut pending_standard_changes = ForkTree::new();

		for old_change in self.pending_changes {
			let new_change = PendingChange {
				next_authorities: old_change.next_authorities,
				delay: old_change.delay,
				canon_height: old_change.canon_height,
				canon_hash: old_change.canon_hash,
				delay_kind: DelayKind::Finalized,
			};

			if let Err(err) = pending_standard_changes.import::<_, ClientError>(
				new_change.canon_hash.clone(),
				new_change.canon_height.clone(),
				new_change,
				// previously we only supported at most one pending change per fork
				&|_, _| Ok(false),
			) {
				warn!(target: "afg", "Error migrating pending authority set change: {:?}.", err);
				warn!(target: "afg", "Node is in a potentially inconsistent state.");
			}
		}

		AuthoritySet {
			current_authorities: self.current_authorities,
			set_id: self.set_id,
			pending_forced_changes: Vec::new(),
			pending_standard_changes
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
		H: Debug + Decode + Encode + Clone + PartialEq,
		N: Debug + Decode + Encode + Clone + Ord,
		G: FnOnce() -> ClientResult<Vec<(Ed25519AuthorityId, u64)>>
{
	let version: Option<u32> = load_decode(backend, VERSION_KEY)?;
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

				let set_state = match load_decode::<_, V0VoterSetState<H, N>>(backend, SET_STATE_KEY)? {
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
				let set_state = match load_decode::<_, VoterSetState<H, N>>(backend, SET_STATE_KEY)? {
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
			(SET_STATE_KEY, genesis_state.encode().as_slice()),
		],
		&[],
	)?;

	Ok(PersistentData {
		authority_set: genesis_set.into(),
		set_state: genesis_state,
		consensus_changes: Arc::new(consensus_changes.into()),
	})
}

/// Update the authority set on disk after a change.
pub(crate) fn update_authority_set<H, N, F, R>(
	set: &AuthoritySet<H, N>,
	new_set: Option<&NewAuthoritySet<H, N>>,
	write_aux: F
) -> R where
	H: Encode + Clone,
	N: Encode + Clone,
	F: FnOnce(&[(&'static [u8], &[u8])]) -> R,
{
	// write new authority set state to disk.
	let encoded_set = set.encode();

	if let Some(new_set) = new_set {
		// we also overwrite the "last completed round" entry with a blank slate
		// because from the perspective of the finality gadget, the chain has
		// reset.
		let round_state = RoundState::genesis((
			new_set.canon_hash.clone(),
			new_set.canon_number.clone(),
		));
		let set_state = VoterSetState::Live(0, round_state);
		let encoded = set_state.encode();

		write_aux(&[
			(AUTHORITY_SET_KEY, &encoded_set[..]),
			(SET_STATE_KEY, &encoded[..]),
		])
	} else {
		write_aux(&[(AUTHORITY_SET_KEY, &encoded_set[..])])
	}
}

/// Write voter set state.
pub(crate) fn write_voter_set_state<B, H, N>(backend: &B, state: &VoterSetState<H, N>)
	-> ClientResult<()>
	where B: AuxStore, H: Encode, N: Encode
{
	backend.insert_aux(
		&[(SET_STATE_KEY, state.encode().as_slice())],
		&[]
	)
}

/// Update the consensus changes.
pub(crate) fn update_consensus_changes<H, N, F, R>(
	set: &ConsensusChanges<H, N>,
	write_aux: F
) -> R where
	H: Encode + Clone,
	N: Encode + Clone,
	F: FnOnce(&[(&'static [u8], &[u8])]) -> R,
{
	write_aux(&[(CONSENSUS_CHANGES_KEY, set.encode().as_slice())])
}

#[cfg(test)]
pub(crate) fn load_authorities<B: AuxStore, H: Decode, N: Decode>(backend: &B)
	-> Option<AuthoritySet<H, N>> {
	load_decode::<_, AuthoritySet<H, N>>(backend, AUTHORITY_SET_KEY)
		.expect("backend error")
}
