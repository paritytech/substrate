// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Schema for Sassafras epoch changes in the aux-db.

use log::info;
use scale_codec::{Decode, Encode};

use sc_client_api::backend::AuxStore;
use sc_consensus_epochs::{EpochChangesFor, SharedEpochChanges};
use sp_blockchain::{Error as ClientError, Result as ClientResult};
use sp_runtime::traits::Block as BlockT;

use crate::Epoch;

const SASSAFRAS_EPOCH_CHANGES_KEY: &[u8] = b"sassafras_epoch_changes";

fn load_decode<B, T>(backend: &B, key: &[u8]) -> ClientResult<Option<T>>
where
	B: AuxStore,
	T: Decode,
{
	match backend.get_aux(key)? {
		Some(t) => T::decode(&mut &t[..]).map(Some).map_err(|e| {
			ClientError::Backend(format!("Sassafras db is corrupted, Decode error: {}", e))
		}),
		None => Ok(None),
	}
}

/// Load or initialize persistent epoch change data from backend.
pub fn load_epoch_changes<B: BlockT, AS: AuxStore>(
	backend: &AS,
) -> ClientResult<SharedEpochChanges<B, Epoch>> {
	let maybe_epoch_changes =
		load_decode::<_, EpochChangesFor<B, Epoch>>(backend, SASSAFRAS_EPOCH_CHANGES_KEY)?;

	let epoch_changes =
		SharedEpochChanges::<B, Epoch>::new(maybe_epoch_changes.unwrap_or_else(|| {
			info!(
				target: "babe",
				"👶 Creating empty BABE epoch changes on what appears to be first startup.",
			);
			EpochChangesFor::<B, Epoch>::default()
		}));

	// rebalance the tree after deserialization. this isn't strictly necessary
	// since the tree is now rebalanced on every update operation. but since the
	// tree wasn't rebalanced initially it's useful to temporarily leave it here
	// to avoid having to wait until an import for rebalancing.
	epoch_changes.shared_data().rebalance();

	Ok(epoch_changes)
}
