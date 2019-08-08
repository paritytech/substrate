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

//! Schema for BABE epoch changes in the aux-db.

use log::info;
use codec::{Decode, Encode};

use client::backend::AuxStore;
use client::error::{Result as ClientResult, Error as ClientError};
use sr_primitives::traits::Block as BlockT;

use super::{EpochChanges, SharedEpochChanges};

const BABE_EPOCH_CHANGES: &[u8] = b"babe_epoch_changes";

fn load_decode<B, T>(backend: &B, key: &[u8]) -> ClientResult<Option<T>>
	where
		B: AuxStore,
		T: Decode,
{
	let corrupt = |e: codec::Error| {
		ClientError::Backend(format!("BABE DB is corrupted. Decode error: {}", e.what())).into()
	};
	match backend.get_aux(key)? {
		None => Ok(None),
		Some(t) => T::decode(&mut &t[..]).map(Some).map_err(corrupt)
	}
}

/// Load or initialize persistent epoch change data from backend.
pub(crate) fn load_epoch_changes<Block: BlockT, B: AuxStore>(
	backend: &B,
) -> ClientResult<SharedEpochChanges<Block>> {
	let epoch_changes = load_decode::<_, EpochChanges<Block>>(backend, BABE_EPOCH_CHANGES)?
		.map(Into::into)
		.unwrap_or_else(|| {
			info!(target: "babe",
				"Creating empty BABE epoch changes on what appears to be first startup."
			);
			SharedEpochChanges::new()
		});

	Ok(epoch_changes)
}

/// Update the epoch changes on disk after a change.
pub(crate) fn write_epoch_changes<Block: BlockT, F, R>(
	epoch_changes: &EpochChanges<Block>,
	write_aux: F,
) -> R where
	F: FnOnce(&[(&'static [u8], &[u8])]) -> R,
{
	let encoded_epoch_changes = epoch_changes.encode();
	write_aux(
		&[(BABE_EPOCH_CHANGES, encoded_epoch_changes.as_slice())],
	)
}
