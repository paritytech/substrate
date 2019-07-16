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

//! Schema for slots in the aux-db.

use super::{Encode, Decode};
use client::backend::AuxStore;
use client::error::{Result as ClientResult, Error as ClientError};
use super::{Epoch, SlotNumber};
use log::error;
use std::u64;
const BABE_CURRENT_EPOCH: &[u8] = b"babe current epoch";
const BABE_NEXT_EPOCH: &[u8] = b"babe next epoch";
const BABE_SLOT_NUMBER: &[u8] = b"babe slot number";

fn load_decode<C, T>(backend: &C, key: &[u8]) -> ClientResult<Option<T>>
	where
		C: AuxStore,
		T: Decode,
{
	let corrupt = || ClientError::Backend(format!("BABE DB is corrupted.")).into();
	match backend.get_aux(key)? {
		None => Ok(None),
		Some(t) => T::decode(&mut &t[..]).ok_or_else(corrupt).map(Some)
	}
}

/// Checks if an epoch is valid.
pub fn check_epoch<C>(
	backend: &C,
	slot_now: u64,
	epoch_under_test: &Epoch,
) -> ClientResult<()> where	C: AuxStore,
{
	if slot_now == 0 {
		// Genesis is trusted
		return backend.insert_aux(
			&[
				(BABE_NEXT_EPOCH, epoch_under_test.encode().as_slice()),
				(BABE_CURRENT_EPOCH, epoch_under_test.encode().as_slice()),
				(BABE_SLOT_NUMBER, 0.encode().as_slice()),
			],
			&[],
		)
	}
	let this_epoch: Epoch = load_decode(backend, BABE_CURRENT_EPOCH)?
		.expect("we will always have a current epoch; qed");
	let last_epoch_change: SlotNumber = load_decode(backend, BABE_SLOT_NUMBER)?.unwrap_or(0);
	if epoch_under_test.epoch_index.checked_sub(this_epoch.epoch_index) != Some(1) {
		return Err(ClientError::Backend(format!(
			"Invalid BABE epoch: expected next epoch to be {:?}, got {:?}",
			this_epoch.epoch_index.saturating_add(1),
			epoch_under_test.epoch_index,
		)))
	}

	let expected_slot_number =
		this_epoch.duration.checked_add(last_epoch_change).unwrap_or_else(|| {
			error!("BABE slot number overflow ― storage is corrupt!");
			u64::MAX
		});
	if slot_now < expected_slot_number {
		return Err(ClientError::Backend(format!(
			"Invalid BABE epoch: wrong slot for epoch change: expected {:?}, got {:?}",
			expected_slot_number,
			slot_now,
		)))
	}
	// The first two epochs are identical by design.  Most clients will hardcode
	// the state of the DB after this point.
	let next_epoch = load_decode(backend, BABE_NEXT_EPOCH)?.unwrap_or_else(|| this_epoch.clone());
	backend.insert_aux(
		&[
			(BABE_NEXT_EPOCH, epoch_under_test.encode().as_slice()),
			(BABE_CURRENT_EPOCH, next_epoch.encode().as_slice()),
			(BABE_SLOT_NUMBER, slot_now.encode().as_slice()),
		],
		&[],
	)
}
