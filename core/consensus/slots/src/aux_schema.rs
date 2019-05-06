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

use std::collections::{BTreeMap, btree_map::Entry};
use std::sync::Arc;
use codec::{Encode, Decode};
use client::backend::AuxStore;
use client::error::{Result as ClientResult, ErrorKind as ClientErrorKind};
use runtime_primitives::traits::{Header};

const VERSION_KEY: &[u8] = b"aura_schema_version";
const SLOT_HEADER_MAP_KEY: &[u8] = b"aura_slot_header_map";
const CURRENT_VERSION: u32 = 1;
pub const MAX_SLOT_CAPACITY: u64 = 1000;

fn load_decode<C, T>(backend: Arc<C>, key: &[u8]) -> ClientResult<Option<T>> 
	where
		C: AuxStore,
		T: Decode,
{
	match backend.get_aux(key)? {
		None => Ok(None),
		Some(t) => T::decode(&mut &t[..])
			.ok_or_else(
				|| ClientErrorKind::Backend(format!("Aura DB is corrupted.")).into(),
			)
			.map(Some)
	}
}

/// Persistent data kept between slots.
#[derive(Debug)]
pub struct PersistentData<H: Header> {
	pub version: u32,
	pub slot_header_map: BTreeMap<u64, H>,
}

#[derive(Debug, Clone)]
pub struct EquivocationProof<H> {
	slot: u64,
	fst_header: H,
	snd_header: H,
}

impl<H> EquivocationProof<H> {
	pub fn get_slot(&self) -> u64 {
		self.slot
	}

	pub fn get_fst_header(&self) -> &H {
		&self.fst_header
	}

	pub fn get_snd_header(&self) -> &H {
		&self.snd_header
	}
}

/// Check if the header is an equivocation and returns the proof in that case.
/// Assumes all the headers in the same slot are signed by the same Signer.
pub fn check_equivocation<C, H>(
	backend: &Arc<C>,
	slot: u64,
	header: H,
) -> ClientResult<Option<EquivocationProof<H>>>
	where
		H: Header,
		C: AuxStore,
{
	let mut slot_header_map = load_decode::<_, BTreeMap<u64, H>>(backend.clone(), SLOT_HEADER_MAP_KEY)?
		.unwrap_or_else(BTreeMap::new);

	match slot_header_map.entry(slot) {
		Entry::Vacant(vacant_entry) => {
			vacant_entry.insert(header);
		},
		Entry::Occupied(occupied_entry) => {
			let fst_header = occupied_entry.get().clone();
			let snd_header = header;

			if fst_header.hash() != snd_header.hash() {
				return Ok(Some(EquivocationProof {
					slot,
					fst_header,
					snd_header,
				}));
			}
		},
	};

	if slot > MAX_SLOT_CAPACITY {
		slot_header_map = slot_header_map.split_off(&(slot - MAX_SLOT_CAPACITY));
	}

	backend.insert_aux(
		&[(SLOT_HEADER_MAP_KEY, slot_header_map.encode().as_slice())],
		&[],
	)?;

	Ok(None)
}
