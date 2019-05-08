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
use client::error::{Result as ClientResult, Error as ClientError};
use runtime_primitives::traits::Header;

const SLOT_HEADER_MAP_KEY: &[u8] = b"slot_header_map";
/// We keep at least this number of slots in database.
pub const MAX_SLOT_CAPACITY: u64 = 1000;
/// We prune slots when they reach this number.
pub const PRUNING_BOUND: usize = MAX_SLOT_CAPACITY as usize + 1000;

fn load_decode<C, T>(backend: Arc<C>, key: &[u8]) -> ClientResult<Option<T>> 
	where
		C: AuxStore,
		T: Decode,
{
	match backend.get_aux(key)? {
		None => Ok(None),
		Some(t) => T::decode(&mut &t[..])
			.ok_or_else(
				|| ClientError::Backend(format!("Slots DB is corrupted.")).into(),
			)
			.map(Some)
	}
}

#[derive(Debug, Clone)]
pub struct EquivocationProof<H> {
	slot: u64,
	fst_header: H,
	snd_header: H,
}

impl<H> EquivocationProof<H> {
	pub fn slot(&self) -> u64 {
		self.slot
	}

	pub fn fst_header(&self) -> &H {
		&self.fst_header
	}

	pub fn snd_header(&self) -> &H {
		&self.snd_header
	}
}

/// Check if the header is an equivocation and returns the proof in that case.
/// Assumes all the headers in the same slot are signed by the same Signer.
pub fn check_equivocation<C, H, P>(
	backend: &Arc<C>,
	slot: u64,
	header: H,
	signer: P,
) -> ClientResult<Option<EquivocationProof<H>>>
	where
		H: Header,
		C: AuxStore,
		P: Encode + Decode + PartialEq,
{
	let mut key = SLOT_HEADER_MAP_KEY.to_vec();
	slot.using_encoded(|s| key.extend(s));

	let mut v = load_decode::<_, Vec<(H, P)>>(backend.clone(), &key[..])?
		.unwrap_or_else(Vec::new);

	for (prev_header, prev_signer) in v.iter() {
		if *prev_signer == signer {
			if header.hash() != prev_header.hash() {
				return Ok(Some(EquivocationProof {
					slot,
					fst_header: prev_header.clone(),
					snd_header: header.clone(),
				}));
			}
		}
	}

	// match slot_header_map.entry(slot) {
	// 	Entry::Vacant(vacant_entry) => {
	// 		vacant_entry.insert(vec![(header, signer)]);
	// 	},
	// 	Entry::Occupied(occupied_entry) => {
	// 		let v = occupied_entry.get();
	// 		for (prev_header, prev_signer) in v.iter() {
	// 			if *prev_signer == signer {
	// 				if header.hash() != prev_header.hash() {
	// 					return Ok(Some(EquivocationProof {
	// 						slot,
	// 						fst_header: prev_header.clone(),
	// 						snd_header: header.clone(),
	// 					}));
	// 				}
	// 			}
	// 		}
			// let fst_header = occupied_entry.get().clone();
			// let snd_header = header;

			// if fst_header.hash() != snd_header.hash() {
			// 	return Ok(Some(EquivocationProof {
			// 		slot,
			// 		fst_header,
			// 		snd_header,
			// 	}));
			// }
	// 	},
	// };

	if slot % PRUNING_BOUND == 0 {
		// slot_header_map = slot_header_map.split_off(&(slot - MAX_SLOT_CAPACITY));
	}

	v.push((header, signer));

	backend.insert_aux(
		&[(&key[..], v.encode().as_slice())],
		&[],
	)?;

	Ok(None)
}
