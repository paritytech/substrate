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

//! Sassafras authority selection and slot claiming.

use crate::Epoch;

use sp_consensus_sassafras::{
	digests::{PreDigest, PrimaryPreDigest},
	AuthorityId, Slot,
};
use sp_core::ByteArray;
use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};

/// Tries to claim the given slot number. This method starts by trying to claim
/// a primary VRF based slot. If we are not able to claim it, then if we have
/// secondary slots enabled for the given epoch, we will fallback to trying to
/// claim a secondary slot.
pub fn claim_slot(
	slot: Slot,
	epoch: &Epoch,
	keystore: &SyncCryptoStorePtr,
) -> Option<(PreDigest, AuthorityId)> {
	let authorities = epoch
		.authorities
		.iter()
		.enumerate()
		.map(|(index, a)| (a.0.clone(), index))
		.collect::<Vec<_>>();
	claim_slot_using_keys(slot, epoch, keystore, &authorities)
}

/// Like `claim_slot`, but allows passing an explicit set of key pairs. Useful if we intend
/// to make repeated calls for different slots using the same key pairs.
pub fn claim_slot_using_keys(
	slot: Slot,
	epoch: &Epoch,
	keystore: &SyncCryptoStorePtr,
	keys: &[(AuthorityId, usize)],
) -> Option<(PreDigest, AuthorityId)> {
	// TODO-SASS
	// claim_primary_slot(slot, epoch, keystore, keys).or_else(|| {
	// 	if epoch.config.allowed_slots.is_secondary_plain_slots_allowed() ||
	// 		epoch.config.allowed_slots.is_secondary_vrf_slots_allowed()
	// 	{
	// 		claim_secondary_slot(
	// 			slot,
	// 			epoch,
	// 			keys,
	// 			keystore,
	// 			epoch.config.allowed_slots.is_secondary_vrf_slots_allowed(),
	// 		)
	// 	} else {
	// 		None
	// 	}
	// })
	claim_primary_slot(slot, epoch, keystore, keys)
}

/// Claim a primary slot if it is our turn.  Returns `None` if it is not our turn.
/// This hashes the slot number, epoch, genesis hash, and chain randomness into
/// the VRF.  If the VRF produces a value less than `threshold`, it is our turn,
/// so it returns `Some(_)`. Otherwise, it returns `None`.
fn claim_primary_slot(
	slot: Slot,
	epoch: &Epoch,
	keystore: &SyncCryptoStorePtr,
	keys: &[(AuthorityId, usize)],
) -> Option<(PreDigest, AuthorityId)> {
	// TODO-SASS: this is a dummy placeholder

	use sp_core::crypto::key_types::SASSAFRAS;

	for (authority_id, authority_index) in keys {
		if SyncCryptoStore::has_keys(
			keystore.as_ref(),
			&[(authority_id.clone().to_raw_vec(), SASSAFRAS)],
		) {
			let pre_digest = PreDigest::Primary(PrimaryPreDigest {
				authority_index: *authority_index as u32,
				slot,
			});
			return Some((pre_digest, authority_id.clone()))
		}
	}

	None
}
