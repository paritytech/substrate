// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Sassafras authority selection and slot claiming.

use codec::Encode;
use sp_core::{blake2_256, U256, crypto::Pair};
use sp_consensus_sassafras::{
	SlotNumber, AuthorityPair, SassafrasConfiguration, AuthorityId,
	SassafrasAuthorityWeight, digests::PreDigest,
};
use sc_keystore::KeyStorePtr;
use super::Epoch;

/// Tries to claim the given slot number. This method starts by trying to claim
/// a primary VRF based slot. If we are not able to claim it, then if we have
/// secondary slots enabled for the given epoch, we will fallback to trying to
/// claim a secondary slot.
pub(super) fn claim_slot(
	slot_number: SlotNumber,
	epoch: &Epoch,
	config: &SassafrasConfiguration,
	keystore: &KeyStorePtr,
) -> Option<(PreDigest, AuthorityPair)> {
	None.or_else(|| {
		if config.secondary_slots {
			claim_secondary_slot(
				slot_number,
				&epoch.validating.authorities,
				keystore,
				epoch.validating.randomness,
			)
		} else {
			None
		}
	})
}

/// Claim a secondary slot if it is our turn to propose, returning the
/// pre-digest to use when authoring the block, or `None` if it is not our turn
/// to propose.
fn claim_secondary_slot(
	slot_number: SlotNumber,
	authorities: &[(AuthorityId, SassafrasAuthorityWeight)],
	keystore: &KeyStorePtr,
	randomness: [u8; 32],
) -> Option<(PreDigest, AuthorityPair)> {
	if authorities.is_empty() {
		return None;
	}

	let expected_author = secondary_slot_author(
		slot_number,
		authorities,
		randomness,
	)?;

	let keystore = keystore.read();

	for (pair, authority_index) in authorities.iter()
		.enumerate()
		.flat_map(|(i, a)| {
			keystore.key_pair::<AuthorityPair>(&a.0).ok().map(|kp| (kp, i))
		})
	{
		if pair.public() == *expected_author {
			let pre_digest = PreDigest::Secondary {
				slot_number,
				authority_index: authority_index as u32,
				commitments: Vec::new(),
			};

			return Some((pre_digest, pair));
		}
	}

	None
}

/// Get the expected secondary author for the given slot and with given
/// authorities. This should always assign the slot to some authority unless the
/// authorities list is empty.
fn secondary_slot_author(
	slot_number: u64,
	authorities: &[(AuthorityId, SassafrasAuthorityWeight)],
	randomness: [u8; 32],
) -> Option<&AuthorityId> {
	if authorities.is_empty() {
		return None;
	}

	let rand = U256::from((randomness, slot_number).using_encoded(blake2_256));

	let authorities_len = U256::from(authorities.len());
	let idx = rand % authorities_len;

	let expected_author = authorities.get(idx.as_u32() as usize)
		.expect("authorities not empty; index constrained to list length; \
				this is a valid index; qed");

	Some(&expected_author.0)
}
