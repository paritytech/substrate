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

//! BABE slot claiming code


use babe_primitives::{Epoch, SlotNumber, AuthorityId, BabeAuthorityWeight, AuthorityPair, BabePreDigest};
use babe_primitives::{BabeConfiguration};
use primitives::Pair;
use keystore::KeyStorePtr;

/// Claim a secondary slot if it is our turn to propose, returning the
/// pre-digest to use when authoring the block, or `None` if it is not our turn
/// to propose.
fn claim_secondary_slot(
	slot_number: SlotNumber,
	authorities: &[(AuthorityId, BabeAuthorityWeight)],
	keystore: &KeyStorePtr,
	randomness: [u8; 32],
) -> Option<(BabePreDigest, AuthorityPair)> {
	if authorities.is_empty() {
		return None;
	}

	let expected_author = super::authorship::secondary_slot_author(
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
			let pre_digest = BabePreDigest::Secondary {
				slot_number,
				authority_index: authority_index as u32,
			};

			return Some((pre_digest, pair));
		}
	}

	None
}

/// Tries to claim the given slot number. This method starts by trying to claim
/// a primary VRF based slot. If we are not able to claim it, then if we have
/// secondary slots enabled for the given epoch, we will fallback to trying to
/// claim a secondary slot.
pub(super) fn claim_slot(
	slot_number: SlotNumber,
	epoch: &Epoch,
	config: &BabeConfiguration,
	keystore: &KeyStorePtr,
) -> Option<(BabePreDigest, AuthorityPair)> {
	claim_primary_slot(slot_number, epoch, config.c, keystore)
		.or_else(|| {
			if config.secondary_slots {
				claim_secondary_slot(
					slot_number,
					&epoch.authorities,
					keystore,
					epoch.randomness,
				)
			} else {
				None
			}
		})
}

fn get_keypair(q: &AuthorityPair) -> &schnorrkel::Keypair {
	use primitives::crypto::IsWrappedBy;
	primitives::sr25519::Pair::from_ref(q).as_ref()
}

/// Claim a primary slot if it is our turn.  Returns `None` if it is not our turn.
/// This hashes the slot number, epoch, genesis hash, and chain randomness into
/// the VRF.  If the VRF produces a value less than `threshold`, it is our turn,
/// so it returns `Some(_)`. Otherwise, it returns `None`.
fn claim_primary_slot(
	slot_number: SlotNumber,
	epoch: &Epoch,
	c: (u64, u64),
	keystore: &KeyStorePtr,
) -> Option<(BabePreDigest, AuthorityPair)> {
	let Epoch { authorities, randomness, epoch_index, .. } = epoch;
	let keystore = keystore.read();

	for (pair, authority_index) in authorities.iter()
		.enumerate()
		.flat_map(|(i, a)| {
			keystore.key_pair::<AuthorityPair>(&a.0).ok().map(|kp| (kp, i))
		})
	{
		let transcript = super::authorship::make_transcript(randomness, slot_number, *epoch_index);

		// Compute the threshold we will use.
		//
		// We already checked that authorities contains `key.public()`, so it can't
		// be empty.  Therefore, this division in `calculate_threshold` is safe.
		let threshold = super::authorship::calculate_primary_threshold(c, authorities, authority_index);

		let pre_digest = get_keypair(&pair)
			.vrf_sign_after_check(transcript, |inout| super::authorship::check_primary_threshold(inout, threshold))
			.map(|s| {
				BabePreDigest::Primary {
					slot_number,
					vrf_output: s.0.to_output(),
					vrf_proof: s.1,
					authority_index: authority_index as u32,
				}
			});

		// early exit on first successful claim
		if let Some(pre_digest) = pre_digest {
			return Some((pre_digest, pair));
		}
	}

	None
}
