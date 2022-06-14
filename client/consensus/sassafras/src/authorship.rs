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

use sp_application_crypto::AppKey;
use sp_consensus_sassafras::{
	digests::{PreDigest, PrimaryPreDigest},
	make_ticket_transcript, make_ticket_transcript_data, make_transcript_data, AuthorityId,
	SassafrasAuthorityWeight, Slot, SASSAFRAS_TICKET_VRF_PREFIX,
};
use sp_consensus_vrf::schnorrkel::{PublicKey, VRFInOut, VRFOutput, VRFProof};
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
	// 		// TODO-SASS: this should not be performed as a fallback...
	// 		// but only if we run out of tickets for the epoch "center"
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
	let Epoch { authorities, randomness, epoch_index, .. } = epoch;
	if authorities.is_empty() {
		return None
	}

	// TODO-SASS: this is a dummy placeholder
	// We'll need to replace this with the ticket system...
	// let expected_author = is_my_turn according to the epoch tickets?

	for (authority_id, authority_index) in keys {
		// TODO-SASS
		// if expected_author != authority_id { continue }

		// If we can author, we also need to push block randomness.
		let transcript_data = make_transcript_data(randomness, slot, *epoch_index);
		let result = SyncCryptoStore::sr25519_vrf_sign(
			&**keystore,
			AuthorityId::ID,
			authority_id.as_ref(),
			transcript_data,
		);
		if let Ok(Some(signature)) = result {
			let pre_digest = PreDigest::Primary(PrimaryPreDigest {
				authority_index: *authority_index as u32,
				slot,
				block_vrf_output: VRFOutput(signature.output),
				block_vrf_proof: VRFProof(signature.proof),
			});
			return Some((pre_digest, authority_id.clone()))
		}
	}
	None
}

/// Computes the threshold for a given epoch as:
///
///     T = (x*s)/(a*V)
///
/// with:
/// - x: redundancy factor
/// - s: number of slots in epoch
/// - a: attempts number
/// - V: number of validator in epoch
///
/// The parameters should be chosen such that T <= 1.
#[inline]
pub fn calculate_threshold(
	redundancy_factor: usize,
	number_of_slots: usize,
	attempts: usize,
	validators: usize,
) -> u128 {
	use num_bigint::{BigUint, ToBigUint};
	use num_traits::cast::ToPrimitive;

	log::warn!(target: "sassafras", ">>> T = {}",
        (redundancy_factor as f64 * number_of_slots as f64) / (attempts as f64 * validators as f64));
	const PROOF: &str = "Value is positive and finite, qed";
	let num = BigUint::from(redundancy_factor) * number_of_slots; //to_biguint().expect(PROOF) * number_of_slots;
	let den = attempts.to_biguint().expect(PROOF) * validators;
	// If (because of badly chosen parameters) T > 1
	let threshold = (u128::MAX.to_biguint().expect(PROOF) * num / den)
		.to_u128()
		.unwrap_or(u128::MAX);
	log::warn!(target: "sassafras", ">>> T (hex) = 0x{:016x}", threshold);
	threshold
}

/// Returns true if the given VRF output is lower than the given threshold, false otherwise.
#[inline]
pub fn check_threshold(inout: &VRFInOut, threshold: u128) -> bool {
	u128::from_le_bytes(inout.make_bytes::<[u8; 16]>(SASSAFRAS_TICKET_VRF_PREFIX)) < threshold
}

/// TODO-SASS: docs
pub struct Ticket {
	/// TODO
	pub attempt: u32,
	/// TODO
	pub authority_index: u32,
	/// TODO
	pub vrf_output: VRFOutput,
	/// TODO
	pub vrf_proof: VRFProof,
}

/// TODO-SASS
pub fn generate_epoch_tickets(
	epoch: &Epoch,
	max_attempts: usize,
	keystore: &SyncCryptoStorePtr,
) -> Vec<Ticket> {
	let mut tickets = vec![];
	let redundancy_factor = 1;

	let authorities = epoch
		.authorities
		.iter()
		.enumerate()
		.map(|(index, a)| (&a.0, index))
		.collect::<Vec<_>>();

	let threshold = calculate_threshold(
		redundancy_factor,
		epoch.duration as usize,
		max_attempts,
		epoch.authorities.len(),
	);

	for (authority_id, authority_index) in authorities {
		for attempt in 0..max_attempts {
			let transcript_data =
				make_ticket_transcript_data(&epoch.randomness, attempt as u64, epoch.epoch_index);

			// TODO-SASS: is a good idea to replace `vrf_sign` with `vrf_sign_after_check`
			// But we need to modify the CryptoStore interface first.
			let result = SyncCryptoStore::sr25519_vrf_sign(
				&**keystore,
				AuthorityId::ID,
				authority_id.as_ref(),
				transcript_data,
			);

			if let Ok(Some(signature)) = result {
				// TODO-SASS: remove unwrap()
				let public = PublicKey::from_bytes(&authority_id.to_raw_vec()).unwrap();
				let transcript =
					make_ticket_transcript(&epoch.randomness, attempt as u64, epoch.epoch_index);
				if let Ok(inout) = signature.output.attach_input_hash(&public, transcript) {
					if check_threshold(&inout, threshold) {
						let ticket = Ticket {
							attempt: attempt as u32,
							authority_index: authority_index as u32,
							vrf_output: VRFOutput(signature.output),
							vrf_proof: VRFProof(signature.proof),
						};
						tickets.push(ticket);
					}
				}
			}
		}
	}
	tickets
}
