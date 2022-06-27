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

use scale_codec::Encode;
use sp_application_crypto::AppKey;
use sp_consensus_sassafras::{
	digests::{PreDigest, PrimaryPreDigest, SecondaryPreDigest},
	make_ticket_transcript, make_ticket_transcript_data, make_transcript_data, AuthorityId,
	SassafrasAuthorityWeight, Slot, Ticket, SASSAFRAS_TICKET_VRF_PREFIX,
};
use sp_consensus_vrf::schnorrkel::{PublicKey, VRFInOut, VRFOutput, VRFProof};
use sp_core::{twox_64, ByteArray};
use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};

/// Tries to claim the given slot number. This method starts by trying to claim
/// a primary VRF based slot. If we are not able to claim it, then if we have
/// secondary slots enabled for the given epoch, we will fallback to trying to
/// claim a secondary slot.
pub fn claim_slot(
	slot: Slot,
	ticket: Option<Ticket>,
	epoch: &Epoch,
	keystore: &SyncCryptoStorePtr,
) -> Option<(PreDigest, AuthorityId)> {
	let authorities = epoch
		.authorities
		.iter()
		.enumerate()
		.map(|(index, a)| (a.0.clone(), index))
		.collect::<Vec<_>>();
	claim_slot_using_keys(slot, ticket, epoch, keystore, &authorities)
}

/// Like `claim_slot`, but allows passing an explicit set of key pairs. Useful if we intend
/// to make repeated calls for different slots using the same key pairs.
pub fn claim_slot_using_keys(
	slot: Slot,
	ticket: Option<Ticket>,
	epoch: &Epoch,
	keystore: &SyncCryptoStorePtr,
	authorities: &[(AuthorityId, usize)],
) -> Option<(PreDigest, AuthorityId)> {
	if authorities.is_empty() {
		return None
	}

	ticket
		.and_then(|ticket| claim_primary_slot(slot, ticket, epoch, keystore, authorities))
		.or_else(|| claim_secondary_slot(slot, epoch, keystore, authorities))
}

/// Claim a primary slot if it is our turn given the ticket.
/// Returns `None` if it is not our turn.
fn claim_primary_slot(
	slot: Slot,
	ticket: Ticket,
	epoch: &Epoch,
	keystore: &SyncCryptoStorePtr,
	authorities: &[(AuthorityId, usize)],
) -> Option<(PreDigest, AuthorityId)> {
	log::debug!(target: "sassafras", ">>> [TRY PRIMARY CLAIM] ticket [ attempt: {}, authority_index: {} ]", ticket.attempt, ticket.authority_index);

	let idx = ticket.authority_index;
	let expected_author = authorities.get(idx as usize).map(|auth| &auth.0)?;

	for (authority_id, authority_index) in authorities {
		if authority_id == expected_author &&
			SyncCryptoStore::has_keys(
				&**keystore,
				&[(authority_id.to_raw_vec(), AuthorityId::ID)],
			) {
			// If we can author we need to push block randomness and proof
			let transcript_data = make_transcript_data(&epoch.randomness, slot, epoch.epoch_index);
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
					block_vrf_proof: VRFProof(signature.proof.clone()),
					ticket_vrf_proof: VRFProof(signature.proof), // TODO-SASS: fetch from epoch
				});
				return Some((pre_digest, authority_id.clone()))
			}
		}
	}
	None
}

/// Claim a secondary slot if it is our turn to propose
/// Returns `None` if it is not our turn.
fn claim_secondary_slot(
	slot: Slot,
	epoch: &Epoch,
	keystore: &SyncCryptoStorePtr,
	authorities: &[(AuthorityId, usize)],
) -> Option<(PreDigest, AuthorityId)> {
	log::debug!(target: "sassafras", ">>> [TRY SECONDARY CLAIM]");

	let idx = u64::from_le_bytes((epoch.randomness, slot).using_encoded(twox_64)) %
		authorities.len() as u64;
	let expected_author = authorities
		.get(idx as usize)
		.map(|auth| &auth.0)
		.expect("authorities not empty and index constrained to list length; qed");

	for (authority_id, authority_index) in authorities {
		if authority_id == expected_author &&
			SyncCryptoStore::has_keys(
				&**keystore,
				&[(authority_id.to_raw_vec(), AuthorityId::ID)],
			) {
			let pre_digest = PreDigest::Secondary(SecondaryPreDigest {
				authority_index: *authority_index as u32,
				slot,
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

	log::debug!(target: "sassafras", "🌳 Tickets threshold: {}",
        (redundancy_factor as f64 * number_of_slots as f64) / (attempts as f64 * validators as f64));

	const PROOF: &str = "Value is positive and finite, qed";
	let num = BigUint::from(redundancy_factor) * number_of_slots; //to_biguint().expect(PROOF) * number_of_slots;
	let den = attempts.to_biguint().expect(PROOF) * validators;
	// If (because of badly chosen parameters) T > 1
	(u128::MAX.to_biguint().expect(PROOF) * num / den)
		.to_u128()
		.unwrap_or(u128::MAX)
}

/// Returns true if the given VRF output is lower than the given threshold, false otherwise.
#[inline]
pub fn check_threshold(inout: &VRFInOut, threshold: u128) -> bool {
	u128::from_le_bytes(inout.make_bytes::<[u8; 16]>(SASSAFRAS_TICKET_VRF_PREFIX)) < threshold
}

/// TODO-SASS: documentation
pub fn generate_epoch_tickets(
	epoch: &mut Epoch,
	max_attempts: usize,
	redundancy_factor: usize,
	keystore: &SyncCryptoStorePtr,
) -> Vec<Ticket> {
	let mut tickets = vec![];

	let threshold = calculate_threshold(
		redundancy_factor,
		epoch.duration as usize,
		max_attempts,
		epoch.authorities.len(),
	);

	let authorities = epoch.authorities.iter().enumerate().map(|(index, a)| (&a.0, index));
	for (authority_id, authority_index) in authorities {
		if !SyncCryptoStore::has_keys(&**keystore, &[(authority_id.to_raw_vec(), AuthorityId::ID)])
		{
			continue
		}

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
						};
						tickets.push(ticket);
						// TODO-SASS
						let key = (authority_index as u64) << 32 | attempt as u64;
						epoch.proofs.insert(key, VRFProof(signature.proof));
					}
				}
			}
		}
	}
	tickets
}
