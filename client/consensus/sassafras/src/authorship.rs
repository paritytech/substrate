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
	digests::PreDigest, make_ticket_transcript, make_ticket_transcript_data, make_transcript_data,
	AuthorityId, SassafrasAuthorityWeight, Slot, Ticket, TicketInfo, SASSAFRAS_TICKET_VRF_PREFIX,
};
use sp_consensus_vrf::schnorrkel::{PublicKey, VRFInOut, VRFOutput, VRFProof};
use sp_core::{twox_64, ByteArray};
use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};

/// Get secondary authority index for the given epoch and slot.
#[inline]
pub fn secondary_authority_index(slot: Slot, epoch: &Epoch) -> u64 {
	u64::from_le_bytes((epoch.randomness, slot).using_encoded(twox_64)) %
		epoch.authorities.len() as u64
}

/// TODO-SASS DOCS
/// Try to claim a slot.
///
/// NOTE: we can't claim primary slot if for some reason the associated ticket information has bot
/// been preserved within the epoch structure.
pub fn claim_slot(
	slot: Slot,
	epoch: &Epoch,
	ticket: Option<Ticket>,
	keystore: &SyncCryptoStorePtr,
) -> Option<(PreDigest, AuthorityId)> {
	let (authority_index, ticket_info) = match ticket {
		Some(ticket) => {
			log::debug!(target: "sassafras", "🌳 [TRY PRIMARY]");
			let ticket_info = epoch.tickets_info.get(&ticket)?.clone();
			log::debug!(target: "sassafras", "🌳 Ticket = [ticket: {:02x?}, auth: {}, attempt: {}]",
                &ticket.as_bytes()[0..8], ticket_info.authority_index, ticket_info.attempt);
			let idx = ticket_info.authority_index as u64;
			(idx, Some(ticket_info))
		},
		None => {
			log::debug!(target: "sassafras", "🌳 [TRY SECONDARY]");
			(secondary_authority_index(slot, epoch), None)
		},
	};
	let authority_id = epoch.authorities.get(authority_index as usize).map(|auth| &auth.0)?;

	let transcript_data = make_transcript_data(&epoch.randomness, slot, epoch.epoch_index);
	let result = SyncCryptoStore::sr25519_vrf_sign(
		&**keystore,
		AuthorityId::ID,
		authority_id.as_ref(),
		transcript_data,
	);

	match result {
		Ok(Some(signature)) => {
			let pre_digest = PreDigest {
				authority_index: authority_index as u32,
				slot,
				block_vrf_output: VRFOutput(signature.output),
				block_vrf_proof: VRFProof(signature.proof.clone()),
				ticket_info,
			};
			Some((pre_digest, authority_id.clone()))
		},
		_ => None,
	}
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
// TODO-SASS: this shall be double-checked...
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

	let authorities = epoch.authorities.iter().enumerate().map(|(index, a)| (index, &a.0));
	for (authority_index, authority_id) in authorities {
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
						let ticket = VRFOutput(signature.output);
						tickets.push(ticket);
						let ticket_info = TicketInfo {
							attempt: attempt as u32,
							authority_index: authority_index as u32,
							proof: VRFProof(signature.proof),
						};
						epoch.tickets_info.insert(ticket, ticket_info);
					}
				}
			}
		}
	}
	tickets
}
