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
	digests::PreDigest, make_slot_transcript_data, make_ticket_transcript_data, AuthorityId, Slot,
	Ticket, TicketInfo, SASSAFRAS_TICKET_VRF_PREFIX,
};
use sp_consensus_vrf::schnorrkel::{PublicKey, VRFInOut, VRFOutput, VRFProof};
use sp_core::{twox_64, ByteArray};
use sp_keystore::{vrf::make_transcript, SyncCryptoStore, SyncCryptoStorePtr};

/// Get secondary authority index for the given epoch and slot.
#[inline]
pub fn secondary_authority_index(slot: Slot, epoch: &Epoch) -> u64 {
	u64::from_le_bytes((epoch.randomness, slot).using_encoded(twox_64)) %
		epoch.authorities.len() as u64
}

/// Try to claim an epoch slot.
/// If ticket is `None`, then the slot should be claimed using the fallback mechanism.
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

	let transcript_data = make_slot_transcript_data(&epoch.randomness, slot, epoch.epoch_index);
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
				vrf_output: VRFOutput(signature.output),
				vrf_proof: VRFProof(signature.proof.clone()),
				ticket_info,
			};
			Some((pre_digest, authority_id.clone()))
		},
		_ => None,
	}
}

/// Computes the threshold for a given epoch as T = (x*s)/(a*v), where:
/// - x: redundancy factor;
/// - s: number of slots in epoch;
/// - a: max number of attempts;
/// - v: number of validator in epoch.
/// The parameters should be chosen such that T <= 1.
/// If `attempts * validators` is zero then we fallback to T = 0
// TODO-SASS-P3: this formula must be double-checked...
#[inline]
fn calculate_threshold(redundancy: u32, slots: u32, attempts: u32, validators: u32) -> u128 {
	let den = attempts as u128 * validators as u128;
	let num = redundancy as u128 * slots as u128;
	let res = u128::MAX.checked_div(den).unwrap_or(0).saturating_mul(num);

	// TODO-SASS-P4 remove me
	log::debug!(
		target: "sassafras",
		"🌳 Tickets threshold: {} {:016x}", num as f64 / den as f64, res,
	);
	res
}

/// Returns true if the given VRF output is lower than the given threshold, false otherwise.
#[inline]
pub fn check_threshold(inout: &VRFInOut, threshold: u128) -> bool {
	u128::from_le_bytes(inout.make_bytes::<[u8; 16]>(SASSAFRAS_TICKET_VRF_PREFIX)) < threshold
}

/// Generate the tickets for the given epoch.
/// Tickets additional information (i.e. `TicketInfo`) will be stored within the `Epoch`
/// structure. The additional information will be used during epoch to claim slots.
pub fn generate_epoch_tickets(
	epoch: &mut Epoch,
	max_attempts: u32,
	redundancy_factor: u32,
	keystore: &SyncCryptoStorePtr,
) -> Vec<Ticket> {
	let mut tickets = vec![];

	let threshold = calculate_threshold(
		redundancy_factor,
		epoch.duration as u32,
		max_attempts,
		epoch.authorities.len() as u32,
	);

	let authorities = epoch.authorities.iter().enumerate().map(|(index, a)| (index, &a.0));
	for (authority_index, authority_id) in authorities {
		let raw_key = authority_id.to_raw_vec();

		if !SyncCryptoStore::has_keys(&**keystore, &[(raw_key.clone(), AuthorityId::ID)]) {
			continue
		}

		let public = match PublicKey::from_bytes(&raw_key) {
			Ok(public) => public,
			Err(_) => continue,
		};

		let get_ticket = |attempt| {
			let transcript_data =
				make_ticket_transcript_data(&epoch.randomness, attempt as u64, epoch.epoch_index);

			// TODO-SASS-P4: can be a good idea to replace `vrf_sign` with `vrf_sign_after_check`,
			// But we need to modify the CryptoStore interface first.
			let signature = SyncCryptoStore::sr25519_vrf_sign(
				&**keystore,
				AuthorityId::ID,
				authority_id.as_ref(),
				transcript_data.clone(),
			)
			.ok()??;

			let transcript = make_transcript(transcript_data);
			let inout = signature.output.attach_input_hash(&public, transcript).ok()?;
			if !check_threshold(&inout, threshold) {
				return None
			}

			let ticket = VRFOutput(signature.output);
			let ticket_info = TicketInfo {
				attempt: attempt as u32,
				authority_index: authority_index as u32,
				proof: VRFProof(signature.proof),
			};

			Some((ticket, ticket_info))
		};

		for attempt in 0..max_attempts {
			if let Some((ticket, ticket_info)) = get_ticket(attempt) {
				tickets.push(ticket);
				epoch.tickets_info.insert(ticket, ticket_info);
			}
		}
	}
	tickets
}
