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
	Ticket, TicketInfo,
};
use sp_consensus_vrf::schnorrkel::{VRFOutput, VRFProof};
use sp_core::{twox_64, ByteArray};
use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};

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

	result.ok().flatten().map(|signature| {
		let pre_digest = PreDigest {
			authority_index: authority_index as u32,
			slot,
			vrf_output: VRFOutput(signature.output),
			vrf_proof: VRFProof(signature.proof.clone()),
			ticket_info,
		};
		(pre_digest, authority_id.clone())
	})
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

	let threshold = sp_consensus_sassafras::compute_threshold(
		redundancy_factor,
		epoch.duration as u32,
		max_attempts,
		epoch.authorities.len() as u32,
	);
	// TODO-SASS-P4 remove me
	log::debug!(target: "sassafras", "🌳 Tickets threshold: {:032x}", threshold);

	let authorities = epoch.authorities.iter().enumerate().map(|(index, a)| (index, &a.0));
	for (authority_index, authority_id) in authorities {
		if !SyncCryptoStore::has_keys(&**keystore, &[(authority_id.to_raw_vec(), AuthorityId::ID)])
		{
			continue
		}

		let make_ticket = |attempt| {
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

			let ticket = VRFOutput(signature.output);
			if !sp_consensus_sassafras::check_threshold(&ticket, threshold) {
				return None
			}

			let ticket_info = TicketInfo {
				attempt: attempt as u32,
				authority_index: authority_index as u32,
				proof: VRFProof(signature.proof),
			};

			Some((ticket, ticket_info))
		};

		for attempt in 0..max_attempts {
			if let Some((ticket, ticket_info)) = make_ticket(attempt) {
				tickets.push(ticket);
				epoch.tickets_info.insert(ticket, ticket_info);
			}
		}
	}
	tickets
}
