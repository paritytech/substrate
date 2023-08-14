// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Primitives related to tickets.

use crate::{Randomness, RingVrfSignature, VrfInput, VrfOutput, VrfSignData, SASSAFRAS_ENGINE_ID};
use scale_codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
use sp_consensus_slots::Slot;
use sp_std::vec::Vec;

pub use sp_core::ed25519::{Public as EphemeralPublic, Signature as EphemeralSignature};

/// Ticket identifier.
///
/// Its value is the output of a VRF whose inputs cannot be controlled by the
/// creator of the ticket (refer to [`ticket_id_vrf_input`] parameters).
/// Because of this, it is also used as the ticket score to compare against
/// the epoch ticket's threshold.
pub type TicketId = u128;

/// Ticket data persisted on-chain.
#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub struct TicketBody {
	/// Attempt index.
	pub attempt_idx: u32,
	/// Ed25519 ephemeral public key representing ticket ownersip.
	/// (i.e. whoever has the secret, is the owner)
	pub erased_public: EphemeralPublic,
}

/// Ticket ring vrf signature.
pub type TicketSignature = RingVrfSignature;

/// Ticket envelope used on during submission.
#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub struct TicketEnvelope {
	/// Ticket body.
	pub body: TicketBody,
	/// Ring signature.
	pub signature: TicketSignature,
}

/// Ticket claim information filled by the block author.
#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub struct TicketClaim {
	/// Signature to claim ownership of `TicketBody::erased_public`.
	pub erased_signature: EphemeralSignature,
}

fn vrf_input_from_data(
	domain: &[u8],
	data: impl IntoIterator<Item = impl AsRef<[u8]>>,
) -> VrfInput {
	let raw = data.into_iter().fold(Vec::new(), |mut v, e| {
		let bytes = e.as_ref();
		v.extend_from_slice(bytes);
		let len = u8::try_from(bytes.len()).expect("private function with well known inputs; qed");
		v.extend_from_slice(&len.to_le_bytes());
		v
	});
	VrfInput::new(domain, raw)
}

/// VRF input to claim slot ownership during block production.
///
/// Input randomness is current epoch randomness.
pub fn slot_claim_vrf_input(randomness: &Randomness, slot: Slot, epoch: u64) -> VrfInput {
	vrf_input_from_data(
		b"sassafras-claim-v1.0",
		[randomness.as_slice(), &slot.to_le_bytes(), &epoch.to_le_bytes()],
	)
}

/// Signing-data to claim slot ownership during block production.
///
/// Input randomness is current epoch randomness.
pub fn slot_claim_sign_data(randomness: &Randomness, slot: Slot, epoch: u64) -> VrfSignData {
	let vrf_input = slot_claim_vrf_input(randomness, slot, epoch);
	VrfSignData::new_unchecked(&SASSAFRAS_ENGINE_ID, Some("slot-claim-transcript"), Some(vrf_input))
}

/// VRF input to generate the ticket id.
///
/// Input randomness is current epoch randomness.
pub fn ticket_id_vrf_input(randomness: &Randomness, attempt: u32, epoch: u64) -> VrfInput {
	vrf_input_from_data(
		b"sassafras-ticket-v1.0",
		[randomness.as_slice(), &attempt.to_le_bytes(), &epoch.to_le_bytes()],
	)
}

/// Data to be signed via ring-vrf.
pub fn ticket_body_sign_data(ticket_body: &TicketBody) -> VrfSignData {
	VrfSignData::new_unchecked(
		&SASSAFRAS_ENGINE_ID,
		&[b"ticket-body-transcript", ticket_body.encode().as_slice()],
		[],
	)
}

/// Get ticket-id for a given vrf input and output.
///
/// Input generally obtained via `ticket_id_vrf_input`.
/// Output can be obtained directly using the vrf secret key or from the signature.
pub fn ticket_id(vrf_input: &VrfInput, vrf_output: &VrfOutput) -> TicketId {
	let bytes = vrf_output.make_bytes::<16>(b"vrf-out", vrf_input);
	u128::from_le_bytes(bytes)
}

/// Computes the ticket-id maximum allowed values for a given epoch.
///
/// Only ticket identifiers below this threshold should be considered for slot
/// assignment.
///
/// The value is computed as `T = TicketId::MAX·(redundancy*slots)/(attempts*validators)`, where:
/// - `redundancy`: redundancy factor;
/// - `slots`: number of slots in epoch;
/// - `attempts`: max number of tickets attempts per validator;
/// - `validators`: number of validators in epoch.
///
/// If `attempts * validators = 0` then we fallback to 0.
pub fn ticket_id_threshold(
	redundancy: u32,
	slots: u32,
	attempts: u32,
	validators: u32,
) -> TicketId {
	let den = attempts as u64 * validators as u64;
	let num = redundancy as u64 * slots as u64;
	TicketId::max_value()
		.checked_div(den.into())
		.unwrap_or_default()
		.saturating_mul(num.into())
}
