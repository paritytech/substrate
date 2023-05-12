// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use super::{Randomness, SASSAFRAS_ENGINE_ID};
use scale_codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
use sp_consensus_slots::Slot;
use sp_core::sr25519::vrf::{VrfInput, VrfOutput};

/// VRF context used for ticket-id generation.
const TICKET_ID_VRF_CONTEXT: &[u8] = b"SassafrasTicketIdVRFContext";

/// Ticket identifier.
///
/// Within the algorithm this is also used as a ticket score applied to bound
/// the ticket to a epoch's slot.
pub type TicketId = u128;

/// Ticket data persisted on-chain.
#[derive(Debug, Default, Clone, PartialEq, Eq, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub struct TicketData {
	/// Attempt index.
	pub attempt_idx: u32,
	/// Ed25519 public key which gets erased when claiming the ticket.
	pub erased_public: [u8; 32],
	/// Ed25519 public key which gets exposed when claiming the ticket.
	pub revealed_public: [u8; 32],
}

/// Ticket ring proof.
/// TODO-SASS-P3: this is a placeholder.
pub type TicketRingProof = ();

/// Ticket envelope used on during submission.
#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub struct TicketEnvelope {
	/// VRF output.
	pub data: TicketData,
	/// VRF pre-output used to generate the ticket id.
	pub vrf_preout: VrfOutput,
	// /// Pedersen VRF signature
	// pub ped_signature: (),
	/// Ring VRF proof.
	pub ring_proof: TicketRingProof,
}

/// Ticket auxiliary information used to claim the ticket ownership.
#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub struct TicketSecret {
	/// Attempt index.
	pub attempt_idx: u32,
	/// Ed25519 used to claim ticket ownership.
	pub erased_secret: [u8; 32],
}

/// Ticket claim information filled by the block author.
#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub struct TicketClaim {
	pub erased_signature: [u8; 64],
}

/// VRF input to claim slot ownership during block production.
///
/// Input randomness is current epoch randomness.
pub fn slot_claim_vrf_input(randomness: &Randomness, slot: Slot, epoch: u64) -> VrfInput {
	VrfInput::new(
		&SASSAFRAS_ENGINE_ID,
		&[
			(b"type", b"ticket-claim-transcript"),
			(b"slot", &slot.to_le_bytes()),
			(b"epoch", &epoch.to_le_bytes()),
			(b"randomness", randomness),
		],
	)
}

/// VRF input to generate the ticket id.
///
/// Input randomness is current epoch randomness.
pub fn ticket_id_vrf_input(randomness: &Randomness, attempt: u32, epoch: u64) -> VrfInput {
	VrfInput::new(
		&SASSAFRAS_ENGINE_ID,
		&[
			(b"type", b"ticket-id-transcript"),
			(b"attempt", &attempt.to_le_bytes()),
			(b"epoch", &epoch.to_le_bytes()),
			(b"randomness", randomness),
		],
	)
}

/// Get ticket-id for a given vrf input and output.
///
/// Input generally obtained via `ticket_id_vrf_input`.
/// Output can be obtained directly using the vrf secret key or from the signature.
// TODO DAVXY: with new VRF authority-id is not necessary
pub fn ticket_id(vrf_input: &VrfInput, vrf_output: &VrfOutput) -> TicketId {
	let public = sp_core::sr25519::Public::from_raw([0; 32]);
	vrf_output
		.make_bytes::<16>(TICKET_ID_VRF_CONTEXT, vrf_input, &public)
		.map(|bytes| u128::from_le_bytes(bytes))
		.unwrap_or(u128::MAX)
}

/// Computes the threshold for a given epoch as T = (x*s)/(a*v), where:
/// - x: redundancy factor;
/// - s: number of slots in epoch;
/// - a: max number of attempts;
/// - v: number of validator in epoch.
/// The parameters should be chosen such that T <= 1.
/// If `attempts * validators` is zero then we fallback to T = 0
// TODO-SASS-P3: this formula must be double-checked...
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
