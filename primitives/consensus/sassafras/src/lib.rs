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

//! Primitives for Sassafras
//! TODO-SASS-P2 : write proper docs

// TODO DAVXY enable warnings
// #![deny(warnings)]
// #![forbid(unsafe_code, missing_docs, unused_variables, unused_imports)]
#![cfg_attr(not(feature = "std"), no_std)]

use scale_codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
#[cfg(feature = "std")]
use serde::{Deserialize, Serialize};
use sp_core::crypto::KeyTypeId;
use sp_runtime::{ConsensusEngineId, RuntimeDebug};
use sp_std::vec::Vec;

pub use sp_consensus_slots::{Slot, SlotDuration};
pub use sp_core::sr25519::vrf::{VrfOutput, VrfProof, VrfSignature, VrfTranscript};

pub mod digests;
pub mod inherents;

mod app {
	use sp_application_crypto::{app_crypto, key_types::SASSAFRAS, sr25519};
	app_crypto!(sr25519, SASSAFRAS);
}

/// Key type for Sassafras protocol.
pub const KEY_TYPE: KeyTypeId = sp_application_crypto::key_types::SASSAFRAS;

/// Consensus engine identifier.
pub const SASSAFRAS_ENGINE_ID: ConsensusEngineId = *b"SASS";

/// VRF context used for per-slot randomness generation.
pub const RANDOMNESS_VRF_CONTEXT: &[u8] = b"SassafrasRandomnessVRFContext";

/// VRF output length for per-slot randomness.
pub const RANDOMNESS_LENGTH: usize = 32;

/// The index of an authority.
pub type AuthorityIndex = u32;

/// Sassafras authority keypair. Necessarily equivalent to the schnorrkel public key used in
/// the main Sassafras module. If that ever changes, then this must, too.
#[cfg(feature = "std")]
pub type AuthorityPair = app::Pair;

/// Sassafras authority signature.
pub type AuthoritySignature = app::Signature;

/// Sassafras authority identifier. Necessarily equivalent to the schnorrkel public key used in
/// the main Sassafras module. If that ever changes, then this must, too.
pub type AuthorityId = app::Public;

/// The weight of an authority.
// NOTE: we use a unique name for the weight to avoid conflicts with other
// `Weight` types, since the metadata isn't able to disambiguate.
pub type SassafrasAuthorityWeight = u64;

/// Weight of a Sassafras block.
/// Primary blocks have a weight of 1 whereas secondary blocks have a weight of 0.
pub type SassafrasBlockWeight = u32;

/// An equivocation proof for multiple block authorships on the same slot (i.e. double vote).
pub type EquivocationProof<H> = sp_consensus_slots::EquivocationProof<H, AuthorityId>;

/// Randomness required by some SASSAFRAS operations.
pub type Randomness = [u8; RANDOMNESS_LENGTH];

/// Configuration data used by the Sassafras consensus engine.
#[derive(Clone, Encode, Decode, RuntimeDebug, PartialEq, Eq, TypeInfo)]
pub struct SassafrasConfiguration {
	/// The slot duration in milliseconds.
	pub slot_duration: u64,
	/// The duration of epoch in slots.
	pub epoch_duration: u64,
	/// The authorities for the epoch.
	pub authorities: Vec<(AuthorityId, SassafrasAuthorityWeight)>,
	/// The randomness for the epoch.
	pub randomness: Randomness,
	/// Tickets threshold parameters.
	pub threshold_params: SassafrasEpochConfiguration,
}

impl SassafrasConfiguration {
	/// Get the slot duration defined in the genesis configuration.
	pub fn slot_duration(&self) -> SlotDuration {
		SlotDuration::from_millis(self.slot_duration)
	}
}

/// Sassafras epoch information
#[derive(Encode, Decode, PartialEq, Eq, Clone, Debug, TypeInfo)]
pub struct Epoch {
	/// The epoch index.
	pub epoch_idx: u64,
	/// The starting slot of the epoch.
	pub start_slot: Slot,
	/// Epoch configuration.
	pub config: SassafrasConfiguration,
}

/// Configuration data used by the Sassafras consensus engine that can be modified on epoch change.
// TODO-SASS-P3: rename to something better... like LotteryConfig
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, MaxEncodedLen, TypeInfo, Default)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct SassafrasEpochConfiguration {
	/// Redundancy factor.
	pub redundancy_factor: u32,
	/// Number of attempts for tickets generation.
	pub attempts_number: u32,
}

/// Ticket identifier.
pub type TicketId = u128;

/// TODO DAVXY
/// input obtained via `make_vrf_input_transcript`
pub fn make_ticket_value(_in: &VrfTranscript, out: &VrfOutput) -> TicketId {
	// TODO DAVXY temporary way to generate id... use io.make_bytes()
	let preout = out;
	let mut raw: [u8; 16] = [0; 16];
	raw.copy_from_slice(&preout.0 .0[0..16]);
	u128::from_le_bytes(raw)
}

/// Ticket value.
// TODO: potentially this can be opaque to separate the protocol from the application
#[derive(Debug, Default, Clone, PartialEq, Eq, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub struct TicketData {
	/// Attempt index.
	pub attempt_idx: u32,
	/// Ed25519 public key which gets erased when claiming the ticket.
	pub erased_public: [u8; 32],
	/// Ed25519 public key which gets exposed when claiming the ticket.
	pub revealed_public: [u8; 32],
}

/// Ticket ZK commitment proof.
/// TODO-SASS-P3: this is a placeholder.
pub type TicketRingProof = ();

/// Ticket envelope used on submission.
// TODO-SASS-P3: we are currently using Shnorrkel structures as placeholders.
// Should switch to new RVRF primitive soon.
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

/// Ticket private auxiliary information.
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

/// Computes the threshold for a given epoch as T = (x*s)/(a*v), where:
/// - x: redundancy factor;
/// - s: number of slots in epoch;
/// - a: max number of attempts;
/// - v: number of validator in epoch.
/// The parameters should be chosen such that T <= 1.
/// If `attempts * validators` is zero then we fallback to T = 0
// TODO-SASS-P3: this formula must be double-checked...
pub fn compute_ticket_id_threshold(
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

/// An opaque type used to represent the key ownership proof at the runtime API boundary.
/// The inner value is an encoded representation of the actual key ownership proof which will be
/// parameterized when defining the runtime. At the runtime API boundary this type is unknown and
/// as such we keep this opaque representation, implementors of the runtime API will have to make
/// sure that all usages of `OpaqueKeyOwnershipProof` refer to the same type.
#[derive(Decode, Encode, PartialEq, TypeInfo)]
pub struct OpaqueKeyOwnershipProof(Vec<u8>);

// impl OpaqueKeyOwnershipProof {
// 	/// Create a new `OpaqueKeyOwnershipProof` using the given encoded representation.
// 	pub fn new(inner: Vec<u8>) -> OpaqueKeyOwnershipProof {
// 		OpaqueKeyOwnershipProof(inner)
// 	}

// 	/// Try to decode this `OpaqueKeyOwnershipProof` into the given concrete key
// 	/// ownership proof type.
// 	pub fn decode<T: Decode>(self) -> Option<T> {
// 		Decode::decode(&mut &self.0[..]).ok()
// 	}
// }

/// Make per slot randomness VRF input transcript.
///
/// Input randomness is current epoch randomness.
pub fn make_slot_vrf_transcript(randomness: &Randomness, slot: Slot, epoch: u64) -> VrfTranscript {
	VrfTranscript::new(
		&SASSAFRAS_ENGINE_ID,
		&[
			(b"type", b"slot-transcript"),
			(b"slot", &slot.to_le_bytes()),
			(b"epoch", &epoch.to_le_bytes()),
			(b"randomness", randomness),
		],
	)
}

/// Make ticket VRF transcript data container.
///
/// Input randomness is current epoch randomness.
pub fn make_ticket_vrf_transcript(
	randomness: &Randomness,
	attempt: u32,
	epoch: u64,
) -> VrfTranscript {
	VrfTranscript::new(
		&SASSAFRAS_ENGINE_ID,
		&[
			(b"type", b"ticket-transcript"),
			(b"attempt", &attempt.to_le_bytes()),
			(b"epoch", &epoch.to_le_bytes()),
			(b"randomness", randomness),
		],
	)
}

// Runtime API.
sp_api::decl_runtime_apis! {
	/// API necessary for block authorship with Sassafras.
	pub trait SassafrasApi {
		/// Submit next epoch validator tickets via an unsigned extrinsic.
		/// This method returns `false` when creation of the extrinsics fails.
		fn submit_tickets_unsigned_extrinsic(tickets: Vec<TicketEnvelope>) -> bool;

		/// Get ticket id associated to the given slot.
		fn slot_ticket_id(slot: Slot) -> Option<TicketId>;

		/// Get ticket id and data associated to the given slot.
		fn slot_ticket(slot: Slot) -> Option<(TicketId, TicketData)>;

		/// Current epoch information.
		fn current_epoch() -> Epoch;

		/// Next epoch information.
		fn next_epoch() -> Epoch;

		/// Generates a proof of key ownership for the given authority in the current epoch.
		///
		/// An example usage of this module is coupled with the session historical module to prove
		/// that a given authority key is tied to a given staking identity during a specific
		/// session. Proofs of key ownership are necessary for submitting equivocation reports.
		///
		/// NOTE: even though the API takes a `slot` as parameter the current implementations
		/// ignores this parameter and instead relies on this method being called at the correct
		/// block height, i.e. any point at which the epoch for the given slot is live on-chain.
		/// Future implementations will instead use indexed data through an offchain worker, not
		/// requiring older states to be available.
		fn generate_key_ownership_proof(
			slot: Slot,
			authority_id: AuthorityId,
		) -> Option<OpaqueKeyOwnershipProof>;

		/// Submits an unsigned extrinsic to report an equivocation.
		///
		/// The caller must provide the equivocation proof and a key ownership proof (should be
		/// obtained using `generate_key_ownership_proof`). The extrinsic will be unsigned and
		/// should only be accepted for local authorship (not to be broadcast to the network). This
		/// method returns `None` when creation of the extrinsic fails, e.g. if equivocation
		/// reporting is disabled for the given runtime (i.e. this method is hardcoded to return
		/// `None`). Only useful in an offchain context.
		fn submit_report_equivocation_unsigned_extrinsic(
			equivocation_proof: EquivocationProof<Block::Header>,
			key_owner_proof: OpaqueKeyOwnershipProof,
		) -> bool;
	}
}
