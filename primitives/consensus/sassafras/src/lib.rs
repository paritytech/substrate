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

//! Primitives for Sassafras consensus.

#![deny(warnings)]
#![forbid(unsafe_code, missing_docs, unused_variables, unused_imports)]
#![cfg_attr(not(feature = "std"), no_std)]

use scale_codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
use sp_core::crypto::KeyTypeId;
use sp_runtime::{ConsensusEngineId, RuntimeDebug};
use sp_std::vec::Vec;

pub use sp_consensus_slots::{Slot, SlotDuration};
pub use sp_core::bandersnatch::{
	ring_vrf::{RingContext, RingProver, RingVerifier, RingVrfSignature},
	vrf::{VrfInput, VrfOutput, VrfSignData, VrfSignature},
};

pub mod digests;
pub mod inherents;
pub mod ticket;

pub use ticket::{
	slot_claim_sign_data, slot_claim_vrf_input, ticket_body_sign_data, ticket_id,
	ticket_id_threshold, ticket_id_vrf_input, TicketBody, TicketClaim, TicketEnvelope, TicketId,
};

mod app {
	use sp_application_crypto::{app_crypto, bandersnatch, key_types::SASSAFRAS};
	app_crypto!(bandersnatch, SASSAFRAS);
}

/// Key type identifier.
pub const KEY_TYPE: KeyTypeId = sp_application_crypto::key_types::SASSAFRAS;

/// Consensus engine identifier.
pub const SASSAFRAS_ENGINE_ID: ConsensusEngineId = *b"SASS";

/// VRF output length for per-slot randomness.
pub const RANDOMNESS_LENGTH: usize = 32;

/// Index of an authority.
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

/// Weight of a Sassafras block.
/// Primary blocks have a weight of 1 whereas secondary blocks have a weight of 0.
pub type SassafrasBlockWeight = u32;

/// An equivocation proof for multiple block authorships on the same slot (i.e. double vote).
pub type EquivocationProof<H> = sp_consensus_slots::EquivocationProof<H, AuthorityId>;

/// Randomness required by some protocol's operations.
pub type Randomness = [u8; RANDOMNESS_LENGTH];

/// Configuration data that can be modified on epoch change.
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, MaxEncodedLen, TypeInfo, Default)]
pub struct EpochConfiguration {
	/// Redundancy factor.
	pub redundancy_factor: u32,
	/// Number of attempts for tickets generation.
	pub attempts_number: u32,
}

/// Information attached to an epoch.
// TODO @davxy. Why not embed this information in `Epoch` structure below?
#[derive(Clone, Encode, Decode, RuntimeDebug, PartialEq, Eq, TypeInfo)]
pub struct EpochData {
	/// Slot duration in milliseconds.
	pub slot_duration: SlotDuration,
	/// Duration of epoch in slots.
	pub epoch_duration: u64,
	/// Authorities for the epoch.
	pub authorities: Vec<AuthorityId>,
	/// Randomness for the epoch.
	pub randomness: Randomness,
	/// Tickets threshold parameters.
	pub threshold_params: EpochConfiguration,
}

/// Sassafras epoch information
#[derive(Encode, Decode, PartialEq, Eq, Clone, Debug, TypeInfo)]
pub struct Epoch {
	/// The epoch index.
	pub epoch_idx: u64,
	/// The starting slot of the epoch.
	pub start_slot: Slot,
	/// Epoch configuration.
	pub config: EpochData,
}

/// An opaque type used to represent the key ownership proof at the runtime API boundary.
///
/// The inner value is an encoded representation of the actual key ownership proof which will be
/// parameterized when defining the runtime. At the runtime API boundary this type is unknown and
/// as such we keep this opaque representation, implementors of the runtime API will have to make
/// sure that all usages of `OpaqueKeyOwnershipProof` refer to the same type.
#[derive(Decode, Encode, PartialEq, TypeInfo)]
pub struct OpaqueKeyOwnershipProof(Vec<u8>);

// Runtime API.
sp_api::decl_runtime_apis! {
	/// API necessary for block authorship with Sassafras.
	pub trait SassafrasApi {
		/// Get ticket id associated to the given slot.
		fn slot_ticket_id(slot: Slot) -> Option<TicketId>;

		/// Get ticket id and data associated to the given slot.
		fn slot_ticket(slot: Slot) -> Option<(TicketId, TicketBody)>;

		/// Current epoch information.
		fn current_epoch() -> Epoch;

		/// Next epoch information.
		fn next_epoch() -> Epoch;

		/// Get ring context to be used for ticket proof construction.
		fn ring_context() -> Option<RingContext>;

		/// Submit next epoch validator tickets via an unsigned extrinsic.
		///
		/// This method returns `false` when creation of the extrinsics fails.
		fn submit_tickets_unsigned_extrinsic(tickets: Vec<TicketEnvelope>) -> bool;
	}
}
