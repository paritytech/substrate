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

#![deny(warnings)]
#![forbid(unsafe_code, missing_docs, unused_variables, unused_imports)]
#![cfg_attr(not(feature = "std"), no_std)]

pub use merlin::Transcript;

use scale_codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
#[cfg(feature = "std")]
use serde::{Deserialize, Serialize};
use sp_core::{crypto, U256};
#[cfg(feature = "std")]
use sp_keystore::vrf::{VRFTranscriptData, VRFTranscriptValue};
use sp_runtime::{ConsensusEngineId, RuntimeDebug};
use sp_std::vec::Vec;

pub use sp_consensus_slots::{Slot, SlotDuration};
pub use sp_consensus_vrf::schnorrkel::{
	Randomness, VRFInOut, VRFOutput, VRFProof, RANDOMNESS_LENGTH, VRF_OUTPUT_LENGTH,
	VRF_PROOF_LENGTH,
};

/// Key type for Sassafras module.
pub const KEY_TYPE: crypto::KeyTypeId = sp_application_crypto::key_types::SASSAFRAS;

pub mod digests;
pub mod inherents;

mod app {
	use sp_application_crypto::{app_crypto, key_types::SASSAFRAS, sr25519};
	app_crypto!(sr25519, SASSAFRAS);
}

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

/// The `ConsensusEngineId` of BABE.
pub const SASSAFRAS_ENGINE_ID: ConsensusEngineId = *b"SASS";

/// The length of the public key
pub const PUBLIC_KEY_LENGTH: usize = 32;

/// The weight of an authority.
// NOTE: we use a unique name for the weight to avoid conflicts with other
// `Weight` types, since the metadata isn't able to disambiguate.
pub type SassafrasAuthorityWeight = u64;

/// Weight of a Sassafras block.
/// Primary blocks have a weight of 1 whereas secondary blocks have a weight of 0.
pub type SassafrasBlockWeight = u32;

/// Configuration data used by the Sassafras consensus engine.
#[derive(Clone, Encode, Decode, RuntimeDebug, PartialEq, Eq)]
pub struct SassafrasGenesisConfiguration {
	/// The slot duration in milliseconds for Sassafras.
	pub slot_duration: u64,
	/// The duration of epochs in slots.
	pub epoch_length: u64,
	/// The authorities for the genesis epoch.
	pub genesis_authorities: Vec<(AuthorityId, SassafrasAuthorityWeight)>,
	/// The randomness for the genesis epoch.
	pub randomness: Randomness,
}

/// Configuration data used by the Sassafras consensus engine that can be modified on epoch change.
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, MaxEncodedLen, TypeInfo)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct SassafrasEpochConfiguration {
	// TODO-SASS-P2
	// x: redundancy_factor
	// a: attempts number
	// L: bound on aa number of tickets that can be gossiped
}

// Sensible defaults for Sassafras epoch configuration.
impl Default for SassafrasEpochConfiguration {
	fn default() -> Self {
		SassafrasEpochConfiguration {
            // TODO-SASS-P2
        }
	}
}

/// Ticket type.
pub type Ticket = VRFOutput;

/// Ticket information.
#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub struct TicketInfo {
	/// Authority index.
	pub authority_index: u32,
	/// Attempt number.
	pub attempt: u32,
	/// Ticket proof.
	pub proof: VRFProof,
}

const TYPE_LABEL: &str = "type";
const EPOCH_LABEL: &str = "epoch";
const SLOT_LABEL: &str = "slot";
const ATTEMPT_LABEL: &str = "slot";
const RANDOMNESS_LABEL: &str = "randomness";

const SLOT_VRF_TYPE_VALUE: &str = "slot-vrf";
const TICKET_VRF_TYPE_VALUE: &str = "ticket-vrf";

/// Make slot VRF transcript.
pub fn make_slot_transcript(randomness: &Randomness, slot: Slot, epoch: u64) -> Transcript {
	let mut transcript = Transcript::new(&SASSAFRAS_ENGINE_ID);
	transcript.append_message(TYPE_LABEL.as_bytes(), SLOT_VRF_TYPE_VALUE.as_bytes());
	transcript.append_u64(SLOT_LABEL.as_bytes(), *slot);
	transcript.append_u64(EPOCH_LABEL.as_bytes(), epoch);
	transcript.append_message(RANDOMNESS_LABEL.as_bytes(), randomness);
	transcript
}

/// Make slot VRF transcript data container.
#[cfg(feature = "std")]
pub fn make_slot_transcript_data(
	randomness: &Randomness,
	slot: Slot,
	epoch: u64,
) -> VRFTranscriptData {
	VRFTranscriptData {
		label: &SASSAFRAS_ENGINE_ID,
		items: vec![
			(TYPE_LABEL, VRFTranscriptValue::Bytes(SLOT_VRF_TYPE_VALUE.as_bytes().to_vec())),
			(SLOT_LABEL, VRFTranscriptValue::U64(*slot)),
			(EPOCH_LABEL, VRFTranscriptValue::U64(epoch)),
			(RANDOMNESS_LABEL, VRFTranscriptValue::Bytes(randomness.to_vec())),
		],
	}
}

/// Make ticket VRF transcript.
pub fn make_ticket_transcript(randomness: &Randomness, attempt: u32, epoch: u64) -> Transcript {
	let mut transcript = Transcript::new(&SASSAFRAS_ENGINE_ID);
	transcript.append_message(TYPE_LABEL.as_bytes(), TICKET_VRF_TYPE_VALUE.as_bytes());
	transcript.append_u64(ATTEMPT_LABEL.as_bytes(), attempt as u64);
	transcript.append_u64(EPOCH_LABEL.as_bytes(), epoch);
	transcript.append_message(RANDOMNESS_LABEL.as_bytes(), randomness);
	transcript
}

/// Make ticket VRF transcript data container.
#[cfg(feature = "std")]
pub fn make_ticket_transcript_data(
	randomness: &Randomness,
	attempt: u32,
	epoch: u64,
) -> VRFTranscriptData {
	VRFTranscriptData {
		label: &SASSAFRAS_ENGINE_ID,
		items: vec![
			(TYPE_LABEL, VRFTranscriptValue::Bytes(TICKET_VRF_TYPE_VALUE.as_bytes().to_vec())),
			(ATTEMPT_LABEL, VRFTranscriptValue::U64(attempt as u64)),
			(EPOCH_LABEL, VRFTranscriptValue::U64(epoch)),
			(RANDOMNESS_LABEL, VRFTranscriptValue::Bytes(randomness.to_vec())),
		],
	}
}

sp_api::decl_runtime_apis! {
	/// API necessary for block authorship with Sassafras.
	pub trait SassafrasApi {
		 /// Return the genesis configuration for Sassafras. The configuration is only read on genesis.
		fn configuration() -> SassafrasGenesisConfiguration;

		/// Submit next epoch validator tickets via an unsigned extrinsic.
		/// This method returns `false` when creation of the extrinsics fails.
		fn submit_tickets_unsigned_extrinsic(tickets: Vec<Ticket>) -> bool;

		/// Get expected ticket for the given slot.
		fn slot_ticket(slot: Slot) -> Option<Ticket>;
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
pub fn compute_threshold(redundancy: u32, slots: u32, attempts: u32, validators: u32) -> U256 {
	let den = attempts as u64 * validators as u64;
	let num = redundancy as u64 * slots as u64;
	U256::max_value()
		.checked_div(den.into())
		.unwrap_or(U256::zero())
		.saturating_mul(num.into())
}

/// Returns true if the given VRF output is lower than the given threshold, false otherwise.
#[inline]
pub fn check_threshold(ticket: &Ticket, threshold: U256) -> bool {
	U256::from(ticket.as_bytes()) < threshold
}

/// TODO-SASS-P3: add to session config
pub const TICKET_MAX_ATTEMPTS: u32 = 30;

/// TODO-SASS-P3: add to session config
pub const TICKET_REDUNDANCY_FACTOR: u32 = 1;
