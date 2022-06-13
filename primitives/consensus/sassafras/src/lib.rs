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

// TODO-SASS : decomment this
//#![deny(warnings)]
//#![forbid(unsafe_code, missing_docs, unused_variables, unused_imports)]
#![cfg_attr(not(feature = "std"), no_std)]
// TODO-SASS: temporary
#![allow(unused_imports)]

pub use merlin::Transcript;

use scale_codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
#[cfg(feature = "std")]
use serde::{Deserialize, Serialize};
#[cfg(feature = "std")]
use sp_keystore::vrf::{VRFTranscriptData, VRFTranscriptValue};
use sp_runtime::{ConsensusEngineId, RuntimeDebug};
use sp_std::vec::Vec;

pub use sp_consensus_slots::{Slot, SlotDuration};
pub use sp_consensus_vrf::schnorrkel::{
	Randomness, RANDOMNESS_LENGTH, VRF_OUTPUT_LENGTH, VRF_PROOF_LENGTH,
};

/// Key type for Sassafras module.
pub const KEY_TYPE: sp_core::crypto::KeyTypeId = sp_application_crypto::key_types::SASSAFRAS;

pub mod digests;
pub mod inherents;

mod app {
	use sp_application_crypto::{app_crypto, key_types::SASSAFRAS, sr25519};
	app_crypto!(sr25519, SASSAFRAS);
}

/// The index of an authority.
pub type AuthorityIndex = u32;

/// BABE VRFInOut context.
pub const SASSAFRAS_VRF_INOUT_CONTEXT: &[u8] = b"BabeVRFInOutContext";

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
	// TODO-SASS
}

/// Configuration data used by the Sassafras consensus engine that can be modified on epoch change.
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, MaxEncodedLen, TypeInfo)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct SassafrasEpochConfiguration {
	// TODO-SASS
}

/// Make a VRF transcript from given randomness, slot number and epoch.
pub fn make_transcript(randomness: &Randomness, slot: Slot, epoch: u64) -> Transcript {
	let mut transcript = Transcript::new(&SASSAFRAS_ENGINE_ID);
	transcript.append_u64(b"slot number", *slot);
	transcript.append_u64(b"current epoch", epoch);
	transcript.append_message(b"chain randomness", &randomness[..]);
	transcript
}

/// Make a VRF transcript data container
#[cfg(feature = "std")]
pub fn make_transcript_data(randomness: &Randomness, slot: Slot, epoch: u64) -> VRFTranscriptData {
	VRFTranscriptData {
		label: &SASSAFRAS_ENGINE_ID,
		items: vec![
			("slot number", VRFTranscriptValue::U64(*slot)),
			("current epoch", VRFTranscriptValue::U64(epoch)),
			("chain randomness", VRFTranscriptValue::Bytes(randomness.to_vec())),
		],
	}
}

sp_api::decl_runtime_apis! {
	/// API necessary for block authorship with Sassafras.
	pub trait SassafrasApi {
		/// Return the genesis configuration for Sassafras. The configuration is only read on genesis.
		fn configuration() -> SassafrasGenesisConfiguration;

		// TODO-SASS: incomplete API
	}
}
