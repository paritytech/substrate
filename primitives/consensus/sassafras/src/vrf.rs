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

//! Primitives related to VRF input and output.

pub use merlin::Transcript;

pub use sp_consensus_slots::Slot;
pub use sp_consensus_vrf::schnorrkel::{PublicKey, Randomness, VRFOutput, VRFProof};
#[cfg(feature = "std")]
use sp_keystore::vrf::{VRFTranscriptData, VRFTranscriptValue};

use crate::SASSAFRAS_ENGINE_ID;

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
