// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! VRF-specifc data types and helpers

use codec::Encode;
use merlin::Transcript;
use schnorrkel::vrf::{VRFOutput, VRFProof};

/// An enum whose variants represent possible
/// accepted values to construct the VRF transcript
#[derive(Clone, Encode)]
#[cfg_attr(feature = "std", derive(serde::Serialize, serde::Deserialize))]
pub enum VRFTranscriptValue {
	/// Value is an array of bytes
	Bytes(Vec<u8>),
	/// Value is a u64 integer
	U64(u64),
}
/// VRF Transcript data
#[derive(Clone, Encode)]
pub struct VRFTranscriptData {
	/// The transcript's label
	pub label: &'static [u8],
	/// Additional data to be registered into the transcript
	pub items: Vec<(&'static str, VRFTranscriptValue)>,
}
/// VRF signature data
pub struct VRFSignature {
	/// The VRFOutput serialized
	pub output: VRFOutput,
	/// The calculated VRFProof
	pub proof: VRFProof,
}

/// Construct a `Transcript` object from data.
///
/// Returns `merlin::Transcript`
pub fn make_transcript(data: VRFTranscriptData) -> Transcript {
	let mut transcript = Transcript::new(data.label);
	for (label, value) in data.items.into_iter() {
		match value {
			VRFTranscriptValue::Bytes(bytes) => {
				transcript.append_message(label.as_bytes(), &bytes);
			},
			VRFTranscriptValue::U64(val) => {
				transcript.append_u64(label.as_bytes(), val);
			},
		}
	}
	transcript
}

#[cfg(test)]
mod tests {
	use super::*;
	use rand::RngCore;
	use rand_chacha::{rand_core::SeedableRng, ChaChaRng};

	#[test]
	fn transcript_creation_matches() {
		let mut orig_transcript = Transcript::new(b"My label");
		orig_transcript.append_u64(b"one", 1);
		orig_transcript.append_message(b"two", "test".as_bytes());

		let new_transcript = make_transcript(VRFTranscriptData {
			label: b"My label",
			items: vec![
				("one", VRFTranscriptValue::U64(1)),
				("two", VRFTranscriptValue::Bytes("test".as_bytes().to_vec())),
			],
		});
		let test = |t: Transcript| -> [u8; 16] {
			let mut b = [0u8; 16];
			t.build_rng().finalize(&mut ChaChaRng::from_seed([0u8; 32])).fill_bytes(&mut b);
			b
		};
		debug_assert!(test(orig_transcript) == test(new_transcript));
	}
}
