// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

/// An enum whose variants represent possible
/// accepted values to construct the VRF transcript
#[derive(Clone, Encode)]
pub enum VRFTranscriptValue<'a> {
	/// Value is an array of bytes
	Bytes(&'a [u8]),
	/// Value is a u64 integer
	U64(u64),
}
/// VRF Transcript data
#[derive(Clone, Encode)]
pub struct VRFTranscriptData<'a> {
	/// The transcript's label
	pub label: &'static [u8],
	/// Additional data to be registered into the transcript
	pub items: Vec<(&'static str, VRFTranscriptValue<'a>)>,
}
/// VRF signature data
pub struct VRFSignature {
	/// The VRFOutput serialized
	pub output: Vec<u8>,
	/// The calculated VRFProof
	pub proof: Vec<u8>,
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
			}
		}
	}
	transcript
}
