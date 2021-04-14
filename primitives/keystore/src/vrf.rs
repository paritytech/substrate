// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

use std::borrow::Cow;

use codec::Encode;
use merlin::Transcript;
use schnorrkel::vrf::{VRFOutput, VRFProof};

/// An enum whose variants represent possible
/// accepted values to construct the VRF transcript
#[derive(Clone, Encode, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum VRFTranscriptValue {
	/// Value is an array of bytes
	Bytes(Vec<u8>),
	/// Value is a u64 integer
	U64(u64),
}
/// VRF Transcript data
#[derive(Clone, Encode, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VRFTranscriptData {
	/// The transcript's label
	pub label: Cow<'static, [u8]>,
	/// Additional data to be registered into the transcript
	pub items: Vec<(Cow<'static, [u8]>, VRFTranscriptValue)>,
}
/// VRF signature data
#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VRFSignature {
	/// The VRFOutput serialized
	pub output: VRFOutput,
	/// The calculated VRFProof
	pub proof: VRFProof,
}

mod cowguard {
    use std::{borrow::Cow, ops::Deref};

	pub enum CowGuardU8 {
		Normal(&'static [u8]),
		Leaked(&'static [u8]),
	}

	impl std::fmt::Debug for CowGuardU8 {
    	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
			match self {
			    CowGuardU8::Normal(r) => write!(f, "Normal@{:p}", *r),
			    CowGuardU8::Leaked(r) => write!(f, "Leaked@{:p}", *r),
			}
		}
	}

	impl Drop for CowGuardU8 {
    	fn drop(&mut self) {
			if let CowGuardU8::Leaked(leaked) = *self {
				unsafe {
					//reclaim the leaked memory
					Box::from_raw(leaked as *const [u8] as *mut [u8]);
				}
			}
		}
	}

	impl Deref for CowGuardU8 {
    	type Target = &'static [u8];

    	fn deref(&self) -> &Self::Target {
			match &self {
			    CowGuardU8::Normal(borrow) => borrow,
			    CowGuardU8::Leaked(leak) => leak,
			}
		}
	}

	impl From<Cow<'static, [u8]>> for CowGuardU8 {
    	fn from(cow: Cow<'static, [u8]>) -> Self {
			match cow {
			    Cow::Borrowed(borrowed) => Self::Normal(borrowed),
			    Cow::Owned(owned) => Self::Leaked(Box::leak(owned.into_boxed_slice())),
			}
		}
	}
}

/// Construct a `Transcript` object from data.
///
/// Returns `merlin::Transcript`
pub fn make_transcript(data: VRFTranscriptData) -> Transcript {
	use cowguard::CowGuardU8 as CowGuard;

	let mut transcript = Transcript::new(*CowGuard::from(data.label));
	for (label, value) in data.items.into_iter() {
		let label = CowGuard::from(label);
		match value {
			VRFTranscriptValue::Bytes(bytes) => {
				transcript.append_message(*label, &bytes);
			},
			VRFTranscriptValue::U64(val) => {
				transcript.append_u64(*label, val);
			}
		}
	}
	transcript
}


#[cfg(test)]
mod tests {
	use super::*;
	use rand::RngCore;
	use rand_chacha::{
		rand_core::SeedableRng,
		ChaChaRng,
	};

	#[test]
	fn transcript_creation_matches() {
		let mut orig_transcript = Transcript::new(b"My label");
		orig_transcript.append_u64(b"one", 1);
		orig_transcript.append_message(b"two", "test".as_bytes());

		let new_transcript = make_transcript(VRFTranscriptData {
			label: Cow::from(&b"My label"[..]),
			items: vec![
				(Cow::from(&b"one"[..]), VRFTranscriptValue::U64(1)),
				(Cow::from(&b"two"[..]), VRFTranscriptValue::Bytes("test".as_bytes().to_vec())),
			],
		});

		let owned_transcript = make_transcript(VRFTranscriptData {
			label: Cow::from(b"My label"[..].to_vec()),
			items: vec![
				(Cow::from(b"one"[..].to_vec()), VRFTranscriptValue::U64(1)),
				(Cow::from(b"two"[..].to_vec()), VRFTranscriptValue::Bytes(b"test"[..].to_vec()))
			]
		});

		let test = |t: Transcript| -> [u8; 16] {
			let mut b = [0u8; 16];
			t.build_rng()
				.finalize(&mut ChaChaRng::from_seed([0u8;32]))
				.fill_bytes(&mut b);
			b
		};

		let orig_test = test(orig_transcript);
		debug_assert!(orig_test == test(new_transcript));
		debug_assert!(orig_test == test(owned_transcript));

	}
}
