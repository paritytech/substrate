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

use codec::{Decode, Encode};
use scale_info::TypeInfo;
use sp_runtime::traits::Block;
use sp_std::prelude::*;

/// Id of different payloads in the [`crate::Commitment`] data.
pub type BeefyPayloadId = [u8; 2];

/// Registry of all known [`BeefyPayloadId`].
pub mod known_payloads {
	use crate::BeefyPayloadId;

	/// A [`Payload`](super::Payload) identifier for Merkle Mountain Range root hash.
	///
	/// Encoded value should contain a [`crate::MmrRootHash`] type (i.e. 32-bytes hash).
	pub const MMR_ROOT_ID: BeefyPayloadId = *b"mh";
}

/// A BEEFY payload type allowing for future extensibility of adding additional kinds of payloads.
///
/// The idea is to store a vector of SCALE-encoded values with an extra identifier.
/// Identifiers MUST be sorted by the [`BeefyPayloadId`] to allow efficient lookup of expected
/// value. Duplicated identifiers are disallowed. It's okay for different implementations to only
/// support a subset of possible values.
#[derive(Decode, Encode, Debug, PartialEq, Eq, Clone, Ord, PartialOrd, Hash, TypeInfo)]
pub struct Payload(Vec<(BeefyPayloadId, Vec<u8>)>);

impl Payload {
	/// Construct a new payload given an initial vallue
	pub fn from_single_entry(id: BeefyPayloadId, value: Vec<u8>) -> Self {
		Self(vec![(id, value)])
	}

	/// Returns a raw payload under given `id`.
	///
	/// If the [`BeefyPayloadId`] is not found in the payload `None` is returned.
	pub fn get_raw(&self, id: &BeefyPayloadId) -> Option<&Vec<u8>> {
		let index = self.0.binary_search_by(|probe| probe.0.cmp(id)).ok()?;
		Some(&self.0[index].1)
	}

	/// Returns a decoded payload value under given `id`.
	///
	/// In case the value is not there or it cannot be decoded does not match `None` is returned.
	pub fn get_decoded<T: Decode>(&self, id: &BeefyPayloadId) -> Option<T> {
		self.get_raw(id).and_then(|raw| T::decode(&mut &raw[..]).ok())
	}

	/// Push a `Vec<u8>` with a given id into the payload vec.
	/// This method will internally sort the payload vec after every push.
	///
	/// Returns self to allow for daisy chaining.
	pub fn push_raw(mut self, id: BeefyPayloadId, value: Vec<u8>) -> Self {
		self.0.push((id, value));
		self.0.sort_by_key(|(id, _)| *id);
		self
	}
}

/// Trait for custom BEEFY payload providers.
pub trait PayloadProvider<B: Block> {
	/// Provide BEEFY payload if available for `header`.
	fn payload(&self, header: &B::Header) -> Option<Payload>;
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn payload_methods_work_as_expected() {
		let id1: BeefyPayloadId = *b"hw";
		let msg1: String = "1. Hello World!".to_string();
		let id2: BeefyPayloadId = *b"yb";
		let msg2: String = "2. Yellow Board!".to_string();
		let id3: BeefyPayloadId = *b"cs";
		let msg3: String = "3. Cello Cord!".to_string();

		let payload = Payload::from_single_entry(id1, msg1.encode())
			.push_raw(id2, msg2.encode())
			.push_raw(id3, msg3.encode());

		assert_eq!(payload.get_decoded(&id1), Some(msg1));
		assert_eq!(payload.get_decoded(&id2), Some(msg2));
		assert_eq!(payload.get_raw(&id3), Some(&msg3.encode()));
		assert_eq!(payload.get_raw(&known_payloads::MMR_ROOT_ID), None);
	}
}
