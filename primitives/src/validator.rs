// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Validator primitives.

use bytes;

/// Parachain incoming messages.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IngressPosts(#[serde(with="bytes")] pub Vec<u8>);

/// Parachain incoming messages delta.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IngressPostsDelta(#[serde(with="bytes")] pub Vec<u8>);

/// Parachain outgoing messages.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EgressPosts(#[serde(with="bytes")] pub Vec<u8>);

/// Validity result of particular proof and ingress queue.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag="type", content="data")]
pub enum ProofValidity {
	/// The proof is invalid.
	#[serde(rename="invalid")]
	Invalid,
	#[serde(rename="valid")]
	/// The proof is processed and new egress queue is created.
	/// Also includes current ingress queue delta.
	Valid(IngressPostsDelta, EgressPosts),
}

impl ProofValidity {
	/// The proof is valid.
	pub fn is_valid(&self) -> bool {
		match *self {
			ProofValidity::Invalid => false,
			ProofValidity::Valid(..) => true,
		}
	}
}

impl From<Option<(IngressPostsDelta, EgressPosts)>> for ProofValidity {
	fn from(posts: Option<(IngressPostsDelta, EgressPosts)>) -> Self {
		match posts {
			Some((delta, posts)) => ProofValidity::Valid(delta, posts),
			None => ProofValidity::Invalid,
		}
	}
}

// TODO [ToDr] This shouldn't be here!
/// Validator logic.
pub trait Validator {
	/// Validation error.
	type Error: ::std::error::Error;

	/// Validates if the provided proof holds given a current ingress queue.
	///
	/// In case of success produces egress posts.
	fn validate(
		&self,
		messages: &IngressPosts,
		proof: &::parachain::Proof,
		code: &[u8],
	) -> Result<ProofValidity, Self::Error>;
}

#[cfg(test)]
mod tests {
	use super::*;
	use polkadot_serializer as ser;

	#[test]
	fn test_proof_validity_serialization() {
		assert_eq!(
			ser::to_string_pretty(&ProofValidity::Invalid),
			r#"{
  "type": "invalid"
}"#);
		assert_eq!(
			ser::to_string_pretty(&ProofValidity::Valid(IngressPostsDelta(vec![1]), EgressPosts(vec![1, 2, 3]))),
			r#"{
  "type": "valid",
  "data": [
    "0x01",
    "0x010203"
  ]
}"#);
	}
}
