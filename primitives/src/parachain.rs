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

//! Parachain data types.

use bytes;

/// Unique identifier of a parachain.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Serialize, Deserialize)]
pub struct Id(u64);

impl From<Id> for u64 {
	fn from(x: Id) -> Self { x.0 }
}

impl From<u64> for Id {
	fn from(x: u64) -> Self { Id(x) }
}

/// A cross-parachain message.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Serialize, Deserialize)]
pub struct Message(#[serde(with="bytes")] pub Vec<u8>);

/// Posts to egress queues.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EgressPosts(pub ::std::collections::BTreeMap<::parachain::Id, Vec<::parachain::Message>>);

/// A collated ingress queue.
///
/// This is just an ordered vector of other parachains' egress queues,
/// obtained according to the routing rules.
#[derive(Default, Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsolidatedIngress(pub Vec<(Id, Vec<Message>)>);

/// A parachain block proposal.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct Candidate {
	/// Parachain ID
	pub id: Id,

	/// Consolidated ingress queues.
	///
	/// This will always be the same for each valid proposal building on the
	/// same relay chain block.
	pub ingress: ConsolidatedIngress,

	/// Hash of data necessary to prove validity of the head data.
	pub proof_hash: ProofHash,
}

/// Parachain head data raw bytes wrapper type.
///
/// The notion of a header is a little too specific for parachains.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HeadData(#[serde(with="bytes")] pub Vec<u8>);

/// Hash used to refer to proof of block head data.
pub type ProofHash = ::hash::H256;

/// Raw proof data.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RawProof(#[serde(with="bytes")] pub Vec<u8>);

impl RawProof {
	/// Compute and store the hash of the proof
	pub fn into_proof(self) -> Proof {
		let hash = ::hash(&self.0);
		Proof(self, hash)
	}
}

/// Parachain proof data. This is passed to the validation function
/// along with the ingress queue and produces head data.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Proof(RawProof, ProofHash);

impl Proof {
	/// Get raw proof data.
	pub fn raw(&self) -> &RawProof { &self.0 }

	/// Get hash of proof data.
	pub fn hash(&self) -> &ProofHash { &self.1 }

	/// Decompose the proof back into raw data and hash.
	pub fn into_inner(self) -> (RawProof, ProofHash) {
		(self.0, self.1)
	}
}

/// Parachain validation code.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ValidationCode(#[serde(with="bytes")] pub Vec<u8>);

#[cfg(test)]
mod tests {
	use super::*;
	use polkadot_serializer as ser;

	#[test]
	fn test_proof_serialization() {
		assert_eq!(
			ser::to_string_pretty(&Proof(RawProof(vec![1,2,3]), 5.into())),
			r#"[
  "0x010203",
  "0x0000000000000000000000000000000000000000000000000000000000000005"
]"#
		)
	}
}
