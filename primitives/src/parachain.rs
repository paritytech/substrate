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
/// This is just an ordered vector of other parachains' egress queues,
/// obtained according to the routing rules.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CollatedIngress(pub Vec<(Id, Vec<Message>)>);

/// A parachain block proposal.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct Proposal {
	/// Parachain block header bytes.
	pub header: Header,
	/// Hash of data necessary to prove validity of the header.
	pub witness_hash: WitnessHash,
}

/// Parachain header raw bytes wrapper type.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Header(#[serde(with="bytes")] pub Vec<u8>);

/// Hash used to refer to witness of block header.
pub type WitnessHash = ::hash::H256;

/// Raw witness data.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RawWitness(#[serde(with="bytes")] pub Vec<u8>);

impl RawWitness {
	/// Compute and store the hash of the witness
	pub fn into_witness(self) -> Witness {
		let hash = ::hash(&self.0);
		Witness(self, hash)
	}
}

/// Parachain witness data.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Witness(RawWitness, WitnessHash);

impl Witness {
	/// Get raw witness data.
	pub fn raw(&self) -> &RawWitness { &self.0 }

	/// Get hash of witness data.
	pub fn hash(&self) -> &WitnessHash { &self.1 }

	/// Decompose the witness back into raw data and hash.
	pub fn into_inner(self) -> (RawWitness, WitnessHash) {
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
	fn test_witness_serialization() {
		assert_eq!(
			ser::to_string_pretty(&Witness(RawWitness(vec![1,2,3]), 5.into())),
			r#"[
  "0x010203",
  "0x0000000000000000000000000000000000000000000000000000000000000005"
]"#
		)
	}
}
