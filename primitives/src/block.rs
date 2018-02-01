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

//! Block and header type definitions.

use bytes::{self, Vec};
use hash::H256;
use parachain;
use transaction::UncheckedTransaction;

/// Used to refer to a block number.
pub type Number = u64;

/// Hash used to refer to a block hash.
pub type HeaderHash = H256;

/// Hash used to refer to a transaction hash.
pub type TransactionHash = H256;

/// Execution log (event)
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct Log(#[serde(with="bytes")] pub Vec<u8>);

/// A Polkadot relay chain block.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct Block {
	/// The block header.
	pub header: Header,
	/// All relay-chain transactions.
	pub transactions: Vec<UncheckedTransaction>,
}

/// The digest of a block, useful for light-clients.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Digest {
	/// All logs that have happened in the block.
	pub logs: Vec<Log>,
}

/// A relay chain block header.
///
/// https://github.com/w3f/polkadot-spec/blob/master/spec.md#header
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct Header {
	/// Block parent's hash.
	pub parent_hash: HeaderHash,
	/// Block number.
	pub number: Number,
	/// State root after this transition.
	pub state_root: H256,
	/// The root of the trie that represents this block's transactions, indexed by a 32-byte integer.
	pub transaction_root: H256,
	/// Parachain activity bitfield
	pub parachain_activity: parachain::Activity,
	/// The digest of activity on the block.
	pub digest: Digest,
}

/// A relay chain block body.
///
/// Included candidates should be sorted by parachain ID, and without duplicate
/// IDs.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct Body {
	/// Parachain proposal blocks.
	pub candidates: Vec<parachain::Candidate>,
}

#[cfg(test)]
mod tests {
	use super::*;
	use polkadot_serializer as ser;

	#[test]
	fn test_header_serialization() {
		assert_eq!(ser::to_string_pretty(&Header {
			parent_hash: 5.into(),
			number: 67,
			state_root: 3.into(),
			parachain_activity: parachain::Activity(vec![0]),
			logs: vec![Log(vec![1])],
		}), r#"{
  "parentHash": "0x0000000000000000000000000000000000000000000000000000000000000005",
  "number": 67,
  "stateRoot": "0x0000000000000000000000000000000000000000000000000000000000000003",
  "parachainActivity": "0x00",
  "logs": [
    "0x01"
  ]
}"#);
	}

	#[test]
	fn test_body_serialization() {
		assert_eq!(ser::to_string_pretty(&Body {
			candidates: vec![
				parachain::Candidate {
					parachain_index: 10.into(),
					collator_signature: Default::default(),
					unprocessed_ingress: Default::default(),
					block: ::parachain::BlockData(vec![1, 3, 5, 8]),
				}
			],
		}), r#"{
  "candidates": [
    {
      "parachainIndex": 10,
      "collatorSignature": "0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
      "unprocessedIngress": [],
      "block": "0x01030508"
    }
  ]
}"#);
	}

}
