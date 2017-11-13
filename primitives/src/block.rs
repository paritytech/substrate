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

use hash::H256;
use parachain;

/// Hash used to refer to a block hash.
pub type HeaderHash = H256;

/// A relay chain block header.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct Header {
	/// Block parent's hash.
	pub parent_hash: HeaderHash,
	/// State root after this transition.
	pub state_root: H256,
	/// Unix time at which this header was produced.
	pub timestamp: u64,
	/// Block number.
	pub number: u64,
}

/// A relay chain block body.
///
/// Included candidates should be sorted by parachain ID, and without duplicate
/// IDs.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct Body {
	/// Parachain proposal blocks.
	pub para_blocks: Vec<parachain::Proposal>,
}


#[cfg(test)]
mod tests {
	use super::*;
	use polkadot_serializer as ser;

	#[test]
	fn test_header_serialization() {
		assert_eq!(ser::to_string_pretty(&Header {
			parent_hash: 5.into(),
			state_root: 3.into(),
			timestamp: 10,
			number: 67,
		}), r#"{
  "parentHash": "0x0000000000000000000000000000000000000000000000000000000000000005",
  "stateRoot": "0x0000000000000000000000000000000000000000000000000000000000000003",
  "timestamp": 10,
  "number": 67
}"#);
	}

	#[test]
	fn test_body_serialization() {
		assert_eq!(ser::to_string_pretty(&Body {
			para_blocks: vec![
				parachain::Proposal {
					parachain: 5.into(),
					header: parachain::Header(vec![1, 2, 3, 4]),
					proof_hash: 5.into(),
				}
			],
		}), r#"{
  "paraBlocks": [
    {
      "parachain": 5,
      "header": "0x01020304",
      "proofHash": "0x0000000000000000000000000000000000000000000000000000000000000005"
    }
  ]
}"#);
	}
}
