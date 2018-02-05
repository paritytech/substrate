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
use codec::Slicable;
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

impl Slicable for Log {
	fn from_slice(value: &mut &[u8]) -> Option<Self> {
		Vec::<u8>::from_slice(value).map(Log)
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.0.as_slice_then(f)
	}
}

impl ::codec::NonTrivialSlicable for Log { }

/// The digest of a block, useful for light-clients.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Digest {
	/// All logs that have happened in the block.
	pub logs: Vec<Log>,
}

impl Slicable for Digest {
	fn from_slice(value: &mut &[u8]) -> Option<Self> {
		Vec::<Log>::from_slice(value).map(|logs| Digest { logs })
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.logs.as_slice_then(f)
	}
}

/// A Polkadot relay chain block.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct Block {
	/// The block header.
	pub header: Header,
	/// All relay-chain transactions.
	pub transactions: Vec<UncheckedTransaction>,
}

impl Slicable for Block {
	fn from_slice(value: &mut &[u8]) -> Option<Self> {
		Some(Block {
			header: try_opt!(Slicable::from_slice(value)),
			transactions: try_opt!(Slicable::from_slice(value)),
		})
	}

	fn to_vec(&self) -> Vec<u8> {
		let mut v = Vec::new();

		v.extend(self.header.to_vec());
		v.extend(self.transactions.to_vec());

		v
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(self.to_vec().as_slice())
	}
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
	/// The digest of activity on the block.
	pub digest: Digest,
}

impl Slicable for Header {
	fn from_slice(value: &mut &[u8]) -> Option<Self> {
		Some(Header {
			parent_hash: try_opt!(Slicable::from_slice(value)),
			number: try_opt!(Slicable::from_slice(value)),
			state_root: try_opt!(Slicable::from_slice(value)),
			transaction_root: try_opt!(Slicable::from_slice(value)),
			digest: try_opt!(Slicable::from_slice(value)),
		})
	}

	fn to_vec(&self) -> Vec<u8> {
		let mut v = Vec::new();

		self.parent_hash.as_slice_then(|s| v.extend(s));
		self.number.as_slice_then(|s| v.extend(s));
		self.state_root.as_slice_then(|s| v.extend(s));
		self.transaction_root.as_slice_then(|s| v.extend(s));
		self.digest.as_slice_then(|s| v.extend(s));

		v
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(self.to_vec().as_slice())
	}
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
	use codec::Slicable;
	use polkadot_serializer as ser;

	#[test]
	fn test_header_serialization() {
		let header = Header {
			parent_hash: 5.into(),
			number: 67,
			state_root: 3.into(),
			transaction_root: 6.into(),
			digest: Digest { logs: vec![Log(vec![1])] },
		};

		assert_eq!(ser::to_string_pretty(&header), r#"{
  "parentHash": "0x0000000000000000000000000000000000000000000000000000000000000005",
  "number": 67,
  "stateRoot": "0x0000000000000000000000000000000000000000000000000000000000000003",
  "transactionRoot": "0x0000000000000000000000000000000000000000000000000000000000000006",
  "digest": {
    "logs": [
      "0x01"
    ]
  }
}"#);

		let v = header.to_vec();
		assert_eq!(Header::from_slice(&mut &v[..]).unwrap(), header);
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
