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

use rstd::fmt;
use rstd::vec::Vec;
#[cfg(feature = "std")]
use bytes;
use Hash;
use codec::{Input, Slicable};

/// Used to refer to a block number.
pub type Number = u64;

/// Hash used to refer to a block hash.
pub type HeaderHash = Hash;

/// Hash used to refer to an extrinsic.
pub type ExtrinsicHash = Hash;

/// Simple generic extrinsic type.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct Extrinsic(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

impl Slicable for Extrinsic {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Vec::<u8>::decode(input).map(Extrinsic)
	}

	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.0.using_encoded(f)
	}
}

/// Execution log (event)
#[derive(PartialEq, Eq, Clone, Default)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct Log(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

impl Slicable for Log {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Vec::<u8>::decode(input).map(Log)
	}

	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.0.using_encoded(f)
	}
}

/// The digest of a block, useful for light-clients.
#[derive(Clone, Default, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct Digest {
	/// All logs that have happened in the block.
	pub logs: Vec<Log>,
}

impl Slicable for Digest {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Vec::<Log>::decode(input).map(|logs| Digest { logs })
	}

	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.logs.using_encoded(f)
	}
}

/// Generic types to be specialised later.
pub mod generic {
	use super::{Header, Slicable, Input, Vec};

	/// A Block - this is generic for later specialisation in particular runtimes.
	#[derive(PartialEq, Eq, Clone)]
	#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
	pub struct Block<Transaction: PartialEq + Eq + Clone> {
		/// The block header.
		pub header: Header,
		/// All relay-chain transactions.
		pub transactions: Vec<Transaction>,
	}

	impl<T: PartialEq + Eq + Clone> Slicable for Block<T> where Vec<T>: Slicable {
		fn decode<I: Input>(input: &mut I) -> Option<Self> {
			Some(Block {
				header: Slicable::decode(input)?,
				transactions: Slicable::decode(input)?,
			})
		}

		fn encode(&self) -> Vec<u8> {
			let mut v: Vec<u8> = Vec::new();
			v.extend(self.header.encode());
			v.extend(self.transactions.encode());
			v
		}
	}
}

/// The body of a block is just a bunch of extrinsics.
pub type Body = Vec<Extrinsic>;
/// The header and body of a concrete, but unspecialised, block. Used by substrate to represent a
/// block some fields of which the runtime alone knows how to interpret (e.g. the transactions).
pub type Block = generic::Block<Extrinsic>;

/// A substrate chain block header.
// TODO: split out into light-client-specific fields and runtime-specific fields.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub struct Header {
	/// Block parent's hash.
	pub parent_hash: HeaderHash,
	/// Block number.
	pub number: Number,
	/// State root after this transition.
	pub state_root: Hash,
	/// The root of the trie that represents this block's transactions, indexed by a 32-byte integer.
	pub extrinsics_root: Hash,
	// TODO...
//	/// The root of the trie that represents the receipts from this block's transactions
//	pub receipts_root: Hash,
	/// The digest of activity on the block.
	pub digest: Digest,
}

impl Header {
	/// Create a new instance with default fields except `number`, which is given as an argument.
	pub fn from_block_number(number: Number) -> Self {
		Header {
			parent_hash: Default::default(),
			number,
			state_root: Default::default(),
			extrinsics_root: Default::default(),
			digest: Default::default(),
		}
	}
}

impl Slicable for Header {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(Header {
			parent_hash: Slicable::decode(input)?,
			number: Slicable::decode(input)?,
			state_root: Slicable::decode(input)?,
			extrinsics_root: Slicable::decode(input)?,
			digest: Slicable::decode(input)?,
		})
	}

	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		self.parent_hash.using_encoded(|s| v.extend(s));
		self.number.using_encoded(|s| v.extend(s));
		self.state_root.using_encoded(|s| v.extend(s));
		self.extrinsics_root.using_encoded(|s| v.extend(s));
		self.digest.using_encoded(|s| v.extend(s));

		v
	}
}

/// Block indentification.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum Id {
	/// Identify by block header hash.
	Hash(HeaderHash),
	/// Identify by block number.
	Number(Number),
}

impl fmt::Display for Id {
	fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
		match *self {
			Id::Hash(h) => h.fmt(f),
			Id::Number(n) => n.fmt(f),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use codec::Slicable;
	use substrate_serializer as ser;

	#[test]
	fn test_header_encoding() {
		let header = Header {
			parent_hash: 5.into(),
			number: 67,
			state_root: 3.into(),
			extrinsics_root: 6.into(),
			digest: Digest { logs: vec![Log(vec![1]), Log(vec![2])] },
		};

		assert_eq!(header.encode(), vec![
			// parent_hash
			0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
			// number
			67, 0, 0, 0, 0, 0, 0, 0,
			// state_root
			0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3,
			// extrinsics_root
			0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6,
			// digest (length, log1, log2)
			2, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 2
		]);
	}

	#[test]
	fn test_header_serialization() {
		let header = Header {
			parent_hash: 5.into(),
			number: 67,
			state_root: 3.into(),
			extrinsics_root: 6.into(),
			digest: Digest { logs: vec![Log(vec![1])] },
		};

		assert_eq!(ser::to_string_pretty(&header), r#"{
  "parentHash": "0x0000000000000000000000000000000000000000000000000000000000000005",
  "number": 67,
  "stateRoot": "0x0000000000000000000000000000000000000000000000000000000000000003",
  "extrinsicsRoot": "0x0000000000000000000000000000000000000000000000000000000000000006",
  "digest": {
    "logs": [
      "0x01"
    ]
  }
}"#);

		let v = header.encode();
		assert_eq!(Header::decode(&mut &v[..]).unwrap(), header);
	}

	#[test]
	fn test_block_encoding() {
		let block = Block {
			header: Header::from_block_number(12),
			transactions: vec![Extrinsic(vec!(4))],
		};

		assert_eq!(block.encode(), vec![
			// parent_hash
			0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
			// number
			12, 0, 0, 0, 0, 0, 0, 0,
			// state_root
			0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
			// extrinsics_root
			0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
			// digest
			0, 0, 0, 0,
			// transactions (length, tx...)
			1, 0, 0, 0, 1, 0, 0, 0, 4
		]);
	}
}
