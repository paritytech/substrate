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

#[cfg(feature = "std")]
use bytes;
use bytes::Vec;

/// Unique identifier of a parachain.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct Id(u64);

impl From<Id> for u64 {
	fn from(x: Id) -> Self { x.0 }
}

impl From<u64> for Id {
	fn from(x: u64) -> Self { Id(x) }
}

impl ::codec::Slicable for Id {
	fn from_slice(value: &mut &[u8]) -> Option<Self> {
		u64::from_slice(value).map(Id)
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.0.as_slice_then(f)
	}
}

/// Candidate parachain block.
///
/// https://github.com/w3f/polkadot-spec/blob/master/spec.md#candidate-para-chain-block
#[derive(Debug, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub struct Candidate {
	/// The ID of the parachain this is a proposal for.
	pub parachain_index: Id,
	/// Collator's signature
	pub collator_signature: ::Signature,
	/// Unprocessed ingress queue.
	///
	/// Ordered by parachain ID and block number.
	pub unprocessed_ingress: ConsolidatedIngress,
	/// Block data
	pub block: BlockData,
}

/// Candidate receipt type.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub struct CandidateReceipt {
	/// The ID of the parachain this is a candidate for.
	pub parachain_index: Id,
	/// The collator's account ID
	pub collator: ::AccountId,
	/// The head-data
	pub head_data: HeadData,
	/// Balance uploads to the relay chain.
	pub balance_uploads: Vec<(::AccountId, ::uint::U256)>,
	/// Egress queue roots.
	pub egress_queue_roots: Vec<(Id, ::hash::H256)>,
	/// Fees paid from the chain to the relay chain validators
	pub fees: ::uint::U256,
}

/// Parachain ingress queue message.
#[derive(Debug, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct Message(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// Consolidated ingress queue data.
///
/// This is just an ordered vector of other parachains' egress queues,
/// obtained according to the routing rules.
#[derive(Debug, Default, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct ConsolidatedIngress(pub Vec<(Id, Vec<Message>)>);

/// Parachain block data.
///
/// contains everything required to validate para-block, may contain block and witness data
#[derive(Debug, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct BlockData(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// Parachain header raw bytes wrapper type.
#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct Header(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// Parachain head data included in the chain.
#[derive(Debug, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct HeadData(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// Parachain validation code.
#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct ValidationCode(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// Activitiy bit field
#[derive(Debug, PartialEq, Eq, Clone, Default)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct Activity(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

impl ::codec::Slicable for Activity {
	fn from_slice(value: &mut &[u8]) -> Option<Self> {
		Vec::<u8>::from_slice(value).map(Activity)
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.0.as_slice_then(f)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use polkadot_serializer as ser;

	#[test]
	fn test_candidate() {
		assert_eq!(ser::to_string_pretty(&Candidate {
			parachain_index: 5.into(),
			collator_signature: 10.into(),
			unprocessed_ingress: ConsolidatedIngress(vec![
				(Id(1), vec![Message(vec![2])]),
				(Id(2), vec![Message(vec![2]), Message(vec![3])]),
			]),
			block: BlockData(vec![1, 2, 3]),
    }), r#"{
  "parachainIndex": 5,
  "collatorSignature": "0x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a",
  "unprocessedIngress": [
    [
      1,
      [
        "0x02"
      ]
    ],
    [
      2,
      [
        "0x02",
        "0x03"
      ]
    ]
  ],
  "block": "0x010203"
}"#);
	}
}
