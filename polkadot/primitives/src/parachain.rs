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
use primitives::bytes;
use primitives;
use codec::{Input, Slicable, NonTrivialSlicable};
use rstd::vec::Vec;

/// Unique identifier of a parachain.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct Id(u32);

impl From<Id> for u32 {
	fn from(x: Id) -> Self { x.0 }
}

impl From<u32> for Id {
	fn from(x: u32) -> Self { Id(x) }
}

impl Slicable for Id {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		u32::decode(input).map(Id)
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.0.as_slice_then(f)
	}
}

/// Identifier for a chain, either one of a number of parachains or the relay chain.
#[derive(Copy, Clone, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum Chain {
	/// The relay chain.
	Relay,
	/// A parachain of the given index.
	Parachain(Id),
}

impl Slicable for Chain {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		let disc = try_opt!(u8::decode(input));

		match disc {
			0 => Some(Chain::Relay),
			1 => Some(Chain::Parachain(try_opt!(Slicable::decode(input)))),
			_ => None,
		}
	}

	fn to_vec(&self) -> Vec<u8> {
		let mut v = Vec::new();
		match *self {
			Chain::Relay => { 0u8.as_slice_then(|s| v.extend(s)); }
			Chain::Parachain(id) => {
				1u8.as_slice_then(|s| v.extend(s));
				id.as_slice_then(|s| v.extend(s));
			}
		}

		v
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(&self.to_vec().as_slice())
	}
}

impl NonTrivialSlicable for Chain { }

/// The duty roster specifying what jobs each validator must do.
#[derive(Clone, PartialEq)]
#[cfg_attr(feature = "std", derive(Default, Debug))]
pub struct DutyRoster {
	/// Lookup from validator index to chain on which that validator has a duty to validate.
	pub validator_duty: Vec<Chain>,
	/// Lookup from validator index to chain on which that validator has a duty to guarantee
	/// availability.
	pub guarantor_duty: Vec<Chain>,
}

impl Slicable for DutyRoster {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(DutyRoster {
			validator_duty: try_opt!(Slicable::decode(input)),
			guarantor_duty: try_opt!(Slicable::decode(input)),
		})
	}

	fn to_vec(&self) -> Vec<u8> {
		let mut v = Vec::new();

		v.extend(self.validator_duty.to_vec());
		v.extend(self.guarantor_duty.to_vec());

		v
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(&self.to_vec().as_slice())
	}
}

/// Candidate parachain block.
///
/// https://github.com/w3f/polkadot-spec/blob/master/spec.md#candidate-para-chain-block
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
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
	/// The collator's relay-chain account ID
	pub collator: ::AccountId,
	/// The head-data
	pub head_data: HeadData,
	/// Balance uploads to the relay chain.
	pub balance_uploads: Vec<(::AccountId, u64)>,
	/// Egress queue roots.
	pub egress_queue_roots: Vec<(Id, primitives::H256)>,
	/// Fees paid from the chain to the relay chain validators
	pub fees: u64,
}

/// Parachain ingress queue message.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct Message(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// Consolidated ingress queue data.
///
/// This is just an ordered vector of other parachains' egress queues,
/// obtained according to the routing rules.
#[derive(Default, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct ConsolidatedIngress(pub Vec<(Id, Vec<Message>)>);

/// Parachain block data.
///
/// contains everything required to validate para-block, may contain block and witness data
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct BlockData(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// Parachain header raw bytes wrapper type.
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct Header(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// Parachain head data included in the chain.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct HeadData(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// Parachain validation code.
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct ValidationCode(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// Activitiy bit field
#[derive(PartialEq, Eq, Clone, Default)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct Activity(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

impl Slicable for Activity {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Vec::<u8>::decode(input).map(Activity)
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.0.as_slice_then(f)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use substrate_serializer as ser;

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
