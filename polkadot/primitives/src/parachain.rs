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
use codec::{Input, Slicable};
use rstd::cmp::{PartialOrd, Ord, Ordering};
use rstd::vec::Vec;
use ::Hash;

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

	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.0.using_encoded(f)
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
		let disc = input.read_byte()?;

		match disc {
			0 => Some(Chain::Relay),
			1 => Some(Chain::Parachain(try_opt!(Slicable::decode(input)))),
			_ => None,
		}
	}

	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();
		match *self {
			Chain::Relay => { v.push(0); }
			Chain::Parachain(id) => {
				v.push(1u8);
				id.using_encoded(|s| v.extend(s));
			}
		}

		v
	}

	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(&self.encode().as_slice())
	}
}



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

	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		v.extend(self.validator_duty.encode());
		v.extend(self.guarantor_duty.encode());

		v
	}

	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(&self.encode().as_slice())
	}
}

/// Extrinsic data for a parachain.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub struct Extrinsic;

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

impl Slicable for CandidateReceipt {
	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		self.parachain_index.using_encoded(|s| v.extend(s));
		self.collator.using_encoded(|s| v.extend(s));
		self.head_data.0.using_encoded(|s| v.extend(s));
		self.balance_uploads.using_encoded(|s| v.extend(s));
		self.egress_queue_roots.using_encoded(|s| v.extend(s));
		self.fees.using_encoded(|s| v.extend(s));

		v
	}

	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(CandidateReceipt {
			parachain_index: try_opt!(Slicable::decode(input)),
			collator: try_opt!(Slicable::decode(input)),
			head_data: try_opt!(Slicable::decode(input).map(HeadData)),
			balance_uploads: try_opt!(Slicable::decode(input)),
			egress_queue_roots: try_opt!(Slicable::decode(input)),
			fees: try_opt!(Slicable::decode(input)),
		})
	}
}

impl CandidateReceipt {
	/// Get the blake2_256 hash
	#[cfg(feature = "std")]
	pub fn hash(&self) -> Hash {
		let encoded = self.encode();
		primitives::hashing::blake2_256(&encoded).into()
	}
}

impl PartialOrd for CandidateReceipt {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl Ord for CandidateReceipt {
	fn cmp(&self, other: &Self) -> Ordering {
		// TODO: compare signatures or something more sane
		self.parachain_index.cmp(&other.parachain_index)
			.then_with(|| self.head_data.cmp(&other.head_data))
	}
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
#[derive(PartialEq, Eq, Clone, PartialOrd, Ord)]
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

	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.0.using_encoded(f)
	}
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
#[repr(u8)]
enum StatementKind {
	Candidate = 1,
	Valid = 2,
	Invalid = 3,
	Available = 4,
}

/// Statements which can be made about parachain candidates.
#[derive(Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum Statement {
	/// Proposal of a parachain candidate.
	Candidate(CandidateReceipt),
	/// State that a parachain candidate is valid.
	Valid(Hash),
	/// Vote to commit to a candidate.
	Invalid(Hash),
	/// Vote to advance round after inactive primary.
	Available(Hash),
}

impl Slicable for Statement {
	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();
		match *self {
			Statement::Candidate(ref candidate) => {
				v.push(StatementKind::Candidate as u8);
				candidate.using_encoded(|s| v.extend(s));
			}
			Statement::Valid(ref hash) => {
				v.push(StatementKind::Valid as u8);
				hash.using_encoded(|s| v.extend(s));
			}
			Statement::Invalid(ref hash) => {
				v.push(StatementKind::Invalid as u8);
				hash.using_encoded(|s| v.extend(s));
			}
			Statement::Available(ref hash) => {
				v.push(StatementKind::Available as u8);
				hash.using_encoded(|s| v.extend(s));
			}
		}

		v
	}

	fn decode<I: Input>(value: &mut I) -> Option<Self> {
		match value.read_byte() {
			Some(x) if x == StatementKind::Candidate as u8 => {
				Slicable::decode(value).map(Statement::Candidate)
			}
			Some(x) if x == StatementKind::Valid as u8 => {
				Slicable::decode(value).map(Statement::Valid)
			}
			Some(x) if x == StatementKind::Invalid as u8 => {
				Slicable::decode(value).map(Statement::Invalid)
			}
			Some(x) if x == StatementKind::Available as u8 => {
				Slicable::decode(value).map(Statement::Available)
			}
			_ => None,
		}
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
