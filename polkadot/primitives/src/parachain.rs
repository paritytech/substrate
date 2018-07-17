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

//! Polkadot parachain types.

use codec::{Encode, Decode, Input, Output};
use rstd::prelude::*;
use rstd::cmp::Ordering;
use super::Hash;

#[cfg(feature = "std")]
use primitives::bytes;

/// Signature on candidate's block data by a collator.
pub type CandidateSignature = ::runtime_primitives::Ed25519Signature;

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

impl Id {
	/// Convert this Id into its inner representation.
	pub fn into_inner(self) -> u32 {
		self.0
	}
}

impl Decode for Id {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		u32::decode(input).map(Id)
	}
}

impl Encode for Id {
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

impl Decode for Chain {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		let disc = input.read_byte()?;
		match disc {
			0 => Some(Chain::Relay),
			1 => Some(Chain::Parachain(Decode::decode(input)?)),
			_ => None,
		}
	}
}

impl Encode for Chain {
	fn encode_to<T: Output>(&self, dest: &mut T) {
		match *self {
			Chain::Relay => { dest.push_byte(0); }
			Chain::Parachain(id) => {
				dest.push_byte(1u8);
				dest.push(&id);
			}
		}
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

impl Decode for DutyRoster {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(DutyRoster {
			validator_duty: Decode::decode(input)?,
			guarantor_duty: Decode::decode(input)?,
		})
	}
}

impl Encode for DutyRoster {
	fn encode_to<T: Output>(&self, dest: &mut T) {
		dest.push(&self.validator_duty);
		dest.push(&self.guarantor_duty);
	}
}

/// Extrinsic data for a parachain.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub struct Extrinsic;

/// Candidate receipt type.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub struct CandidateReceipt {
	/// The ID of the parachain this is a candidate for.
	pub parachain_index: Id,
	/// The collator's relay-chain account ID
	pub collator: super::AccountId,
	/// Signature on blake2-256 of the block data by collator.
	pub signature: CandidateSignature,
	/// The head-data
	pub head_data: HeadData,
	/// Balance uploads to the relay chain.
	pub balance_uploads: Vec<(super::AccountId, u64)>,
	/// Egress queue roots.
	pub egress_queue_roots: Vec<(Id, Hash)>,
	/// Fees paid from the chain to the relay chain validators
	pub fees: u64,
	/// blake2-256 Hash of block data.
	pub block_data_hash: Hash,
}

impl Encode for CandidateReceipt {
	fn encode_to<T: Output>(&self, dest: &mut T) {
		dest.push(&self.parachain_index);
		dest.push(&self.collator);
		dest.push(&self.signature);
		dest.push(&self.head_data.0);
		dest.push(&self.balance_uploads);
		dest.push(&self.egress_queue_roots);
		dest.push(&self.fees);
		dest.push(&self.block_data_hash);
	}
}

impl Decode for CandidateReceipt {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(CandidateReceipt {
			parachain_index: Decode::decode(input)?,
			collator: Decode::decode(input)?,
			signature: Decode::decode(input)?,
			head_data: Decode::decode(input).map(HeadData)?,
			balance_uploads: Decode::decode(input)?,
			egress_queue_roots: Decode::decode(input)?,
			fees: Decode::decode(input)?,
			block_data_hash: Decode::decode(input)?,
		})
	}
}

impl CandidateReceipt {
	/// Get the blake2_256 hash
	#[cfg(feature = "std")]
	pub fn hash(&self) -> Hash {
		use runtime_primitives::traits::{BlakeTwo256, Hash};
		BlakeTwo256::hash_of(self)
	}

	/// Check integrity vs. provided block data.
	pub fn check_signature(&self) -> Result<(), ()> {
		use runtime_primitives::traits::Verify;

		if self.signature.verify(&self.block_data_hash.0[..], &self.collator) {
			Ok(())
		} else {
			Err(())
		}
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

/// A full collation.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub struct Collation {
	/// Block data.
	pub block_data: BlockData,
	/// Candidate receipt itself.
	pub receipt: CandidateReceipt,
}

impl Decode for Collation {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(Collation {
			block_data: Decode::decode(input)?,
			receipt: Decode::decode(input)?,
		})
	}
}

impl Encode for Collation {
	fn encode_to<T: Output>(&self, dest: &mut T) {
		dest.push(&self.block_data);
		dest.push(&self.receipt);
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

impl BlockData {
	/// Compute hash of block data.
	#[cfg(feature = "std")]
	pub fn hash(&self) -> Hash {
		use runtime_primitives::traits::{BlakeTwo256, Hash};
		BlakeTwo256::hash(&self.0[..])
	}
}

impl Decode for BlockData {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(BlockData(Decode::decode(input)?))
	}
}

impl Encode for BlockData {
	fn encode_to<T: Output>(&self, dest: &mut T) {
		dest.push(&self.0);
	}
}

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

impl Decode for Activity {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Vec::<u8>::decode(input).map(Activity)
	}
}

impl Encode for Activity {
	fn encode_to<T: Output>(&self, dest: &mut T) {
		self.0.encode_to(dest)
	}
}

/// Statements which can be made about parachain candidates.
#[derive(Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
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
