// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Message formats for the BFT consensus layer.

use rstd::prelude::*;
use codec::{Decode, Encode, Input, Output};
use substrate_primitives::{AuthorityId, Signature};

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
#[repr(i8)]
enum ActionKind {
	Propose = 1,
	ProposeHeader = 2,
	Prepare = 3,
	Commit = 4,
	AdvanceRound = 5,
}

/// Type alias for extracting message type from block.
pub type ActionFor<B> = Action<B, <B as ::traits::Block>::Hash>;

/// Actions which can be taken during the BFT process.
#[derive(Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub enum Action<Block, H> {
	/// Proposal of a block candidate.
	Propose(u32, Block),
	/// Proposal header of a block candidate. Accompanies any proposal,
	/// but is used for misbehavior reporting since blocks themselves are big.
	ProposeHeader(u32, H),
	/// Preparation to commit for a candidate.
	Prepare(u32, H),
	/// Vote to commit to a candidate.
	Commit(u32, H),
	/// Vote to advance round after inactive primary.
	AdvanceRound(u32),
}

impl<Block: Encode, Hash: Encode> Encode for Action<Block, Hash> {
	fn encode_to<T: Output>(&self, dest: &mut T) {
		match *self {
			Action::Propose(ref round, ref block) => {
				dest.push_byte(ActionKind::Propose as u8);
				dest.push(round);
				dest.push(block);
			}
			Action::ProposeHeader(ref round, ref hash) => {
				dest.push_byte(ActionKind::ProposeHeader as u8);
				dest.push(round);
				dest.push(hash);
			}
			Action::Prepare(ref round, ref hash) => {
				dest.push_byte(ActionKind::Prepare as u8);
				dest.push(round);
				dest.push(hash);
			}
			Action::Commit(ref round, ref hash) => {
				dest.push_byte(ActionKind::Commit as u8);
				dest.push(round);
				dest.push(hash);
			}
			Action::AdvanceRound(ref round) => {
				dest.push_byte(ActionKind::AdvanceRound as u8);
				dest.push(round);
			}
		}
	}
}

impl<Block: Decode, Hash: Decode> Decode for Action<Block, Hash> {
	fn decode<I: Input>(value: &mut I) -> Option<Self> {
		match i8::decode(value) {
			Some(x) if x == ActionKind::Propose as i8 => {
				let (round, block) = Decode::decode(value)?;
				Some(Action::Propose(round, block))
			}
			Some(x) if x == ActionKind::ProposeHeader as i8 => {
				let (round, hash) = Decode::decode(value)?;
				Some(Action::ProposeHeader(round, hash))
			}
			Some(x) if x == ActionKind::Prepare as i8 => {
				let (round, hash) = Decode::decode(value)?;
				Some(Action::Prepare(round, hash))
			}
			Some(x) if x == ActionKind::Commit as i8 => {
				let (round, hash) = Decode::decode(value)?;
				Some(Action::Commit(round, hash))
			}
			Some(x) if x == ActionKind::AdvanceRound as i8 => {
				Decode::decode(value).map(Action::AdvanceRound)
			}
			_ => None,
		}
	}
}

/// Type alias for extracting message type from block.
pub type MessageFor<B> = Message<B, <B as ::traits::Block>::Hash>;

/// Messages exchanged between participants in the BFT consensus.
#[derive(Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct Message<Block, Hash> {
	/// The parent header hash this action is relative to.
	pub parent: Hash,
	/// The action being broadcasted.
	pub action: Action<Block, Hash>,
}

impl<Block: Encode, Hash: Encode> Encode for Message<Block, Hash> {
	fn encode_to<T: Output>(&self, dest: &mut T) {
		dest.push(&self.parent);
		dest.push(&self.action);
	}
}

impl<Block: Decode, Hash: Decode> Decode for Message<Block, Hash> {
	fn decode<I: Input>(value: &mut I) -> Option<Self> {
		Some(Message {
			parent: Decode::decode(value)?,
			action: Decode::decode(value)?,
		})
	}
}

/// Justification of a block.
#[derive(Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct Justification<H> {
	/// The round consensus was reached in.
	pub round_number: u32,
	/// The hash of the header justified.
	pub hash: H,
	/// The signatures and signers of the hash.
	pub signatures: Vec<(AuthorityId, Signature)>
}

impl<H: Encode> Encode for Justification<H> {
	fn encode_to<T: Output>(&self, dest: &mut T) {
		dest.push(&self.round_number);
		dest.push(&self.hash);
		dest.push(&self.signatures);
	}
}

impl<H: Decode> Decode for Justification<H> {
	fn decode<I: Input>(value: &mut I) -> Option<Self> {
		Some(Justification {
			round_number: Decode::decode(value)?,
			hash: Decode::decode(value)?,
			signatures: Decode::decode(value)?,
		})
	}
}

// single-byte code to represent misbehavior kind.
#[repr(i8)]
enum MisbehaviorCode {
	/// BFT: double prepare.
	BftDoublePrepare = 0x11,
	/// BFT: double commit.
	BftDoubleCommit = 0x12,
}

impl MisbehaviorCode {
	fn from_i8(x: i8) -> Option<Self> {
		match x {
			0x11 => Some(MisbehaviorCode::BftDoublePrepare),
			0x12 => Some(MisbehaviorCode::BftDoubleCommit),
			_ => None,
		}
	}
}

/// Misbehavior kinds.
#[derive(Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub enum MisbehaviorKind<Hash> {
	/// BFT: double prepare.
	BftDoublePrepare(u32, (Hash, Signature), (Hash, Signature)),
	/// BFT: double commit.
	BftDoubleCommit(u32, (Hash, Signature), (Hash, Signature)),
}

/// A report of misbehavior by an authority.
#[derive(Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct MisbehaviorReport<Hash, Number> {
	/// The parent hash of the block where the misbehavior occurred.
	pub parent_hash: Hash,
	/// The parent number of the block where the misbehavior occurred.
	pub parent_number: Number,
	/// The authority who misbehavior.
	pub target: AuthorityId,
	/// The misbehavior kind.
	pub misbehavior: MisbehaviorKind<Hash>,
}

impl<Hash: Encode, Number: Encode> Encode for MisbehaviorReport<Hash, Number> {
	fn encode_to<T: Output>(&self, dest: &mut T) {
		dest.push(&self.parent_hash);
		dest.push(&self.parent_number);
		dest.push(&self.target);

		match self.misbehavior {
			MisbehaviorKind::BftDoublePrepare(ref round, (ref h_a, ref s_a), (ref h_b, ref s_b)) => {
				dest.push(&(MisbehaviorCode::BftDoublePrepare as i8));
				dest.push(round);
				dest.push(h_a);
				dest.push(s_a);
				dest.push(h_b);
				dest.push(s_b);
			}
			MisbehaviorKind::BftDoubleCommit(ref round, (ref h_a, ref s_a), (ref h_b, ref s_b)) => {
				dest.push(&(MisbehaviorCode::BftDoubleCommit as i8));
				dest.push(round);
				dest.push(h_a);
				dest.push(s_a);
				dest.push(h_b);
				dest.push(s_b);
			}
		}
	}
}

impl<Hash: Decode, Number: Decode> Decode for MisbehaviorReport<Hash, Number> {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		let parent_hash = Hash::decode(input)?;
		let parent_number = Number::decode(input)?;
		let target = AuthorityId::decode(input)?;

		let misbehavior = match i8::decode(input).and_then(MisbehaviorCode::from_i8)? {
			MisbehaviorCode::BftDoublePrepare => {
				MisbehaviorKind::BftDoublePrepare(
					u32::decode(input)?,
					(Hash::decode(input)?, Signature::decode(input)?),
					(Hash::decode(input)?, Signature::decode(input)?),
				)
			}
			MisbehaviorCode::BftDoubleCommit => {
				MisbehaviorKind::BftDoubleCommit(
					u32::decode(input)?,
					(Hash::decode(input)?, Signature::decode(input)?),
					(Hash::decode(input)?, Signature::decode(input)?),
				)
			}
		};

		Some(MisbehaviorReport {
			parent_hash,
			parent_number,
			target,
			misbehavior,
		})
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use substrate_primitives::H256;

	#[test]
	fn misbehavior_report_roundtrip() {
		let report = MisbehaviorReport::<H256, u64> {
			parent_hash: [0; 32].into(),
			parent_number: 999,
			target: [1; 32].into(),
			misbehavior: MisbehaviorKind::BftDoubleCommit(
				511,
				([2; 32].into(), [3; 64].into()),
				([4; 32].into(), [5; 64].into()),
			),
		};

		let encoded = report.encode();
		assert_eq!(MisbehaviorReport::<H256, u64>::decode(&mut &encoded[..]).unwrap(), report);

		let report = MisbehaviorReport::<H256, u64> {
			parent_hash: [0; 32].into(),
			parent_number: 999,
			target: [1; 32].into(),
			misbehavior: MisbehaviorKind::BftDoublePrepare(
				511,
				([2; 32].into(), [3; 64].into()),
				([4; 32].into(), [5; 64].into()),
			),
		};

		let encoded = report.encode();
		assert_eq!(MisbehaviorReport::<H256, u64>::decode(&mut &encoded[..]).unwrap(), report);
	}
}
