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

use block::{Block, HeaderHash};
use codec::{Slicable, Input};
use rstd::vec::Vec;

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
#[repr(u8)]
enum ActionKind {
	Propose = 1,
	Prepare = 2,
	Commit = 3,
	AdvanceRound = 4,
}

/// Actions which can be taken during the BFT process.
#[derive(Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum Action {
	/// Proposal of a block candidate.
	Propose(u32, Block),
	/// Preparation to commit for a candidate.
	Prepare(u32, HeaderHash),
	/// Vote to commit to a candidate.
	Commit(u32, HeaderHash),
	/// Vote to advance round after inactive primary.
	AdvanceRound(u32),
}

impl Slicable for Action {
	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();
		match *self {
			Action::Propose(ref round, ref block) => {
				v.push(ActionKind::Propose as u8);
				round.using_encoded(|s| v.extend(s));
				block.using_encoded(|s| v.extend(s));
			}
			Action::Prepare(ref round, ref hash) => {
				v.push(ActionKind::Prepare as u8);
				round.using_encoded(|s| v.extend(s));
				hash.using_encoded(|s| v.extend(s));
			}
			Action::Commit(ref round, ref hash) => {
				v.push(ActionKind::Commit as u8);
				round.using_encoded(|s| v.extend(s));
				hash.using_encoded(|s| v.extend(s));
			}
			Action::AdvanceRound(ref round) => {
				v.push(ActionKind::AdvanceRound as u8);
				round.using_encoded(|s| v.extend(s));
			}
		}

		v
	}

	fn decode<I: Input>(value: &mut I) -> Option<Self> {
		match u8::decode(value) {
			Some(x) if x == ActionKind::Propose as u8 => {
				let (round, block) = try_opt!(Slicable::decode(value));
				Some(Action::Propose(round, block))
			}
			Some(x) if x == ActionKind::Prepare as u8 => {
				let (round, hash) = try_opt!(Slicable::decode(value));

				Some(Action::Prepare(round, hash))
			}
			Some(x) if x == ActionKind::Commit as u8 => {
				let (round, hash) = try_opt!(Slicable::decode(value));

				Some(Action::Commit(round, hash))
			}
			Some(x) if x == ActionKind::AdvanceRound as u8 => {
				Slicable::decode(value).map(Action::AdvanceRound)
			}
			_ => None,
		}
	}
}

/// Messages exchanged between participants in the BFT consensus.
#[derive(Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Message {
	/// The parent header hash this action is relative to.
	pub parent: HeaderHash,
	/// The action being broadcasted.
	pub action: Action,
}

impl Slicable for Message {
	fn encode(&self) -> Vec<u8> {
		let mut v = self.parent.encode();
		self.action.using_encoded(|s| v.extend(s));
		v
	}

	fn decode<I: Input>(value: &mut I) -> Option<Self> {
		Some(Message {
			parent: try_opt!(Slicable::decode(value)),
			action: try_opt!(Slicable::decode(value)),
		})
	}
}
