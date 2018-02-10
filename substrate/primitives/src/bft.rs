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
	Propose(usize, Block),
	/// Preparation to commit for a candidate.
	Prepare(usize, HeaderHash),
	/// Vote to commit to a candidate.
	Commit(usize, HeaderHash),
	/// Vote to advance round after inactive primary.
	AdvanceRound(usize),
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
