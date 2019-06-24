// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Common utilities for accountable safety in Substrate.

#![cfg_attr(not(feature = "std"), no_std)]

pub trait AuthorshipEquivocationProof<H, S> {
	/// Create an equivocation proof for AuRa or Babe.
	fn new(
		first_header: H,
		second_header: H,
		first_signature: S, 
		second_signature: S,
	) -> Self;

	/// Get the first header involved in the equivocation.
	fn first_header(&self) -> &H;

	/// Get the second header involved in the equivocation.
	fn second_header(&self) -> &H;

	/// Get signature for the first header involved in the equivocation.
	fn first_signature(&self) -> &S;

	/// Get signature for the second header involved in the equivocation.
	fn second_signature(&self) -> &S;
}

/// A challenge is a transaction T containing
/// a) the set of votes S being challenged, that were cast in round r_S,
/// b) a reference to a finalized block B, with respect to which the set of votes S is incompatible,
/// c) a set C_B of pre-commit votes in round r_B (where r_B <= r_S) having supermajority for B,
///    and thus proving that B was indeed finalized in round r_B, and
/// d) a reference to a previous challenge, if the current tx is an answer to it.
pub struct GrandpaChallenge<Vote, Block, Precommit, Hash> {
	challenged_votes: Vec<Vote>,
	finalized_block: Block,
	block_proof: Vec<Precommit>,
	previous_challenge: Option<Hash>,
}
