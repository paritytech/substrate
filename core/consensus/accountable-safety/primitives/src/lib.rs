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

use rstd::vec::Vec;
use parity_codec::{Encode, Decode, Codec};
#[cfg(feature = "std")]
use serde::Serialize;
use runtime_primitives::{traits::{Header, Verify}, };
use grandpa_primitives::{Message, };
use substrate_primitives::ed25519::{
	Public as AuthorityId, Signature as AuthoritySignature
};

pub trait AuthorshipEquivocationProof {
	type Header: Header;
	type Signature: Verify;
	type Identity: Codec;
	type InclusionProof: Codec;

	/// Create an equivocation proof for AuRa or Babe.
	fn new(
		identity: Self::Identity,
		identity_proof: Self::InclusionProof,
		first_header: Self::Header,
		second_header: Self::Header,
		first_signature: Self::Signature, 
		second_signature: Self::Signature,
	) -> Self;

	/// Check the validity of the equivocation.
	/// Includes checking signatures, identity inclusion, same slot and distinct headers.
	fn is_valid(&self) -> bool;

	/// Get the identity of the suspect of equivocating.
	fn identity(&self) -> &Self::Identity;

	/// Get the proof of inclusion of the identity in the validator set.
	fn identity_proof(&self) -> &Self::InclusionProof;

	/// Get the first header involved in the equivocation.
	fn first_header(&self) -> &Self::Header;

	/// Get the second header involved in the equivocation.
	fn second_header(&self) -> &Self::Header;

	/// Get signature for the first header involved in the equivocation.
	fn first_signature(&self) -> &Self::Signature;

	/// Get signature for the second header involved in the equivocation.
	fn second_signature(&self) -> &Self::Signature;
}

/// A challenge is a transaction T containing
/// a) the set of votes S being challenged, that were cast in round r_S,
/// b) a reference to a finalized block B, with respect to which the set of votes S is incompatible,
/// c) a set C_B of pre-commit votes in round r_B (where r_B <= r_S) having supermajority for B,
///    and thus proving that B was indeed finalized in round r_B, and
/// d) a reference to a previous challenge, if the current tx is an answer to it.

#[cfg_attr(feature = "std", derive(Debug, Serialize))]
#[derive(Clone, PartialEq, Eq, Encode, Decode)]
pub struct Challenge<H, N, Header, P> {
	pub targets: Vec<AuthorityId>, // TODO: Optimize to bitset?
	pub targets_proof: Option<Vec<P>>,
	pub finalized_block: (H, N),
	pub finalized_block_proof: VoteSet<H, N, Header>,
	pub rejecting_set: VoteSet<H, N, Header>,
	pub previous_challenge: Option<H>,
}

#[cfg_attr(feature = "std", derive(Debug, Serialize))]
#[derive(Clone, PartialEq, Eq, Encode, Decode)]
pub struct VoteSet<H, N, Header> {
	pub votes: Vec<ChallengedVote<H, N>>,
	pub headers: Vec<Header>,
	pub round: u64,
}

#[cfg_attr(feature = "std", derive(Debug, Serialize))]
#[derive(Clone, PartialEq, Eq, Encode, Decode)]
pub struct ChallengedVote<H, N> {
	pub vote: Message<H, N>,
	pub authority: AuthorityId,
	pub signature: AuthoritySignature,
}

/// A stored pending change.
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
#[derive(Encode, Decode, Clone, PartialEq, Eq)]
pub struct StoredPendingChallenge<H, N, Header, P> {
	/// The challenge submitted.
	pub challenge: Challenge<H, N, Header, P>,
}

/// A stored pending change.
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
#[derive(Encode, Decode, Clone, PartialEq, Eq)]
pub struct StoredChallengeSession<H, N> {
	/// The round of the rejecting set votes.
	pub rejecting_set_round: u64,
	/// Reference block.
	pub reference_block: (H, N),
	/// The block number this was scheduled at.
	pub scheduled_at: N,
	/// The hash of the parent of block that created this challenge.
	pub parent_hash: H,
	/// The delay in blocks until it will expire.
	pub delay: N,
	/// The hash of the challenge.
	pub challenge_hash: H,
}
