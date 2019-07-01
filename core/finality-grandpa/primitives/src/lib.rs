// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Primitives for GRANDPA integration, suitable for WASM compilation.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
extern crate alloc;
extern crate num_traits;

#[cfg(feature = "std")]
use serde::Serialize;

use parity_codec::{Encode, Decode};
use sr_primitives::{
	ConsensusEngineId, traits::{DigestFor, NumberFor, Block as BlockT, Hash, Header},
	generic::Block,
};
use client::decl_runtime_apis;
use rstd::vec::Vec;
#[cfg(not(feature = "std"))]
use alloc::collections::BTreeMap;
#[cfg(feature = "std")]
use std::collections::BTreeMap;
use num_traits as num;

pub use grandpa_primitives::{
	Precommit, Prevote, Equivocation, Message, Error as GrandpaError, Chain,
	validate_commit, Commit, VoterSet
};

/// The grandpa crypto scheme defined via the keypair type.
#[cfg(feature = "std")]
pub type AuthorityPair = substrate_primitives::ed25519::Pair;

/// Identity of a Grandpa authority.
pub type AuthorityId = substrate_primitives::ed25519::Public;

/// Signature for a Grandpa authority.
pub type AuthoritySignature = substrate_primitives::ed25519::Signature;

/// The `ConsensusEngineId` of GRANDPA.
pub const GRANDPA_ENGINE_ID: ConsensusEngineId = *b"FRNK";

/// The weight of an authority.
pub type AuthorityWeight = u64;

/// Prevote equivocation.
pub type PrevoteEquivocation<Hash, Number> =
	Equivocation<AuthorityId, Prevote<Hash, Number>, AuthoritySignature>;

/// Precommit equivocation.
pub type PrecommitEquivocation<Hash, Number> =
	Equivocation<AuthorityId, Precommit<Hash, Number>, AuthoritySignature>;


/// A scheduled change of authority set.
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
#[derive(Clone, Eq, PartialEq, Encode, Decode)]
pub struct ScheduledChange<N> {
	/// The new authorities after the change, along with their respective weights.
	pub next_authorities: Vec<(AuthorityId, u64)>,
	/// The number of blocks to delay.
	pub delay: N,
}

/// WASM function call to check for pending changes.
pub const PENDING_CHANGE_CALL: &str = "grandpa_pending_change";
/// WASM function call to get current GRANDPA authorities.
pub const AUTHORITIES_CALL: &str = "grandpa_authorities";

/// Length of a challenge session in blocks.
pub const CHALLENGE_SESSION_LENGTH: u32 = 8;

/// A scheduled change of authority set.
#[cfg_attr(feature = "std", derive(Serialize))]
#[derive(Clone, Eq, PartialEq, Encode, Decode)]
pub struct Challenge<H, N, Header, Signature, Id> {
	pub phantom_data: core::marker::PhantomData<(H, N, Header, Signature, Id)>,
}

decl_runtime_apis! {
	/// APIs for integrating the GRANDPA finality gadget into runtimes.
	/// This should be implemented on the runtime side.
	///
	/// This is primarily used for negotiating authority-set changes for the
	/// gadget. GRANDPA uses a signaling model of changing authority sets:
	/// changes should be signaled with a delay of N blocks, and then automatically
	/// applied in the runtime after those N blocks have passed.
	///
	/// The consensus protocol will coordinate the handoff externally.
	#[api_version(3)]
	pub trait GrandpaApi {
		/// Check a digest for pending changes.
		/// Return `None` if there are no pending changes.
		///
		/// Precedence towards earlier or later digest items can be given
		/// based on the rules of the chain.
		///
		/// No change should be scheduled if one is already and the delay has not
		/// passed completely.
		///
		/// This should be a pure function: i.e. as long as the runtime can interpret
		/// the digest type it should return the same result regardless of the current
		/// state.
		fn grandpa_pending_change(digest: &DigestFor<Block>)
			-> Option<ScheduledChange<NumberFor<Block>>>;

		/// Check a digest for forced changes.
		/// Return `None` if there are no forced changes. Otherwise, return a
		/// tuple containing the pending change and the median last finalized
		/// block number at the time the change was signaled.
		///
		/// Added in version 2.
		///
		/// Forced changes are applied after a delay of _imported_ blocks,
		/// while pending changes are applied after a delay of _finalized_ blocks.
		///
		/// Precedence towards earlier or later digest items can be given
		/// based on the rules of the chain.
		///
		/// No change should be scheduled if one is already and the delay has not
		/// passed completely.
		///
		/// This should be a pure function: i.e. as long as the runtime can interpret
		/// the digest type it should return the same result regardless of the current
		/// state.
		fn grandpa_forced_change(digest: &DigestFor<Block>)
			-> Option<(NumberFor<Block>, ScheduledChange<NumberFor<Block>>)>;

		/// Get the current GRANDPA authorities and weights. This should not change except
		/// for when changes are scheduled and the corresponding delay has passed.
		///
		/// When called at block B, it will return the set of authorities that should be
		/// used to finalize descendants of this block (B+1, B+2, ...). The block B itself
		/// is finalized by the authorities from block B-1.
		fn grandpa_authorities() -> Vec<(AuthorityId, AuthorityWeight)>;
		
		/// Construct a call to report the prevote equivocation.
		fn construct_prevote_equivocation_report_call(
			proof: GrandpaEquivocationProof<PrevoteEquivocation<<Block as BlockT>::Hash, NumberFor<Block>>>
		) -> Vec<u8>;
		
		/// Construct a call to report the precommit equivocation.
		fn construct_precommit_equivocation_report_call(
			proof: GrandpaEquivocationProof<PrecommitEquivocation<<Block as BlockT>::Hash, NumberFor<Block>>>
		) -> Vec<u8>;

		fn grandpa_challenge(digest: &DigestFor<Block>)
			-> Option<Challenge<<Block as BlockT>::Hash, NumberFor<Block>, <Block as BlockT>::Header, AuthoritySignature, AuthorityId>>;
	}
}

#[derive(Debug, Clone, Encode, Decode, PartialEq)]
pub struct GrandpaEquivocationProof<E> {
	pub set_id: u64,
	pub equivocation: E,
}

pub fn localized_payload<E: Encode>(round: u64, set_id: u64, message: &E) -> Vec<u8> {
	(message, round, set_id).encode()
}

/// A challenge is a transaction T containing
/// a) the set of votes S being challenged, that were cast in round r_S,
/// b) a reference to a finalized block B, with respect to which the set of votes S is incompatible,
/// c) a set C_B of pre-commit votes in round r_B (where r_B <= r_S) having supermajority for B,
///    and thus proving that B was indeed finalized in round r_B, and
/// d) a reference to a previous challenge, if the current tx is an answer to it.


#[cfg_attr(feature = "std", derive(Serialize, Debug))]
#[derive(Encode, Decode, Clone, PartialEq, Eq)]
pub struct PrevoteChallenge<H, N, Header, S, Id, Vote> {
	pub finalized_block: (H, N),
	pub finalized_block_proof: FinalizedBlockProof<H, N, Header, S, Id>,
	pub challenged_votes: ChallengedVoteSet<Vote>,
	pub previous_challenge: Option<H>,
}

#[cfg_attr(feature = "std", derive(Debug, Serialize))]
#[derive(Encode, Decode, Clone, PartialEq, Eq)]
pub struct FinalizedBlockProof<H, N, Header, S, Id> {
	pub commit: Commit<H, N, S, Id>,
	pub headers: Vec<Header>,
}


#[cfg_attr(feature = "std", derive(Serialize, Debug))]
#[derive(Encode, Decode, Clone, PartialEq, Eq)]
pub struct PrecommitChallenge<H, N, Header, S, Id, Vote> {
	pub finalized_block: (H, N),
	pub finalized_block_proof: FinalizedBlockProof<H, N, Header, S, Id>,
	pub challenged_votes: ChallengedVoteSet<Vote>,
	pub previous_challenge: Option<H>,
}


#[cfg_attr(feature = "std", derive(Debug, Serialize))]
#[derive(Encode, Decode, Clone, PartialEq, Eq)]
pub struct ChallengedVoteSet<Vote> {
	pub challenged_votes: Vec<ChallengedVote<Vote>>,
	pub set_id: u64,
	pub round: u64,
}


#[cfg_attr(feature = "std", derive(Debug, Serialize))]
#[derive(Encode, Decode, Clone, PartialEq, Eq)]
pub struct ChallengedVote<Vote> {
	// Prevote or Precommit
	pub vote: Vote,
	pub authority: AuthorityId,
	pub signature: AuthoritySignature,
}

/// A utility trait implementing `grandpa::Chain` using a given set of headers.
/// This is useful when validating commits, using the given set of headers to
/// verify a valid ancestry route to the target commit block.
pub struct AncestryChain<Block: BlockT> {
	ancestry: BTreeMap<Block::Hash, Block::Header>,
}

impl<Block: BlockT> AncestryChain<Block> 
where
	<Block as BlockT>::Hash: Ord
{
	pub fn new(ancestry: &[Block::Header]) -> AncestryChain<Block> {
		let ancestry: BTreeMap<_, _> = ancestry
			.iter()
			.cloned()
			.map(|h: Block::Header| (h.hash(), h))
			.collect();

		AncestryChain { ancestry }
	}
}

impl<Block: BlockT> Chain<Block::Hash, NumberFor<Block>> for AncestryChain<Block>
where
	<Block as BlockT>::Hash: Ord,
	<<Block as BlockT>::Header as Header>::Number: num::cast::AsPrimitive<usize>,
{
	fn ancestry(&self, base: Block::Hash, block: Block::Hash) -> Result<Vec<Block::Hash>, GrandpaError> {
		let mut route = Vec::new();
		let mut current_hash = block;
		loop {
			if current_hash == base { break; }
			match self.ancestry.get(&current_hash) {
				Some(current_header) => {
					current_hash = *current_header.parent_hash();
					route.push(current_hash);
				},
				_ => return Err(GrandpaError::NotDescendent),
			}
		}
		route.pop(); // remove the base

		Ok(route)
	}

	fn best_chain_containing(&self, _block: Block::Hash) -> Option<(Block::Hash, NumberFor<Block>)> {
		None
	}
}
