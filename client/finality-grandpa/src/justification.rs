// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use std::{
	collections::{HashMap, HashSet},
	sync::Arc,
};

use finality_grandpa::{voter_set::VoterSet, Error as GrandpaError};
use parity_scale_codec::{Decode, Encode};
use sp_blockchain::{Error as ClientError, HeaderBackend};
use sp_finality_grandpa::AuthorityId;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header as HeaderT, NumberFor},
};

use crate::{AuthorityList, Commit, Error};

/// A GRANDPA justification for block finality, it includes a commit message and
/// an ancestry proof including all headers routing all precommit target blocks
/// to the commit target block. Due to the current voting strategy the precommit
/// targets should be the same as the commit target, since honest voters don't
/// vote past authority set change blocks.
///
/// This is meant to be stored in the db and passed around the network to other
/// nodes, and are used by syncing nodes to prove authority set handoffs.
#[derive(Clone, Encode, Decode, PartialEq, Eq, Debug)]
pub struct GrandpaJustification<Block: BlockT> {
	pub(crate) round: u64,
	pub(crate) commit: Commit<Block>,
	pub(crate) votes_ancestries: Vec<Block::Header>,
}

impl<Block: BlockT> GrandpaJustification<Block> {
	/// Create a GRANDPA justification from the given commit. This method
	/// assumes the commit is valid and well-formed.
	pub fn from_commit<C>(
		client: &Arc<C>,
		round: u64,
		commit: Commit<Block>,
	) -> Result<GrandpaJustification<Block>, Error>
	where
		C: HeaderBackend<Block>,
	{
		let mut votes_ancestries_hashes = HashSet::new();
		let mut votes_ancestries = Vec::new();

		let error = || {
			let msg = "invalid precommits for target commit".to_string();
			Err(Error::Client(ClientError::BadJustification(msg)))
		};

		// we pick the precommit for the lowest block as the base that
		// should serve as the root block for populating ancestry (i.e.
		// collect all headers from all precommit blocks to the base)
		let (base_hash, base_number) = match commit
			.precommits
			.iter()
			.map(|signed| &signed.precommit)
			.min_by_key(|precommit| precommit.target_number)
			.map(|precommit| (precommit.target_hash.clone(), precommit.target_number))
		{
			None => return error(),
			Some(base) => base,
		};

		for signed in commit.precommits.iter() {
			let mut current_hash = signed.precommit.target_hash;
			loop {
				if current_hash == base_hash {
					break
				}

				match client.header(BlockId::Hash(current_hash))? {
					Some(current_header) => {
						// NOTE: this should never happen as we pick the lowest block
						// as base and only traverse backwards from the other blocks
						// in the commit. but better be safe to avoid an unbound loop.
						if *current_header.number() <= base_number {
							return error()
						}

						let parent_hash = *current_header.parent_hash();
						if votes_ancestries_hashes.insert(current_hash) {
							votes_ancestries.push(current_header);
						}

						current_hash = parent_hash;
					},
					_ => return error(),
				}
			}
		}

		Ok(GrandpaJustification { round, commit, votes_ancestries })
	}

	/// Decode a GRANDPA justification and validate the commit and the votes'
	/// ancestry proofs finalize the given block.
	pub fn decode_and_verify_finalizes(
		encoded: &[u8],
		finalized_target: (Block::Hash, NumberFor<Block>),
		set_id: u64,
		voters: &VoterSet<AuthorityId>,
	) -> Result<GrandpaJustification<Block>, ClientError>
	where
		NumberFor<Block>: finality_grandpa::BlockNumberOps,
	{
		let justification = GrandpaJustification::<Block>::decode(&mut &*encoded)
			.map_err(|_| ClientError::JustificationDecode)?;

		if (justification.commit.target_hash, justification.commit.target_number) !=
			finalized_target
		{
			let msg = "invalid commit target in grandpa justification".to_string();
			Err(ClientError::BadJustification(msg))
		} else {
			justification.verify_with_voter_set(set_id, voters).map(|_| justification)
		}
	}

	/// Validate the commit and the votes' ancestry proofs.
	pub fn verify(&self, set_id: u64, authorities: &AuthorityList) -> Result<(), ClientError>
	where
		NumberFor<Block>: finality_grandpa::BlockNumberOps,
	{
		let voters = VoterSet::new(authorities.iter().cloned())
			.ok_or(ClientError::Consensus(sp_consensus::Error::InvalidAuthoritiesSet))?;

		self.verify_with_voter_set(set_id, &voters)
	}

	/// Validate the commit and the votes' ancestry proofs.
	pub(crate) fn verify_with_voter_set(
		&self,
		set_id: u64,
		voters: &VoterSet<AuthorityId>,
	) -> Result<(), ClientError>
	where
		NumberFor<Block>: finality_grandpa::BlockNumberOps,
	{
		use finality_grandpa::Chain;

		let ancestry_chain = AncestryChain::<Block>::new(&self.votes_ancestries);

		match finality_grandpa::validate_commit(&self.commit, voters, &ancestry_chain) {
			Ok(ref result) if result.is_valid() => {},
			_ => {
				let msg = "invalid commit in grandpa justification".to_string();
				return Err(ClientError::BadJustification(msg))
			},
		}

		// we pick the precommit for the lowest block as the base that
		// should serve as the root block for populating ancestry (i.e.
		// collect all headers from all precommit blocks to the base)
		let base_hash = self
			.commit
			.precommits
			.iter()
			.map(|signed| &signed.precommit)
			.min_by_key(|precommit| precommit.target_number)
			.map(|precommit| precommit.target_hash.clone())
			.expect(
				"can only fail if precommits is empty; \
				 commit has been validated above; \
				 valid commits must include precommits; \
				 qed.",
			);

		let mut buf = Vec::new();
		let mut visited_hashes = HashSet::new();
		for signed in self.commit.precommits.iter() {
			if !sp_finality_grandpa::check_message_signature_with_buffer(
				&finality_grandpa::Message::Precommit(signed.precommit.clone()),
				&signed.id,
				&signed.signature,
				self.round,
				set_id,
				&mut buf,
			) {
				return Err(ClientError::BadJustification(
					"invalid signature for precommit in grandpa justification".to_string(),
				))
			}

			if base_hash == signed.precommit.target_hash {
				continue
			}

			match ancestry_chain.ancestry(base_hash, signed.precommit.target_hash) {
				Ok(route) => {
					// ancestry starts from parent hash but the precommit target hash has been
					// visited
					visited_hashes.insert(signed.precommit.target_hash);
					for hash in route {
						visited_hashes.insert(hash);
					}
				},
				_ =>
					return Err(ClientError::BadJustification(
						"invalid precommit ancestry proof in grandpa justification".to_string(),
					)),
			}
		}

		let ancestry_hashes: HashSet<_> =
			self.votes_ancestries.iter().map(|h: &Block::Header| h.hash()).collect();

		if visited_hashes != ancestry_hashes {
			return Err(ClientError::BadJustification(
				"invalid precommit ancestries in grandpa justification with unused headers"
					.to_string(),
			))
		}

		Ok(())
	}

	/// The target block number and hash that this justifications proves finality for.
	pub fn target(&self) -> (NumberFor<Block>, Block::Hash) {
		(self.commit.target_number, self.commit.target_hash)
	}
}

/// A utility trait implementing `finality_grandpa::Chain` using a given set of headers.
/// This is useful when validating commits, using the given set of headers to
/// verify a valid ancestry route to the target commit block.
struct AncestryChain<Block: BlockT> {
	ancestry: HashMap<Block::Hash, Block::Header>,
}

impl<Block: BlockT> AncestryChain<Block> {
	fn new(ancestry: &[Block::Header]) -> AncestryChain<Block> {
		let ancestry: HashMap<_, _> =
			ancestry.iter().cloned().map(|h: Block::Header| (h.hash(), h)).collect();

		AncestryChain { ancestry }
	}
}

impl<Block: BlockT> finality_grandpa::Chain<Block::Hash, NumberFor<Block>> for AncestryChain<Block>
where
	NumberFor<Block>: finality_grandpa::BlockNumberOps,
{
	fn ancestry(
		&self,
		base: Block::Hash,
		block: Block::Hash,
	) -> Result<Vec<Block::Hash>, GrandpaError> {
		let mut route = Vec::new();
		let mut current_hash = block;
		loop {
			if current_hash == base {
				break
			}
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
}
