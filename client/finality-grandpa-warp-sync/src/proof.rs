// Copyright 2021 Parity Technologies (UK) Ltd.
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

use codec::{Decode, Encode};

use sc_finality_grandpa::{AuthoritySetChanges, GrandpaJustification};
use sp_blockchain::Backend as BlockchainBackend;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, NumberFor},
};

use crate::HandleRequestError;

/// The maximum number of authority set change proofs to include in a single warp sync proof.
const MAX_CHANGES_PER_WARP_SYNC_PROOF: usize = 256;

#[derive(Decode, Encode)]
pub struct AuthoritySetChangeProof<Block: BlockT> {
	/// must contain the authorities for the following set
	pub header: Block::Header,
	/// this justification proves finality of the header above
	/// it must be validated against the authorities of the previous set.
	pub justification: GrandpaJustification<Block>,
}

#[derive(Decode, Encode)]
pub struct WarpSyncProof<Block: BlockT> {
	proofs: Vec<AuthoritySetChangeProof<Block>>,
}

impl<Block: BlockT> WarpSyncProof<Block> {
	pub fn generate<Backend>(
		backend: &Backend,
		begin: Block::Hash,
		set_changes: &AuthoritySetChanges<NumberFor<Block>>,
	) -> Result<WarpSyncProof<Block>, HandleRequestError>
	where
		Backend: BlockchainBackend<Block>,
	{
		// TODO: cache best response (i.e. the one with lowest begin_number)

		let begin_number = backend
			.block_number_from_id(&BlockId::Hash(begin))?
			.ok_or_else(|| HandleRequestError::InvalidRequest("Missing start block".to_string()))?;

		if begin_number > backend.info().finalized_number {
			return Err(HandleRequestError::InvalidRequest(
				"Start block is not finalized".to_string(),
			));
		}

		let canon_hash = backend.hash(begin_number)?.expect(
			"begin number is lower than finalized number; \
			 all blocks below finalized number must have been imported; \
			 qed.",
		);

		if canon_hash != begin {
			return Err(HandleRequestError::InvalidRequest(
				"Start block is not in the finalized chain".to_string(),
			));
		}

		let mut proofs = Vec::new();

		for (_, last_block) in set_changes.iter_from(begin_number) {
			if proofs.len() >= MAX_CHANGES_PER_WARP_SYNC_PROOF {
				break;
			}

			if *last_block <= begin_number {
				continue;
			}

			let header = backend.header(BlockId::Number(*last_block))?.expect(
				"header number comes from previously applied set changes; must exist in db; qed.",
			);

			// the last block in a set is the one that triggers a change to the next set,
			// therefore the block must have a digest that signals the authority set change
			if sc_finality_grandpa::find_scheduled_change::<Block>(&header).is_none() {
				// if it doesn't contain a signal for standard change then the set must have changed
				// through a forced changed, in which case we stop collecting proofs as the chain of
				// trust in authority handoffs was broken.
				break;
			}

			let justification = backend.justification(BlockId::Number(*last_block))?.expect(
				"header is last in set and contains standard change signal; \
				 must have justification; \
				 qed.",
			);

			let justification = GrandpaJustification::<Block>::decode(&mut &justification[..])?;

			proofs.push(AuthoritySetChangeProof {
				header: header.clone(),
				justification,
			});
		}

		Ok(WarpSyncProof { proofs })
	}
}
