// Copyright Parity Technologies (UK) Ltd.
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

//! Utilities for generating and verifying GRANDPA warp sync proofs.

use sp_runtime::codec::{self, Decode, Encode};

use crate::{
	best_justification, find_scheduled_change, AuthoritySetChanges, AuthoritySetHardFork,
	BlockNumberOps, GrandpaJustification, SharedAuthoritySet,
};
use sc_client_api::Backend as ClientBackend;
use sc_network_common::sync::warp::{EncodedProof, VerificationResult, WarpSyncProvider};
use sp_blockchain::{Backend as BlockchainBackend, HeaderBackend};
use sp_consensus_grandpa::{AuthorityList, SetId, GRANDPA_ENGINE_ID};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header as HeaderT, NumberFor, One},
};

use std::{collections::HashMap, sync::Arc};

/// Warp proof processing error.
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// Decoding error.
	#[error("Failed to decode block hash: {0}.")]
	DecodeScale(#[from] codec::Error),
	/// Client backend error.
	#[error("{0}")]
	Client(#[from] sp_blockchain::Error),
	/// Invalid request data.
	#[error("{0}")]
	InvalidRequest(String),
	/// Invalid warp proof.
	#[error("{0}")]
	InvalidProof(String),
	/// Missing header or authority set change data.
	#[error("Missing required data to be able to answer request.")]
	MissingData,
}

/// The maximum size in bytes of the `WarpSyncProof`.
pub(super) const MAX_WARP_SYNC_PROOF_SIZE: usize = 8 * 1024 * 1024;

/// A proof of an authority set change.
#[derive(Decode, Encode, Debug)]
pub struct WarpSyncFragment<Block: BlockT> {
	/// The last block that the given authority set finalized. This block should contain a digest
	/// signaling an authority set change from which we can fetch the next authority set.
	pub header: Block::Header,
	/// A justification for the header above which proves its finality. In order to validate it the
	/// verifier must be aware of the authorities and set id for which the justification refers to.
	pub justification: GrandpaJustification<Block>,
}

/// An accumulated proof of multiple authority set changes.
#[derive(Decode, Encode)]
pub struct WarpSyncProof<Block: BlockT> {
	proofs: Vec<WarpSyncFragment<Block>>,
	is_finished: bool,
}

impl<Block: BlockT> WarpSyncProof<Block> {
	/// Generates a warp sync proof starting at the given block. It will generate authority set
	/// change proofs for all changes that happened from `begin` until the current authority set
	/// (capped by MAX_WARP_SYNC_PROOF_SIZE).
	fn generate<Backend>(
		backend: &Backend,
		begin: Block::Hash,
		set_changes: &AuthoritySetChanges<NumberFor<Block>>,
	) -> Result<WarpSyncProof<Block>, Error>
	where
		Backend: ClientBackend<Block>,
	{
		// TODO: cache best response (i.e. the one with lowest begin_number)
		let blockchain = backend.blockchain();

		let begin_number = blockchain
			.block_number_from_id(&BlockId::Hash(begin))?
			.ok_or_else(|| Error::InvalidRequest("Missing start block".to_string()))?;

		if begin_number > blockchain.info().finalized_number {
			return Err(Error::InvalidRequest("Start block is not finalized".to_string()))
		}

		let canon_hash = blockchain.hash(begin_number)?.expect(
			"begin number is lower than finalized number; \
			 all blocks below finalized number must have been imported; \
			 qed.",
		);

		if canon_hash != begin {
			return Err(Error::InvalidRequest(
				"Start block is not in the finalized chain".to_string(),
			))
		}

		let mut proofs = Vec::new();
		let mut proofs_encoded_len = 0;
		let mut proof_limit_reached = false;

		let set_changes = set_changes.iter_from(begin_number).ok_or(Error::MissingData)?;

		for (_, last_block) in set_changes {
			let hash = blockchain.block_hash_from_id(&BlockId::Number(*last_block))?
				.expect("header number comes from previously applied set changes; corresponding hash must exist in db; qed.");

			let header = blockchain
				.header(hash)?
				.expect("header hash obtained from header number exists in db; corresponding header must exist in db too; qed.");

			// the last block in a set is the one that triggers a change to the next set,
			// therefore the block must have a digest that signals the authority set change
			if find_scheduled_change::<Block>(&header).is_none() {
				// if it doesn't contain a signal for standard change then the set must have changed
				// through a forced changed, in which case we stop collecting proofs as the chain of
				// trust in authority handoffs was broken.
				break
			}

			let justification = blockchain
				.justifications(header.hash())?
				.and_then(|just| just.into_justification(GRANDPA_ENGINE_ID))
				.ok_or_else(|| Error::MissingData)?;

			let justification = GrandpaJustification::<Block>::decode(&mut &justification[..])?;

			let proof = WarpSyncFragment { header: header.clone(), justification };
			let proof_size = proof.encoded_size();

			// Check for the limit. We remove some bytes from the maximum size, because we're only
			// counting the size of the `WarpSyncFragment`s. The extra margin is here to leave
			// room for rest of the data (the size of the `Vec` and the boolean).
			if proofs_encoded_len + proof_size >= MAX_WARP_SYNC_PROOF_SIZE - 50 {
				proof_limit_reached = true;
				break
			}

			proofs_encoded_len += proof_size;
			proofs.push(proof);
		}

		let is_finished = if proof_limit_reached {
			false
		} else {
			let latest_justification = best_justification(backend)?.filter(|justification| {
				// the existing best justification must be for a block higher than the
				// last authority set change. if we didn't prove any authority set
				// change then we fallback to make sure it's higher or equal to the
				// initial warp sync block.
				let limit = proofs
					.last()
					.map(|proof| proof.justification.target().0 + One::one())
					.unwrap_or(begin_number);

				justification.target().0 >= limit
			});

			if let Some(latest_justification) = latest_justification {
				let header = blockchain.header(latest_justification.target().1)?
					.expect("header hash corresponds to a justification in db; must exist in db as well; qed.");

				proofs.push(WarpSyncFragment { header, justification: latest_justification })
			}

			true
		};

		let final_outcome = WarpSyncProof { proofs, is_finished };
		debug_assert!(final_outcome.encoded_size() <= MAX_WARP_SYNC_PROOF_SIZE);
		Ok(final_outcome)
	}

	/// Verifies the warp sync proof starting at the given set id and with the given authorities.
	/// Verification stops when either the proof is exhausted or finality for the target header can
	/// be proven. If the proof is valid the new set id and authorities is returned.
	fn verify(
		&self,
		set_id: SetId,
		authorities: AuthorityList,
		hard_forks: &HashMap<(Block::Hash, NumberFor<Block>), (SetId, AuthorityList)>,
	) -> Result<(SetId, AuthorityList), Error>
	where
		NumberFor<Block>: BlockNumberOps,
	{
		let mut current_set_id = set_id;
		let mut current_authorities = authorities;

		for (fragment_num, proof) in self.proofs.iter().enumerate() {
			let hash = proof.header.hash();
			let number = *proof.header.number();

			if let Some((set_id, list)) = hard_forks.get(&(hash, number)) {
				current_set_id = *set_id;
				current_authorities = list.clone();
			} else {
				proof
					.justification
					.verify(current_set_id, &current_authorities)
					.map_err(|err| Error::InvalidProof(err.to_string()))?;

				if proof.justification.target().1 != hash {
					return Err(Error::InvalidProof(
						"Mismatch between header and justification".to_owned(),
					))
				}

				if let Some(scheduled_change) = find_scheduled_change::<Block>(&proof.header) {
					current_authorities = scheduled_change.next_authorities;
					current_set_id += 1;
				} else if fragment_num != self.proofs.len() - 1 || !self.is_finished {
					// Only the last fragment of the last proof message is allowed to be missing the
					// authority set change.
					return Err(Error::InvalidProof(
						"Header is missing authority set change digest".to_string(),
					))
				}
			}
		}
		Ok((current_set_id, current_authorities))
	}
}

/// Implements network API for warp sync.
pub struct NetworkProvider<Block: BlockT, Backend: ClientBackend<Block>>
where
	NumberFor<Block>: BlockNumberOps,
{
	backend: Arc<Backend>,
	authority_set: SharedAuthoritySet<Block::Hash, NumberFor<Block>>,
	hard_forks: HashMap<(Block::Hash, NumberFor<Block>), (SetId, AuthorityList)>,
}

impl<Block: BlockT, Backend: ClientBackend<Block>> NetworkProvider<Block, Backend>
where
	NumberFor<Block>: BlockNumberOps,
{
	/// Create a new istance for a given backend and authority set.
	pub fn new(
		backend: Arc<Backend>,
		authority_set: SharedAuthoritySet<Block::Hash, NumberFor<Block>>,
		hard_forks: Vec<AuthoritySetHardFork<Block>>,
	) -> Self {
		NetworkProvider {
			backend,
			authority_set,
			hard_forks: hard_forks
				.into_iter()
				.map(|fork| (fork.block, (fork.set_id, fork.authorities)))
				.collect(),
		}
	}
}

impl<Block: BlockT, Backend: ClientBackend<Block>> WarpSyncProvider<Block>
	for NetworkProvider<Block, Backend>
where
	NumberFor<Block>: BlockNumberOps,
{
	fn generate(
		&self,
		start: Block::Hash,
	) -> Result<EncodedProof, Box<dyn std::error::Error + Send + Sync>> {
		let proof = WarpSyncProof::<Block>::generate(
			&*self.backend,
			start,
			&self.authority_set.authority_set_changes(),
		)
		.map_err(Box::new)?;
		Ok(EncodedProof(proof.encode()))
	}

	fn verify(
		&self,
		proof: &EncodedProof,
		set_id: SetId,
		authorities: AuthorityList,
	) -> Result<VerificationResult<Block>, Box<dyn std::error::Error + Send + Sync>> {
		let EncodedProof(proof) = proof;
		let proof = WarpSyncProof::<Block>::decode(&mut proof.as_slice())
			.map_err(|e| format!("Proof decoding error: {:?}", e))?;
		let last_header = proof
			.proofs
			.last()
			.map(|p| p.header.clone())
			.ok_or_else(|| "Empty proof".to_string())?;
		let (next_set_id, next_authorities) =
			proof.verify(set_id, authorities, &self.hard_forks).map_err(Box::new)?;
		if proof.is_finished {
			Ok(VerificationResult::<Block>::Complete(next_set_id, next_authorities, last_header))
		} else {
			Ok(VerificationResult::<Block>::Partial(
				next_set_id,
				next_authorities,
				last_header.hash(),
			))
		}
	}

	fn current_authorities(&self) -> AuthorityList {
		self.authority_set.inner().current_authorities.clone()
	}
}

#[cfg(test)]
mod tests {
	use super::{codec::Encode, WarpSyncProof};
	use crate::{AuthoritySetChanges, GrandpaJustification};
	use rand::prelude::*;
	use sc_block_builder::BlockBuilderProvider;
	use sp_blockchain::HeaderBackend;
	use sp_consensus::BlockOrigin;
	use sp_consensus_grandpa::GRANDPA_ENGINE_ID;
	use sp_keyring::Ed25519Keyring;
	use std::sync::Arc;
	use substrate_test_runtime_client::{
		BlockBuilderExt, ClientBlockImportExt, ClientExt, DefaultTestClientBuilderExt,
		TestClientBuilder, TestClientBuilderExt,
	};

	#[test]
	fn warp_sync_proof_generate_verify() {
		let mut rng = rand::rngs::StdRng::from_seed([0; 32]);
		let builder = TestClientBuilder::new();
		let backend = builder.backend();
		let mut client = Arc::new(builder.build());

		let available_authorities = Ed25519Keyring::iter().collect::<Vec<_>>();
		let genesis_authorities = vec![(Ed25519Keyring::Alice.public().into(), 1)];

		let mut current_authorities = vec![Ed25519Keyring::Alice];
		let mut current_set_id = 0;
		let mut authority_set_changes = Vec::new();

		for n in 1..=100 {
			let mut builder = client.new_block(Default::default()).unwrap();
			let mut new_authorities = None;

			// we will trigger an authority set change every 10 blocks
			if n != 0 && n % 10 == 0 {
				// pick next authorities and add digest for the set change
				let n_authorities = rng.gen_range(1..available_authorities.len());
				let next_authorities = available_authorities
					.choose_multiple(&mut rng, n_authorities)
					.cloned()
					.collect::<Vec<_>>();

				new_authorities = Some(next_authorities.clone());

				let next_authorities = next_authorities
					.iter()
					.map(|keyring| (keyring.public().into(), 1))
					.collect::<Vec<_>>();

				let digest = sp_runtime::generic::DigestItem::Consensus(
					sp_consensus_grandpa::GRANDPA_ENGINE_ID,
					sp_consensus_grandpa::ConsensusLog::ScheduledChange(
						sp_consensus_grandpa::ScheduledChange { delay: 0u64, next_authorities },
					)
					.encode(),
				);

				builder.push_deposit_log_digest_item(digest).unwrap();
			}

			let block = builder.build().unwrap().block;

			futures::executor::block_on(client.import(BlockOrigin::Own, block)).unwrap();

			if let Some(new_authorities) = new_authorities {
				// generate a justification for this block, finalize it and note the authority set
				// change
				let (target_hash, target_number) = {
					let info = client.info();
					(info.best_hash, info.best_number)
				};

				let mut precommits = Vec::new();
				for keyring in &current_authorities {
					let precommit = finality_grandpa::Precommit { target_hash, target_number };

					let msg = finality_grandpa::Message::Precommit(precommit.clone());
					let encoded = sp_consensus_grandpa::localized_payload(42, current_set_id, &msg);
					let signature = keyring.sign(&encoded[..]).into();

					let precommit = finality_grandpa::SignedPrecommit {
						precommit,
						signature,
						id: keyring.public().into(),
					};

					precommits.push(precommit);
				}

				let commit = finality_grandpa::Commit { target_hash, target_number, precommits };

				let justification = GrandpaJustification::from_commit(&client, 42, commit).unwrap();

				client
					.finalize_block(target_hash, Some((GRANDPA_ENGINE_ID, justification.encode())))
					.unwrap();

				authority_set_changes.push((current_set_id, n));

				current_set_id += 1;
				current_authorities = new_authorities;
			}
		}

		let authority_set_changes = AuthoritySetChanges::from(authority_set_changes);

		// generate a warp sync proof
		let genesis_hash = client.hash(0).unwrap().unwrap();

		let warp_sync_proof =
			WarpSyncProof::generate(&*backend, genesis_hash, &authority_set_changes).unwrap();

		// verifying the proof should yield the last set id and authorities
		let (new_set_id, new_authorities) =
			warp_sync_proof.verify(0, genesis_authorities, &Default::default()).unwrap();

		let expected_authorities = current_authorities
			.iter()
			.map(|keyring| (keyring.public().into(), 1))
			.collect::<Vec<_>>();

		assert_eq!(new_set_id, current_set_id);
		assert_eq!(new_authorities, expected_authorities);
	}
}
