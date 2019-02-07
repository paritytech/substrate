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

use std::sync::Arc;

use codec::Encode;
use futures::sync::mpsc;

use client::{CallExecutor, Client};
use client::backend::Backend;
use consensus_common::{
	BlockImport, Error as ConsensusError, ErrorKind as ConsensusErrorKind,
	ImportBlock, ImportResult, JustificationImport,
};
use fg_primitives::GrandpaApi;
use runtime_primitives::Justification;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{
	Block as BlockT, DigestFor, DigestItemFor, DigestItem,
	Header as HeaderT, NumberFor, ProvideRuntimeApi,
};
use substrate_primitives::{H256, Ed25519AuthorityId, Blake2Hasher};

use crate::{AUTHORITY_SET_KEY, Error};
use authorities::SharedAuthoritySet;
use consensus_changes::SharedConsensusChanges;
use environment::{canonical_at_height, finalize_block, ExitOrError, NewAuthoritySet};
use justification::GrandpaJustification;

/// A block-import handler for GRANDPA.
///
/// This scans each imported block for signals of changing authority set.
/// If the block being imported enacts an authority set change then:
/// - If the current authority set is still live: we import the block
/// - Otherwise, the block must include a valid justification.
///
/// When using GRANDPA, the block import worker should be using this block import
/// object.
pub struct GrandpaBlockImport<B, E, Block: BlockT<Hash=H256>, RA, PRA> {
	inner: Arc<Client<B, E, Block, RA>>,
	authority_set: SharedAuthoritySet<Block::Hash, NumberFor<Block>>,
	authority_set_change: mpsc::UnboundedSender<NewAuthoritySet<Block::Hash, NumberFor<Block>>>,
	consensus_changes: SharedConsensusChanges<Block::Hash, NumberFor<Block>>,
	api: Arc<PRA>,
}

impl<B, E, Block: BlockT<Hash=H256>, RA, PRA> JustificationImport<Block>
	for GrandpaBlockImport<B, E, Block, RA, PRA> where
		NumberFor<Block>: grandpa::BlockNumberOps,
		B: Backend<Block, Blake2Hasher> + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		DigestFor<Block>: Encode,
		DigestItemFor<Block>: DigestItem<AuthorityId=Ed25519AuthorityId>,
		RA: Send + Sync,
		PRA: ProvideRuntimeApi,
		PRA::Api: GrandpaApi<Block>,
{
	type Error = ConsensusError;

	fn on_start(&self, link: &::consensus_common::import_queue::Link<Block>) {
		let chain_info = match self.inner.info() {
			Ok(info) => info.chain,
			_ => return,
		};

		// request justifications for all pending changes for which change blocks have already been imported
		for pending_change in self.authority_set.inner().read().pending_changes() {
			if pending_change.effective_number() > chain_info.finalized_number &&
				pending_change.effective_number() <= chain_info.best_number
			{
				let effective_block_hash = self.inner.best_containing(
					pending_change.canon_hash,
					Some(pending_change.effective_number()),
				);

				if let Ok(Some(hash)) = effective_block_hash {
					if let Ok(Some(header)) = self.inner.header(&BlockId::Hash(hash)) {
						if *header.number() == pending_change.effective_number() {
							link.request_justification(&header.hash(), *header.number());
						}
					}
				}
			}
		}
	}

	fn import_justification(
		&self,
		hash: Block::Hash,
		number: NumberFor<Block>,
		justification: Justification,
	) -> Result<(), Self::Error> {
		self.import_justification(hash, number, justification, false)
	}
}

impl<B, E, Block: BlockT<Hash=H256>, RA, PRA> BlockImport<Block>
	for GrandpaBlockImport<B, E, Block, RA, PRA> where
		NumberFor<Block>: grandpa::BlockNumberOps,
		B: Backend<Block, Blake2Hasher> + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		DigestFor<Block>: Encode,
		DigestItemFor<Block>: DigestItem<AuthorityId=Ed25519AuthorityId>,
		RA: Send + Sync,
		PRA: ProvideRuntimeApi,
		PRA::Api: GrandpaApi<Block>,
{
	type Error = ConsensusError;

	fn import_block(&self, mut block: ImportBlock<Block>, new_authorities: Option<Vec<Ed25519AuthorityId>>)
		-> Result<ImportResult, Self::Error>
	{
		use authorities::PendingChange;

		let hash = block.post_header().hash();
		let number = block.header.number().clone();

		let maybe_change = self.api.runtime_api().grandpa_pending_change(
			&BlockId::hash(*block.header.parent_hash()),
			&block.header.digest().clone(),
		);

		let maybe_change = match maybe_change {
			Err(e) => return Err(ConsensusErrorKind::ClientImport(e.to_string()).into()),
			Ok(maybe) => maybe,
		};

		// when we update the authorities, we need to hold the lock
		// until the block is written to prevent a race if we need to restore
		// the old authority set on error.
		let just_in_case = if let Some(change) = maybe_change {
			let parent_hash = *block.header.parent_hash();

			let mut authorities = self.authority_set.inner().write();
			let old_set = authorities.clone();

			let is_equal_or_descendent_of = |base: &Block::Hash| -> Result<(), ConsensusError> {
				let error = || {
					debug!(target: "afg", "rejecting change: {} is in the same chain as {}", hash, base);
					Err(ConsensusErrorKind::ClientImport("Incorrect base hash".to_string()).into())
				};

				if *base == hash { return error(); }
				if *base == parent_hash { return error(); }

				let tree_route = ::client::blockchain::tree_route(
					self.inner.backend().blockchain(),
					BlockId::Hash(parent_hash),
					BlockId::Hash(*base),
				);

				let tree_route = match tree_route {
					Err(e) => return Err(ConsensusErrorKind::ClientImport(e.to_string()).into()),
					Ok(route) => route,
				};

				if tree_route.common_block().hash == *base {
					return error();
				}

				Ok(())
			};

			authorities.add_pending_change(
				PendingChange {
					next_authorities: change.next_authorities,
					finalization_depth: change.delay,
					canon_height: number,
					canon_hash: hash,
				},
				is_equal_or_descendent_of,
			)?;

			block.auxiliary.push((AUTHORITY_SET_KEY.to_vec(), Some(authorities.encode())));
			Some((old_set, authorities))
		} else {
			None
		};

		// we don't want to finalize on `inner.import_block`
		let justification = block.justification.take();
		let enacts_consensus_change = new_authorities.is_some();
		let import_result = self.inner.import_block(block, new_authorities);

		let import_result = {
			// we scope this so that `just_in_case` is dropped eagerly and releases the authorities lock
			let revert_authorities = || if let Some((old_set, mut authorities)) = just_in_case {
				*authorities = old_set;
			};

			match import_result {
				Ok(ImportResult::Queued) => ImportResult::Queued,
				Ok(r) => {
					debug!(target: "afg", "Restoring old authority set after block import result: {:?}", r);
					revert_authorities();
					return Ok(r);
				},
				Err(e) => {
					debug!(target: "afg", "Restoring old authority set after block import error: {:?}", e);
					revert_authorities();
					return Err(ConsensusErrorKind::ClientImport(e.to_string()).into());
				},
			}
		};

		let enacts_change = self.authority_set.inner().read().enacts_change(number, |canon_number| {
			canonical_at_height(&self.inner, (hash, number), canon_number)
		}).map_err(|e| ConsensusError::from(ConsensusErrorKind::ClientImport(e.to_string())))?;

		if !enacts_change && !enacts_consensus_change {
			return Ok(import_result);
		}

		match justification {
			Some(justification) => {
				self.import_justification(hash, number, justification, enacts_change)?;
			},
			None => {
				if enacts_change {
					trace!(
						target: "finality",
						"Imported unjustified block #{} that enacts authority set change, waiting for finality for enactment.",
						number,
					);
				}

				// we have imported block with consensus data changes, but without justification
				// => remember to create justification when next block will be finalized
				if enacts_consensus_change {
					self.consensus_changes.lock().note_change((number, hash));
				}

				return Ok(ImportResult::NeedsJustification);
			}
		}

		Ok(import_result)
	}

	fn check_block(
		&self,
		hash: Block::Hash,
		parent_hash: Block::Hash,
	) -> Result<ImportResult, Self::Error> {
		self.inner.check_block(hash, parent_hash)
	}
}

impl<B, E, Block: BlockT<Hash=H256>, RA, PRA> GrandpaBlockImport<B, E, Block, RA, PRA> {
	pub(crate) fn new(
		inner: Arc<Client<B, E, Block, RA>>,
		authority_set: SharedAuthoritySet<Block::Hash, NumberFor<Block>>,
		authority_set_change: mpsc::UnboundedSender<NewAuthoritySet<Block::Hash, NumberFor<Block>>>,
		consensus_changes: SharedConsensusChanges<Block::Hash, NumberFor<Block>>,
		api: Arc<PRA>,
	) -> GrandpaBlockImport<B, E, Block, RA, PRA> {
		GrandpaBlockImport {
			inner,
			authority_set,
			authority_set_change,
			consensus_changes,
			api,
		}
	}
}

impl<B, E, Block: BlockT<Hash=H256>, RA, PRA>
	GrandpaBlockImport<B, E, Block, RA, PRA> where
		NumberFor<Block>: grandpa::BlockNumberOps,
		B: Backend<Block, Blake2Hasher> + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		RA: Send + Sync,
{

	/// Import a block justification and finalize the block.
	///
	/// If `enacts_change` is set to true, then finalizing this block *must*
	/// enact an authority set change, the function will panic otherwise.
	fn import_justification(
		&self,
		hash: Block::Hash,
		number: NumberFor<Block>,
		justification: Justification,
		enacts_change: bool,
	) -> Result<(), ConsensusError> {
		let justification = GrandpaJustification::decode_and_verify(
			justification,
			self.authority_set.set_id(),
			&self.authority_set.current_authorities(),
		);

		let justification = match justification {
			Err(e) => return Err(ConsensusErrorKind::ClientImport(e.to_string()).into()),
			Ok(justification) => justification,
		};

		let result = finalize_block(
			&*self.inner,
			&self.authority_set,
			&self.consensus_changes,
			None,
			hash,
			number,
			justification.into(),
		);

		match result {
			Err(ExitOrError::AuthoritiesChanged(new)) => {
				info!(target: "finality", "Imported justification for block #{} that enacts authority set change, signalling voter.", number);
				if let Err(e) = self.authority_set_change.unbounded_send(new) {
					return Err(ConsensusErrorKind::ClientImport(e.to_string()).into());
				}
			},
			Err(ExitOrError::Error(e)) => {
				return Err(match e {
					Error::Grandpa(error) => ConsensusErrorKind::ClientImport(error.to_string()),
					Error::Network(error) => ConsensusErrorKind::ClientImport(error),
					Error::Blockchain(error) => ConsensusErrorKind::ClientImport(error),
					Error::Client(error) => ConsensusErrorKind::ClientImport(error.to_string()),
					Error::Timer(error) => ConsensusErrorKind::ClientImport(error.to_string()),
				}.into());
			},
			Ok(_) => {
				assert!(!enacts_change, "returns Ok when no authority set change should be enacted; qed;");
			},
		}

		Ok(())
	}
}
