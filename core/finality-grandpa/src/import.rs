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
use parking_lot::RwLockWriteGuard;

use client::{blockchain, CallExecutor, Client, error::Error as ClientError};
use client::backend::Backend;
use client::runtime_api::Core as CoreApi;
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

use crate::{Error, CommandOrError, NewAuthoritySet, VoterCommand};
use authorities::{AuthoritySet, SharedAuthoritySet, DelayKind, PendingChange};
use aux_schema::AUTHORITY_SET_KEY;
use consensus_changes::SharedConsensusChanges;
use environment::{canonical_at_height, finalize_block};
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
	send_voter_commands: mpsc::UnboundedSender<VoterCommand<Block::Hash, NumberFor<Block>>>,
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

enum AppliedChanges<H, N> {
	Standard,
	Forced(NewAuthoritySet<H, N>),
	None,
}

impl<H, N> AppliedChanges<H, N> {
	fn needs_justification(&self) -> bool {
		match *self {
			AppliedChanges::Standard => true,
			AppliedChanges::Forced(_) | AppliedChanges::None => false,
		}
	}
}

struct PendingSetChanges<'a, Block: 'a + BlockT> {
	just_in_case: Option<(
		AuthoritySet<Block::Hash, NumberFor<Block>>,
		RwLockWriteGuard<'a, AuthoritySet<Block::Hash, NumberFor<Block>>>,
	)>,
	applied_changes: AppliedChanges<Block::Hash, NumberFor<Block>>,
	do_pause: bool,
}

impl<'a, Block: 'a + BlockT> PendingSetChanges<'a, Block> {
	// revert the pending set change explicitly.
	fn revert(self) { }

	fn defuse(mut self) -> (AppliedChanges<Block::Hash, NumberFor<Block>>, bool) {
		self.just_in_case = None;
		let applied_changes = ::std::mem::replace(&mut self.applied_changes, AppliedChanges::None);
		(applied_changes, self.do_pause)
	}
}

impl<'a, Block: 'a + BlockT> Drop for PendingSetChanges<'a, Block> {
	fn drop(&mut self) {
		if let Some((old_set, mut authorities)) = self.just_in_case.take() {
			*authorities = old_set;
		}
	}
}

impl<B, E, Block: BlockT<Hash=H256>, RA, PRA> GrandpaBlockImport<B, E, Block, RA, PRA> where
	NumberFor<Block>: grandpa::BlockNumberOps,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
	DigestFor<Block>: Encode,
	DigestItemFor<Block>: DigestItem<AuthorityId=Ed25519AuthorityId>,
	RA: Send + Sync,
	PRA: ProvideRuntimeApi,
	PRA::Api: GrandpaApi<Block>,
{
	// check for a new authority set change.
	fn check_new_change(&self, header: &Block::Header, hash: Block::Hash)
		-> Result<Option<PendingChange<Block::Hash, NumberFor<Block>>>, ConsensusError>
	{
		let at = BlockId::hash(*header.parent_hash());
		let digest = header.digest();

		let api = self.api.runtime_api();

		// check for forced change.
		{
			let maybe_change = api.grandpa_forced_change(
				&at,
				digest,
			);

			match maybe_change {
				Err(e) => match api.version(&at) {
					Err(e) => return Err(ConsensusErrorKind::ClientImport(e.to_string()).into()),
					Ok(version) => if version.has_api_with::<GrandpaApi<Block>, _>(|v| v >= 2) {
						// API version is high enough to support forced changes
						// but got error, so it is legitimate.
						return Err(ConsensusErrorKind::ClientImport(e.to_string()).into())
					}
				}
				Ok(None) => {},
				Ok(Some(change)) => return Ok(Some(PendingChange {
					next_authorities: change.next_authorities,
					delay: change.delay,
					canon_height: *header.number(),
					canon_hash: hash,
					delay_kind: DelayKind::Best,
				})),
			}
		}

		// check normal scheduled change.
		{
			let maybe_change = api.grandpa_pending_change(
				&at,
				digest,
			);

			match maybe_change {
				Err(e) => Err(ConsensusErrorKind::ClientImport(e.to_string()).into()),
				Ok(Some(change)) => Ok(Some(PendingChange {
					next_authorities: change.next_authorities,
					delay: change.delay,
					canon_height: *header.number(),
					canon_hash: hash,
					delay_kind: DelayKind::Finalized,
				})),
				Ok(None) => Ok(None),
			}
		}
	}

	fn make_authorities_changes<'a>(&'a self, block: &mut ImportBlock<Block>, hash: Block::Hash)
		-> Result<PendingSetChanges<'a, Block>, ConsensusError>
	{
		use consensus_common::ForkChoiceStrategy;


		// when we update the authorities, we need to hold the lock
		// until the block is written to prevent a race if we need to restore
		// the old authority set on error or panic.
		struct InnerGuard<'a, T: 'a> {
			old: Option<T>,
			guard: Option<RwLockWriteGuard<'a, T>>,
		}

		impl<'a, T: 'a> InnerGuard<'a, T> {
			fn as_mut(&mut self) -> &mut T {
				&mut **self.guard.as_mut().expect("only taken on deconstruction; qed")
			}

			fn set_old(&mut self, old: T) {
				if self.old.is_none() {
					// ignore "newer" old changes.
					self.old = Some(old);
				}
			}

			fn consume(mut self) -> Option<(T, RwLockWriteGuard<'a, T>)> {
				if let Some(old) = self.old.take() {
					Some((old, self.guard.take().expect("only taken on deconstruction; qed")))
				} else {
					None
				}
			}
		}

		impl<'a, T: 'a> Drop for InnerGuard<'a, T> {
			fn drop(&mut self) {
				if let (Some(mut guard), Some(old)) = (self.guard.take(), self.old.take()) {
					*guard = old;
				}
			}
		}

		let number = block.header.number().clone();
		let maybe_change = self.check_new_change(
			&block.header,
			hash,
		)?;

		// NOTE: this is valid because our underyling `BlockImport`
		// is always a client -- if there were a lower level `BlockImport`
		// it might change the fork choice strategy.
		let new_is_best = match block.fork_choice {
			ForkChoiceStrategy::Custom(v) => v,
			ForkChoiceStrategy::LongestChain => {
				let info = self.inner.info()
					.map_err(|e: ClientError| ConsensusErrorKind::ClientImport(e.to_string()))
					.map_err(ConsensusError::from)?;

				block.header.number() > &info.chain.best_number
			}
		};

		// tells us the hash that is canonical at a given height
		// consistent with querying client directly after importing the block.
		let canon_at_height = |canon_number| -> Result<_, ClientError> {
			canonical_at_height(
				&self.inner,
				(hash, number),
				new_is_best,
				canon_number,
			)
		};

		let mut guard = InnerGuard {
			guard: Some(self.authority_set.inner().write()),
			old: None,
		};

		// whether to pause the old authority set -- happens after import
		// of a forced change block.
		let mut do_pause = false;

		// add any pending changes.
		if let Some(change) = maybe_change {
			let parent_hash = *block.header.parent_hash();

			let old = guard.as_mut().clone();
			guard.set_old(old);

			let is_equal_or_descendent_of = |base: &Block::Hash| -> Result<(), ConsensusError> {
				let error = || {
					debug!(target: "afg", "rejecting change: {} is in the same chain as {}",
						hash, base);
					Err(ConsensusErrorKind::ClientImport(
						format!("Incorrect base hash")
					).into())
				};

				if *base == hash { return error(); }
				if *base == parent_hash { return error(); }

				let tree_route = blockchain::tree_route(
					self.inner.backend().blockchain(),
					BlockId::Hash(parent_hash),
					BlockId::Hash(*base),
				);

				let tree_route = match tree_route {
					Err(e) => return Err(
						ConsensusErrorKind::ClientImport(e.to_string()).into()
					),
					Ok(route) => route,
				};

				if tree_route.common_block().hash == *base {
					return error();
				}

				Ok(())
			};

			if let DelayKind::Best = change.delay_kind {
				do_pause = true;
			}

			guard.as_mut().add_pending_change(
				change,
				is_equal_or_descendent_of,
			)?;
		}

		let applied_changes = {
			let forced_change_set = guard.as_mut().apply_forced_changes(number, &canon_at_height)
				.map_err(|e| ConsensusErrorKind::ClientImport(e.to_string()))
				.map_err(ConsensusError::from)?;

			if let Some(new_set) = forced_change_set {
				let new_authorities = {
					let (set_id, new_authorities) = new_set.current();
					NewAuthoritySet {
						canon_number: number,
						canon_hash: hash,
						set_id,
						authorities: new_authorities.to_vec(),
					}
				};
				let old = ::std::mem::replace(guard.as_mut(), new_set);
				guard.set_old(old);

				AppliedChanges::Forced(new_authorities)
			} else {
				let did_standard = guard.as_mut().enacts_standard_change(number, &canon_at_height)
					.map_err(|e| ConsensusErrorKind::ClientImport(e.to_string()))
					.map_err(ConsensusError::from)?;

				if did_standard {
					AppliedChanges::Standard
				} else {
					AppliedChanges::None
				}
			}
		};

		// consume the guard safely.
		let just_in_case = guard.consume();
		if let Some((_, ref authorities)) = just_in_case {
			block.auxiliary.push((AUTHORITY_SET_KEY.to_vec(), Some(authorities.encode())));
		}
		Ok(PendingSetChanges { just_in_case, applied_changes, do_pause })
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
		use client::blockchain::HeaderBackend;

		let hash = block.post_header().hash();
		let number = block.header.number().clone();

		// early exit if block already in chain, otherwise the check for
		// authority changes will error when trying to re-import a change block
		match self.inner.backend().blockchain().status(BlockId::Hash(hash)) {
			Ok(blockchain::BlockStatus::InChain) => return Ok(ImportResult::AlreadyInChain),
			Ok(blockchain::BlockStatus::Unknown) => {},
			Err(e) => return Err(ConsensusErrorKind::ClientImport(e.to_string()).into()),
		}

		let pending_changes = self.make_authorities_changes(&mut block, hash)?;

		// we don't want to finalize on `inner.import_block`
		let mut justification = block.justification.take();
		let enacts_consensus_change = new_authorities.is_some();
		let import_result = self.inner.import_block(block, new_authorities);

		let import_result = {
			match import_result {
				Ok(ImportResult::Queued) => ImportResult::Queued,
				Ok(r) => {
					debug!(target: "afg", "Restoring old authority set after block import result: {:?}", r);
					pending_changes.revert();
					return Ok(r);
				},
				Err(e) => {
					debug!(target: "afg", "Restoring old authority set after block import error: {:?}", e);
					pending_changes.revert();
					return Err(ConsensusErrorKind::ClientImport(e.to_string()).into());
				},
			}
		};

		let (applied_changes, do_pause) = pending_changes.defuse();

		// Send the pause signal after import but BEFORE sending a `ChangeAuthorities` message.
		let _ = self.send_voter_commands.unbounded_send(VoterCommand::Pause(format!("Forced change scheduled after inactivity")));

		let needs_justification = applied_changes.needs_justification();
		if let AppliedChanges::Forced(new) = applied_changes {
			// NOTE: when we do a force change we are "discrediting" the old set
			// so we ignore any justifications from them.
			// TODO: figure out if this is right...the new set will finalize this block as
			// well so we should probably only reject justifications from the old set.
			justification = None;
			let _ = self.send_voter_commands.unbounded_send(VoterCommand::ChangeAuthorities(new));
		}

		if !needs_justification && !enacts_consensus_change {
			return Ok(import_result);
		}

		match justification {
			Some(justification) => {
				self.import_justification(hash, number, justification, needs_justification)?;
			},
			None => {
				if needs_justification {
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
		send_voter_commands: mpsc::UnboundedSender<VoterCommand<Block::Hash, NumberFor<Block>>>,
		consensus_changes: SharedConsensusChanges<Block::Hash, NumberFor<Block>>,
		api: Arc<PRA>,
	) -> GrandpaBlockImport<B, E, Block, RA, PRA> {
		GrandpaBlockImport {
			inner,
			authority_set,
			send_voter_commands,
			consensus_changes,
			api,
		}
	}
}

impl<B, E, Block: BlockT<Hash=H256>, RA, PRA> GrandpaBlockImport<B, E, Block, RA, PRA>
	where
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
			Err(CommandOrError::VoterCommand(command)) => {
				info!(target: "finality", "Imported justification for block #{} that triggers \
					command {}, signalling voter.", number, command);

				if let Err(e) = self.send_voter_commands.unbounded_send(command) {
					return Err(ConsensusErrorKind::ClientImport(e.to_string()).into());
				}
			},
			Err(CommandOrError::Error(e)) => {
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
