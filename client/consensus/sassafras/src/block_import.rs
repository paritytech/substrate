// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Types and functions related to block import.

use super::*;
use sc_client_api::{AuxDataOperations, FinalityNotification, PreCommitActions};
use sp_blockchain::BlockStatus;

/// Block-import handler for Sassafras.
///
/// This scans each imported block for epoch change announcements. The announcements are
/// tracked in a tree (of all forks), and the import logic validates all epoch change
/// transitions, i.e. whether a given epoch change is expected or whether it is missing.
///
/// The epoch change tree should be pruned as blocks are finalized.
pub struct SassafrasBlockImport<B: BlockT, C, I> {
	inner: I,
	client: Arc<C>,
	epoch_changes: SharedEpochChanges<B, Epoch>,
	genesis_config: SassafrasConfiguration,
}

impl<Block: BlockT, I: Clone, Client> Clone for SassafrasBlockImport<Block, Client, I> {
	fn clone(&self) -> Self {
		SassafrasBlockImport {
			inner: self.inner.clone(),
			client: self.client.clone(),
			epoch_changes: self.epoch_changes.clone(),
			genesis_config: self.genesis_config.clone(),
		}
	}
}

fn aux_storage_cleanup<B, C>(
	_client: &C,
	_notification: &FinalityNotification<B>,
) -> AuxDataOperations
where
	B: BlockT,
	C: HeaderMetadata<B> + HeaderBackend<B>,
{
	// TODO-SASS-P3
	Default::default()
}

impl<B: BlockT, C, I> SassafrasBlockImport<B, C, I>
where
	C: AuxStore
		+ HeaderBackend<B>
		+ HeaderMetadata<B, Error = sp_blockchain::Error>
		+ PreCommitActions<B>
		+ 'static,
{
	/// Constructor.
	pub fn new(
		inner: I,
		client: Arc<C>,
		epoch_changes: SharedEpochChanges<B, Epoch>,
		genesis_config: SassafrasConfiguration,
	) -> Self {
		let client_weak = Arc::downgrade(&client);
		let on_finality = move |notification: &FinalityNotification<B>| {
			if let Some(client) = client_weak.upgrade() {
				aux_storage_cleanup(client.as_ref(), notification)
			} else {
				Default::default()
			}
		};
		client.register_finality_action(Box::new(on_finality));

		SassafrasBlockImport { inner, client, epoch_changes, genesis_config }
	}
}

struct RecoverableEpochChanges<B: BlockT> {
	old_epoch_changes: EpochChangesFor<B, Epoch>,
	weak_lock: sc_consensus::shared_data::SharedDataLockedUpgradable<EpochChangesFor<B, Epoch>>,
}

impl<B: BlockT> RecoverableEpochChanges<B> {
	fn rollback(mut self) {
		*self.weak_lock.upgrade() = self.old_epoch_changes;
	}
}

impl<B: BlockT, C, I> SassafrasBlockImport<B, C, I>
where
	C: AuxStore + HeaderBackend<B> + HeaderMetadata<B, Error = sp_blockchain::Error>,
{
	// The fork choice rule is that we pick the heaviest chain (i.e. more blocks built
	// using primary mechanism), if there's a tie we go with the longest chain.
	fn is_new_best(
		&self,
		curr_weight: u32,
		curr_number: NumberFor<B>,
		parent_hash: B::Hash,
	) -> Result<bool, ConsensusError> {
		let info = self.client.info();

		let new_best = if info.best_hash == parent_hash {
			true
		} else {
			let best_weight = aux_schema::load_block_weight(&*self.client, &info.best_hash)
				.map_err(|e| ConsensusError::ChainLookup(e.to_string()))?
				.ok_or_else(|| {
					ConsensusError::ChainLookup("No block weight for best header.".into())
				})?;
			curr_weight > best_weight ||
				(curr_weight == best_weight && curr_number > info.best_number)
		};

		Ok(new_best)
	}

	fn import_epoch(
		&mut self,
		viable_epoch_desc: ViableEpochDescriptor<B::Hash, NumberFor<B>, Epoch>,
		next_epoch_desc: NextEpochDescriptor,
		slot: Slot,
		number: NumberFor<B>,
		hash: B::Hash,
		parent_hash: B::Hash,
		verbose: bool,
		auxiliary: &mut Vec<(Vec<u8>, Option<Vec<u8>>)>,
	) -> Result<RecoverableEpochChanges<B>, ConsensusError> {
		let mut epoch_changes = self.epoch_changes.shared_data_locked();

		let log_level = if verbose { log::Level::Debug } else { log::Level::Info };

		let mut viable_epoch = epoch_changes
			.viable_epoch(&viable_epoch_desc, |slot| Epoch::genesis(&self.genesis_config, slot))
			.ok_or_else(|| {
				ConsensusError::ClientImport(Error::<B>::FetchEpoch(parent_hash).into())
			})?
			.into_cloned();

		if viable_epoch.as_ref().end_slot() <= slot {
			// Some epochs must have been skipped as our current slot fits outside the
			// current epoch. We will figure out which is the first skipped epoch and we
			// will partially re-use its data for this "recovery" epoch.
			let epoch_data = viable_epoch.as_mut();
			let skipped_epochs =
				(*slot - *epoch_data.start_slot) / epoch_data.config.epoch_duration;
			let original_epoch_idx = epoch_data.epoch_idx;

			// NOTE: notice that we are only updating a local copy of the `Epoch`, this
			// makes it so that when we insert the next epoch into `EpochChanges` below
			// (after incrementing it), it will use the correct epoch index and start slot.
			// We do not update the original epoch that may be reused because there may be
			// some other forks where the epoch isn't skipped.
			// Not updating the original epoch works because when we search the tree for
			// which epoch to use for a given slot, we will search in-depth with the
			// predicate `epoch.start_slot <= slot` which will still match correctly without
			// requiring to update `start_slot` to the correct value.
			epoch_data.epoch_idx += skipped_epochs;
			epoch_data.start_slot = Slot::from(
				*epoch_data.start_slot + skipped_epochs * epoch_data.config.epoch_duration,
			);
			log::warn!(
				target: "sassafras",
				"🌳 Epoch(s) skipped from {} to {}",
				 original_epoch_idx, epoch_data.epoch_idx
			);
		}

		log!(target: "sassafras",
			 log_level,
			 "🌳 🍁 New epoch {} launching at block {} (block slot {} >= start slot {}).",
			 viable_epoch.as_ref().epoch_idx,
			 hash,
			 slot,
			 viable_epoch.as_ref().start_slot,
		);

		let next_epoch = viable_epoch.increment(next_epoch_desc);

		log!(target: "sassafras",
			 log_level,
			 "🌳 🍁 Next epoch starts at slot {}",
			 next_epoch.as_ref().start_slot,
		);

		let old_epoch_changes = (*epoch_changes).clone();

		// Prune the tree of epochs not part of the finalized chain or
		// that are not live anymore, and then track the given epoch change
		// in the tree.
		// NOTE: it is important that these operations are done in this
		// order, otherwise if pruning after import the `is_descendent_of`
		// used by pruning may not know about the block that is being
		// imported.
		let prune_and_import = || {
			prune_finalized(self.client.clone(), &mut epoch_changes)?;

			epoch_changes
				.import(descendent_query(&*self.client), hash, number, parent_hash, next_epoch)
				.map_err(|e| {
					ConsensusError::ClientImport(format!("Error importing epoch changes: {}", e))
				})?;

			Ok(())
		};

		if let Err(e) = prune_and_import() {
			warn!(target: "sassafras", "🌳 Failed to launch next epoch: {}", e);
			*epoch_changes = old_epoch_changes;
			return Err(e)
		}

		aux_schema::write_epoch_changes::<B, _, _>(&*epoch_changes, |insert| {
			auxiliary.extend(insert.iter().map(|(k, v)| (k.to_vec(), Some(v.to_vec()))))
		});

		Ok(RecoverableEpochChanges { old_epoch_changes, weak_lock: epoch_changes.release_mutex() })
	}
}

impl<Block, Client, Inner> SassafrasBlockImport<Block, Client, Inner>
where
	Block: BlockT,
	Inner: BlockImport<Block, Transaction = sp_api::TransactionFor<Client, Block>> + Send + Sync,
	Inner::Error: Into<ConsensusError>,
	Client: HeaderBackend<Block>
		+ HeaderMetadata<Block, Error = sp_blockchain::Error>
		+ AuxStore
		+ ProvideRuntimeApi<Block>
		+ Send
		+ Sync,
	Client::Api: SassafrasApi<Block> + ApiExt<Block>,
{
	/// Import whole state after a warp sync.
	///
	/// This function makes multiple transactions to the DB. If one of them fails we may
	/// end up in an inconsistent state and have to resync
	async fn import_state(
		&mut self,
		mut block: BlockImportParams<Block, sp_api::TransactionFor<Client, Block>>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> Result<ImportResult, ConsensusError> {
		let hash = block.post_hash();
		let parent_hash = *block.header.parent_hash();
		let number = *block.header.number();

		// Check for the unit tag.
		block.remove_intermediate::<()>(INTERMEDIATE_KEY)?;

		// Import as best
		block.fork_choice = Some(ForkChoiceStrategy::Custom(true));

		// Reset block weight
		aux_schema::write_block_weight(hash, 0, |values| {
			block
				.auxiliary
				.extend(values.iter().map(|(k, v)| (k.to_vec(), Some(v.to_vec()))))
		});

		// First make the client import the state
		let aux = match self.inner.import_block(block, new_cache).await {
			Ok(ImportResult::Imported(aux)) => aux,
			Ok(r) =>
				return Err(ConsensusError::ClientImport(format!(
					"Unexpected import result: {:?}",
					r
				))),
			Err(e) => return Err(e.into()),
		};

		// Read epoch info from the imported state
		let block_id = BlockId::Hash(hash);
		let curr_epoch = self.client.runtime_api().current_epoch(&block_id).map_err(|e| {
			ConsensusError::ClientImport(sassafras_err::<Block>(Error::RuntimeApi(e)).into())
		})?;
		let next_epoch = self.client.runtime_api().next_epoch(&block_id).map_err(|e| {
			ConsensusError::ClientImport(sassafras_err::<Block>(Error::RuntimeApi(e)).into())
		})?;

		let mut epoch_changes = self.epoch_changes.shared_data();
		epoch_changes.reset(parent_hash, hash, number, curr_epoch.into(), next_epoch.into());

		aux_schema::write_epoch_changes::<Block, _, _>(&*epoch_changes, |insert| {
			self.client.insert_aux(insert, [])
		})
		.map_err(|e| ConsensusError::ClientImport(e.to_string()))?;

		Ok(ImportResult::Imported(aux))
	}
}

#[async_trait::async_trait]
impl<Block, Client, Inner> BlockImport<Block> for SassafrasBlockImport<Block, Client, Inner>
where
	Block: BlockT,
	Inner: BlockImport<Block, Transaction = sp_api::TransactionFor<Client, Block>> + Send + Sync,
	Inner::Error: Into<ConsensusError>,
	Client: HeaderBackend<Block>
		+ HeaderMetadata<Block, Error = sp_blockchain::Error>
		+ AuxStore
		+ ProvideRuntimeApi<Block>
		+ Send
		+ Sync,
	Client::Api: SassafrasApi<Block> + ApiExt<Block>,
{
	type Error = ConsensusError;
	type Transaction = sp_api::TransactionFor<Client, Block>;

	async fn import_block(
		&mut self,
		mut block: BlockImportParams<Block, Self::Transaction>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		let hash = block.post_hash();
		let number = *block.header.number();
		let info = self.client.info();

		let block_status = self
			.client
			.status(hash)
			.map_err(|e| ConsensusError::ClientImport(e.to_string()))?;

		// Skip protocol-specific logic if block already on-chain or importing blocks
		// during initial sync, otherwise the check for epoch changes will error
		// because trying to re-import an epoch change entry or because of missing epoch
		// data in the tree, respectivelly.
		if info.block_gap.map_or(false, |(s, e)| s <= number && number <= e) ||
			block_status == BlockStatus::InChain
		{
			// When re-importing existing block strip away intermediates.
			// In case of initial sync intermediates should not be present...
			let _ = block.remove_intermediate::<SassafrasIntermediate<Block>>(INTERMEDIATE_KEY);
			block.fork_choice = Some(ForkChoiceStrategy::Custom(false));
			return self.inner.import_block(block, new_cache).await.map_err(Into::into)
		}

		if block.with_state() {
			return self.import_state(block, new_cache).await
		}

		let viable_epoch_desc = block
			.remove_intermediate::<SassafrasIntermediate<Block>>(INTERMEDIATE_KEY)?
			.epoch_descriptor;

		let pre_digest = find_pre_digest::<Block>(&block.header)
			.expect("valid headers contain a pre-digest; header has been already verified; qed");
		let slot = pre_digest.slot;

		let parent_hash = *block.header.parent_hash();
		let parent_header = self
			.client
			.header(parent_hash)
			.map_err(|e| ConsensusError::ChainLookup(e.to_string()))?
			.ok_or_else(|| {
				ConsensusError::ChainLookup(
					sassafras_err(Error::<Block>::ParentUnavailable(parent_hash, hash)).into(),
				)
			})?;
		let parent_slot = find_pre_digest::<Block>(&parent_header)
			.map(|d| d.slot)
			.expect("parent is non-genesis; valid headers contain a pre-digest; header has been already verified; qed");

		// Make sure that slot number is strictly increasing
		if slot <= parent_slot {
			return Err(ConsensusError::ClientImport(
				sassafras_err(Error::<Block>::SlotMustIncrease(parent_slot, slot)).into(),
			))
		}

		// Check if there's any epoch change expected to happen at this slot.
		// `epoch` is the epoch to verify the block under, and `first_in_epoch` is true
		// if this is the first block in its chain for that epoch.

		let first_in_epoch = parent_slot < viable_epoch_desc.start_slot();

		let next_epoch_digest = find_next_epoch_digest::<Block>(&block.header)
			.map_err(|e| ConsensusError::ClientImport(e.to_string()))?;

		match (first_in_epoch, next_epoch_digest.is_some()) {
			(true, false) =>
				return Err(ConsensusError::ClientImport(
					sassafras_err(Error::<Block>::ExpectedEpochChange(hash, slot)).into(),
				)),
			(false, true) =>
				return Err(ConsensusError::ClientImport(
					sassafras_err(Error::<Block>::UnexpectedEpochChange).into(),
				)),
			_ => (),
		}

		// Compute the total weight of the chain, including the imported block.

		let parent_weight = aux_schema::load_block_weight(&*self.client, parent_hash)
			.map_err(|e| ConsensusError::ClientImport(e.to_string()))?
			.or_else(|| (*parent_header.number() == Zero::zero()).then(|| 0))
			.ok_or_else(|| {
				ConsensusError::ClientImport(
					sassafras_err(Error::<Block>::ParentBlockNoAssociatedWeight(hash)).into(),
				)
			})?;

		let total_weight = parent_weight + pre_digest.ticket_aux.is_some() as u32;

		aux_schema::write_block_weight(hash, total_weight, |values| {
			block
				.auxiliary
				.extend(values.iter().map(|(k, v)| (k.to_vec(), Some(v.to_vec()))))
		});

		// If there's a pending epoch we'll try to update all the involved data while
		// saving the previous epoch changes as well. In this way we can revert it if
		// there's any error.
		let epoch_changes_data = next_epoch_digest
			.map(|next_epoch_desc| {
				self.import_epoch(
					viable_epoch_desc,
					next_epoch_desc,
					slot,
					number,
					hash,
					parent_hash,
					block.origin != BlockOrigin::NetworkInitialSync,
					&mut block.auxiliary,
				)
			})
			.transpose()?;

		// The fork choice rule is intentionally changed within the context of the
		// epoch changes lock to avoid annoying race conditions on what is the current
		// best block. That is, the best may be changed by the inner block import.
		let is_new_best = self.is_new_best(total_weight, number, parent_hash)?;
		block.fork_choice = Some(ForkChoiceStrategy::Custom(is_new_best));

		let import_result = self.inner.import_block(block, new_cache).await;

		// Revert to the original epoch changes in case there's an error
		// importing the block
		// TODO-SASS-P3: shouldn't we check for Ok(Imported(_))?
		if import_result.is_err() {
			if let Some(data) = epoch_changes_data {
				data.rollback();
			}
		}

		import_result.map_err(Into::into)
	}

	async fn check_block(
		&mut self,
		block: BlockCheckParams<Block>,
	) -> Result<ImportResult, Self::Error> {
		self.inner.check_block(block).await.map_err(Into::into)
	}
}

/// Gets the best finalized block and its slot, and prunes the given epoch tree.
fn prune_finalized<C, B>(
	client: Arc<C>,
	epoch_changes: &mut EpochChangesFor<B, Epoch>,
) -> Result<(), ConsensusError>
where
	B: BlockT,
	C: HeaderBackend<B> + HeaderMetadata<B, Error = sp_blockchain::Error>,
{
	let info = client.info();

	let finalized_slot = {
		let finalized_header = client
			.header(info.finalized_hash)
			.map_err(|e| ConsensusError::ClientImport(e.to_string()))?
			.expect("finalized headers must exist in db; qed");

		find_pre_digest::<B>(&finalized_header)
			.expect("valid blocks have a pre-digest; qed")
			.slot
	};

	epoch_changes
		.prune_finalized(
			descendent_query(&*client),
			&info.finalized_hash,
			info.finalized_number,
			finalized_slot,
		)
		.map_err(|e| ConsensusError::ClientImport(e.to_string()))?;

	Ok(())
}

/// Produce a Sassafras block-import object to be used later on in the construction of
/// an import-queue.
///
/// Also returns a link object used to correctly instantiate the import queue
/// and authoring worker.
pub fn block_import<C, B: BlockT, I>(
	genesis_config: SassafrasConfiguration,
	inner_block_import: I,
	client: Arc<C>,
) -> ClientResult<(SassafrasBlockImport<B, C, I>, SassafrasLink<B>)>
where
	C: AuxStore
		+ HeaderBackend<B>
		+ HeaderMetadata<B, Error = sp_blockchain::Error>
		+ PreCommitActions<B>
		+ 'static,
{
	let epoch_changes = aux_schema::load_epoch_changes::<B, _>(&*client)?;

	prune_finalized(client.clone(), &mut epoch_changes.shared_data())?;

	let link = SassafrasLink {
		epoch_changes: epoch_changes.clone(),
		genesis_config: genesis_config.clone(),
	};

	let block_import =
		SassafrasBlockImport::new(inner_block_import, client, epoch_changes, genesis_config);

	Ok((block_import, link))
}
