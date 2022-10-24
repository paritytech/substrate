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

/// A block-import handler for Sassafras.
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

impl<B: BlockT, C, I> SassafrasBlockImport<B, C, I> {
	/// Constructor.
	pub fn new(
		inner: I,
		client: Arc<C>,
		epoch_changes: SharedEpochChanges<B, Epoch>,
		genesis_config: SassafrasConfiguration,
	) -> Self {
		SassafrasBlockImport { inner, client, epoch_changes, genesis_config }
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

		let pre_digest = find_pre_digest::<Block>(&block.header).expect(
			"valid sassafras headers must contain a predigest; header has been already verified; qed",
		);
		let slot = pre_digest.slot;

		let parent_hash = *block.header.parent_hash();
		let parent_header = self
			.client
			.header(BlockId::Hash(parent_hash))
			.map_err(|e| ConsensusError::ChainLookup(e.to_string()))?
			.ok_or_else(|| {
				ConsensusError::ChainLookup(
					sassafras_err(Error::<Block>::ParentUnavailable(parent_hash, hash)).into(),
				)
			})?;

		let parent_slot = find_pre_digest::<Block>(&parent_header).map(|d| d.slot).expect(
			"parent is non-genesis; valid Sassafras headers contain a pre-digest; \
             header has already been verified; qed",
		);

		// Make sure that slot number is strictly increasing
		if slot <= parent_slot {
			return Err(ConsensusError::ClientImport(
				sassafras_err(Error::<Block>::SlotMustIncrease(parent_slot, slot)).into(),
			))
		}

		// If there's a pending epoch we'll save the previous epoch changes here
		// this way we can revert it if there's any error
		let mut old_epoch_changes = None;

		// Use an extra scope to make the compiler happy, because otherwise he complains about the
		// mutex, even if we dropped it...
		let mut epoch_changes = {
			let mut epoch_changes = self.epoch_changes.shared_data_locked();

			// Check if there's any epoch change expected to happen at this slot.
			// `epoch` is the epoch to verify the block under, and `first_in_epoch` is true
			// if this is the first block in its chain for that epoch.
			//
			// also provides the total weight of the chain, including the imported block.
			let parent_weight = if *parent_header.number() == Zero::zero() {
				0
			} else {
				aux_schema::load_block_weight(&*self.client, parent_hash)
					.map_err(|e| ConsensusError::ClientImport(e.to_string()))?
					.ok_or_else(|| {
						ConsensusError::ClientImport(
							sassafras_err(Error::<Block>::ParentBlockNoAssociatedWeight(hash))
								.into(),
						)
					})?
			};

			let intermediate =
				block.remove_intermediate::<SassafrasIntermediate<Block>>(INTERMEDIATE_KEY)?;

			let epoch_descriptor = intermediate.epoch_descriptor;
			let first_in_epoch = parent_slot < epoch_descriptor.start_slot();

			let total_weight = parent_weight + pre_digest.ticket_aux.is_some() as u32;

			// Search for this all the time so we can reject unexpected announcements.
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

			if let Some(next_epoch_descriptor) = next_epoch_digest {
				old_epoch_changes = Some((*epoch_changes).clone());

				let mut viable_epoch = epoch_changes
					.viable_epoch(&epoch_descriptor, |slot| {
						Epoch::genesis(&self.genesis_config, slot)
					})
					.ok_or_else(|| {
						ConsensusError::ClientImport(Error::<Block>::FetchEpoch(parent_hash).into())
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

				// Restrict info logging during initial sync to avoid spam
				let log_level = match block.origin {
					BlockOrigin::NetworkInitialSync => log::Level::Debug,
					_ => log::Level::Info,
				};

				log!(target: "sassafras",
					 log_level,
					 "🌳 🍁 New epoch {} launching at block {} (block slot {} >= start slot {}).",
					 viable_epoch.as_ref().epoch_idx,
					 hash,
					 slot,
					 viable_epoch.as_ref().start_slot,
				);

				let next_epoch = viable_epoch.increment(next_epoch_descriptor);

				log!(target: "sassafras",
					 log_level,
					 "🌳 🍁 Next epoch starts at slot {}",
					 next_epoch.as_ref().start_slot,
				);

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
						.import(
							descendent_query(&*self.client),
							hash,
							number,
							*block.header.parent_hash(),
							next_epoch,
						)
						.map_err(|e| {
							ConsensusError::ClientImport(format!(
								"Error importing epoch changes: {}",
								e
							))
						})?;

					Ok(())
				};

				if let Err(e) = prune_and_import() {
					debug!(target: "sassafras", "🌳 Failed to launch next epoch: {}", e);
					*epoch_changes =
						old_epoch_changes.expect("set `Some` above and not taken; qed");
					return Err(e)
				}

				aux_schema::write_epoch_changes::<Block, _, _>(&*epoch_changes, |insert| {
					block
						.auxiliary
						.extend(insert.iter().map(|(k, v)| (k.to_vec(), Some(v.to_vec()))))
				});
			}

			aux_schema::write_block_weight(hash, total_weight, |values| {
				block
					.auxiliary
					.extend(values.iter().map(|(k, v)| (k.to_vec(), Some(v.to_vec()))))
			});

			// The fork choice rule is that we pick the heaviest chain (i.e. more blocks built
			// using primary mechanism), if there's a tie we go with the longest chain.
			block.fork_choice = {
				let info = self.client.info();
				let best_weight = if &info.best_hash == block.header.parent_hash() {
					// the parent=genesis case is already covered for loading parent weight,
					// so we don't need to cover again here.
					parent_weight
				} else {
					aux_schema::load_block_weight(&*self.client, &info.best_hash)
						.map_err(|e| ConsensusError::ChainLookup(e.to_string()))?
						.ok_or_else(|| {
							ConsensusError::ChainLookup(
								"No block weight for parent header.".to_string(),
							)
						})?
				};

				let is_new_best = total_weight > best_weight ||
					(total_weight == best_weight && number > info.best_number);
				Some(ForkChoiceStrategy::Custom(is_new_best))
			};
			// Release the mutex, but it stays locked
			epoch_changes.release_mutex()
		};

		let import_result = self.inner.import_block(block, new_cache).await;

		// Revert to the original epoch changes in case there's an error
		// importing the block
		if import_result.is_err() {
			if let Some(old_epoch_changes) = old_epoch_changes {
				*epoch_changes.upgrade() = old_epoch_changes;
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
	if info.block_gap.is_none() {
		epoch_changes.clear_gap();
	}

	let finalized_slot = {
		let finalized_header = client
			.header(BlockId::Hash(info.finalized_hash))
			.map_err(|e| ConsensusError::ClientImport(e.to_string()))?
			.expect(
				"best finalized hash was given by client; finalized headers must exist in db; qed",
			);

		find_pre_digest::<B>(&finalized_header)
			.expect("finalized header must be valid; valid blocks have a pre-digest; qed")
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
	C: AuxStore + HeaderBackend<B> + HeaderMetadata<B, Error = sp_blockchain::Error> + 'static,
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
