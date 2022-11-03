// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

extern crate core;

mod canon_engine;
#[cfg(test)]
pub mod test_utils;

use std::{marker::PhantomData, sync::Arc};

use futures::StreamExt;
use log::{debug, error, trace, warn};

use sc_client_api::{Backend, BlockchainEvents, FinalityNotification, FinalityNotifications};
use sc_offchain::OffchainDb;
use sp_api::ProvideRuntimeApi;
use sp_blockchain::{HeaderBackend, HeaderMetadata};
use sp_mmr_primitives::{utils, LeafIndex, MmrApi};
use sp_runtime::{
	generic::BlockId,
	traits::{Block, Header, NumberFor, Zero},
};

use crate::canon_engine::CanonEngine;
use beefy_primitives::MmrRootHash;

pub const LOG_TARGET: &str = "mmr";

enum MaybeCanonEngine<B: Block, C, S> {
	Uninitialized { client: Arc<C>, offchain_db: OffchainDb<S>, indexing_prefix: Vec<u8> },
	Initialized(CanonEngine<C, B, S>),
}

impl<B, C, S> MaybeCanonEngine<B, C, S>
where
	B: Block,
	C: ProvideRuntimeApi<B>,
	C::Api: MmrApi<B, MmrRootHash, NumberFor<B>>,
{
	fn try_prepare_init(
		&mut self,
		notification: &FinalityNotification<B>,
	) -> Option<<B::Header as Header>::Number> {
		if let MaybeCanonEngine::Uninitialized { client, .. } = self {
			let best_block = *notification.header.number();
			return match client.runtime_api().num_mmr_blocks(&BlockId::number(best_block)) {
				Ok(Ok(num_mmr_blocks)) => {
					match utils::first_mmr_block_num::<B::Header>(best_block, num_mmr_blocks) {
						Ok(first_mmr_block) => Some(first_mmr_block),
						Err(e) => {
							error!(
								target: LOG_TARGET,
								"Error calculating the first mmr block: {:?}", e
							);
							return None
						},
					}
				},
				_ => {
					trace!(target: LOG_TARGET, "Finality notification: {:?}", notification);
					debug!(target: LOG_TARGET, "Waiting for MMR pallet to become available ...");

					None
				},
			}
		}

		None
	}

	fn try_init(self, first_mmr_block: <B::Header as Header>::Number) -> Self {
		if let MaybeCanonEngine::Uninitialized { client, offchain_db, indexing_prefix } = self {
			debug!(
				target: LOG_TARGET,
				"MMR pallet available since block {:?}. \
				Starting offchain MMR leafs canonicalization.",
				first_mmr_block
			);

			return MaybeCanonEngine::Initialized(CanonEngine {
				client,
				offchain_db,
				indexing_prefix,
				first_mmr_block,
				_phantom: Default::default(),
			})
		}

		return self
	}
}

/// A MMR Gadget.
pub struct MmrGadget<B: Block, BE: Backend<B>, C> {
	finality_notifications: FinalityNotifications<B>,
	best_finalized_head: (<B::Header as Header>::Number, B::Hash),
	maybe_engine: MaybeCanonEngine<B, C, BE::OffchainStorage>,

	_phantom: PhantomData<(B, BE)>,
}

impl<B, BE, C> MmrGadget<B, BE, C>
where
	B: Block,
	<B::Header as Header>::Number: Into<LeafIndex>,
	BE: Backend<B>,
	C: BlockchainEvents<B> + HeaderBackend<B> + HeaderMetadata<B> + ProvideRuntimeApi<B>,
	C::Api: MmrApi<B, MmrRootHash, NumberFor<B>>,
{
	fn new(client: Arc<C>, backend: Arc<BE>, indexing_prefix: Vec<u8>) -> Option<Self> {
		let offchain_db = match backend.offchain_storage() {
			Some(offchain_storage) => OffchainDb::new(offchain_storage),
			None => {
				warn!(
					target: LOG_TARGET,
					"Can't spawn a MmrGadget for a node without offchain storage."
				);
				return None
			},
		};

		Some(MmrGadget {
			finality_notifications: client.finality_notification_stream(),
			best_finalized_head: (Zero::zero(), client.info().genesis_hash),
			maybe_engine: MaybeCanonEngine::Uninitialized { client, offchain_db, indexing_prefix },

			_phantom: Default::default(),
		})
	}

	async fn run(mut self) {
		while let Some(notification) = self.finality_notifications.next().await {
			// Initialize the canonicalization engine if the MMR pallet is available.
			if let Some(first_mmr_block) = self.maybe_engine.try_prepare_init(&notification) {
				self.maybe_engine = self.maybe_engine.try_init(first_mmr_block);
			}

			if let MaybeCanonEngine::Initialized(engine) = &mut self.maybe_engine {
				// Perform the actual logic.
				engine.canonicalize_and_prune(&self.best_finalized_head, &notification);
			}

			self.best_finalized_head = (*notification.header.number(), notification.hash);
		}
	}

	/// Create and run the MMR gadget.
	pub async fn start(client: Arc<C>, backend: Arc<BE>, indexing_prefix: Vec<u8>) {
		if let Some(mmr_gadget) = Self::new(client, backend, indexing_prefix) {
			mmr_gadget.run().await
		}
	}
}

#[cfg(test)]
mod tests {
	use crate::test_utils::run_test_with_mmr_gadget;
	use sp_runtime::generic::BlockId;
	use std::time::Duration;

	#[test]
	fn mmr_first_block_is_computed_correctly() {
		// Check the case where the first block is also the first block with MMR.
		run_test_with_mmr_gadget(|client| async move {
			// G -> A1 -> A2
			//      |
			//      | -> first mmr block

			let a1 = client.import_block(&BlockId::Number(0), b"a1", Some(0)).await;
			let a2 = client.import_block(&BlockId::Hash(a1.hash()), b"a2", Some(1)).await;

			client.finalize_block(a1.hash(), Some(1));
			async_std::task::sleep(Duration::from_millis(200)).await;
			// expected finalized heads: a1
			client.assert_canonicalized(&[&a1]);
			client.assert_not_pruned(&[&a2]);
		});

		// Check the case where the first block with MMR comes later.
		run_test_with_mmr_gadget(|client| async move {
			// G -> A1 -> A2 -> A3 -> A4 -> A5 -> A6
			//                        |
			//                        | -> first mmr block

			let a1 = client.import_block(&BlockId::Number(0), b"a1", None).await;
			let a2 = client.import_block(&BlockId::Hash(a1.hash()), b"a2", None).await;
			let a3 = client.import_block(&BlockId::Hash(a2.hash()), b"a3", None).await;
			let a4 = client.import_block(&BlockId::Hash(a3.hash()), b"a4", Some(0)).await;
			let a5 = client.import_block(&BlockId::Hash(a4.hash()), b"a5", Some(1)).await;
			let a6 = client.import_block(&BlockId::Hash(a5.hash()), b"a6", Some(2)).await;

			client.finalize_block(a5.hash(), Some(2));
			async_std::task::sleep(Duration::from_millis(200)).await;
			// expected finalized heads: a4, a5
			client.assert_canonicalized(&[&a4, &a5]);
			client.assert_not_pruned(&[&a6]);
		});
	}

	#[test]
	fn does_not_panic_on_invalid_num_mmr_blocks() {
		run_test_with_mmr_gadget(|client| async move {
			// G -> A1
			//      |
			//      | -> first mmr block

			let a1 = client.import_block(&BlockId::Number(0), b"a1", Some(0)).await;

			// Simulate the case where the runtime says that there are 2 mmr_blocks when in fact
			// there is only 1.
			client.finalize_block(a1.hash(), Some(2));
			async_std::task::sleep(Duration::from_millis(200)).await;
			// expected finalized heads: -
			client.assert_not_canonicalized(&[&a1]);
		});
	}
}
