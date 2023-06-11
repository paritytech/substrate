// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use futures::{
	prelude::*,
	task::{Context, Poll},
};
use futures_timer::Delay;
use log::*;
use parking_lot::Mutex;
use sc_client_api::ImportNotifications;
use sc_consensus::{BlockImportParams, BoxBlockImport, StateAction, StorageChanges};
use sp_consensus::{BlockOrigin, Proposal};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header as HeaderT},
	DigestItem,
};
use std::{
	pin::Pin,
	sync::{
		atomic::{AtomicUsize, Ordering},
		Arc,
	},
	time::Duration,
};

use crate::{PowAlgorithm, PowIntermediate, Seal, INTERMEDIATE_KEY, LOG_TARGET, POW_ENGINE_ID};

/// Mining metadata. This is the information needed to start an actual mining loop.
#[derive(Clone, Eq, PartialEq)]
pub struct MiningMetadata<H, D> {
	/// Currently known best hash which the pre-hash is built on.
	pub best_hash: H,
	/// Mining pre-hash.
	pub pre_hash: H,
	/// Pre-runtime digest item.
	pub pre_runtime: Option<Vec<u8>>,
	/// Mining target difficulty.
	pub difficulty: D,
}

/// A build of mining, containing the metadata and the block proposal.
pub struct MiningBuild<
	Block: BlockT,
	Algorithm: PowAlgorithm<Block>,
	C: sp_api::ProvideRuntimeApi<Block>,
	Proof,
> {
	/// Mining metadata.
	pub metadata: MiningMetadata<Block::Hash, Algorithm::Difficulty>,
	/// Mining proposal.
	pub proposal: Proposal<Block, sp_api::TransactionFor<C, Block>, Proof>,
}

/// Version of the mining worker.
#[derive(Eq, PartialEq, Clone, Copy)]
pub struct Version(usize);

/// Mining worker that exposes structs to query the current mining build and submit mined blocks.
pub struct MiningHandle<
	Block: BlockT,
	Algorithm: PowAlgorithm<Block>,
	C: sp_api::ProvideRuntimeApi<Block>,
	L: sc_consensus::JustificationSyncLink<Block>,
	Proof,
> {
	version: Arc<AtomicUsize>,
	algorithm: Arc<Algorithm>,
	justification_sync_link: Arc<L>,
	build: Arc<Mutex<Option<MiningBuild<Block, Algorithm, C, Proof>>>>,
	block_import: Arc<Mutex<BoxBlockImport<Block, sp_api::TransactionFor<C, Block>>>>,
}

impl<Block, Algorithm, C, L, Proof> MiningHandle<Block, Algorithm, C, L, Proof>
where
	Block: BlockT,
	C: sp_api::ProvideRuntimeApi<Block>,
	Algorithm: PowAlgorithm<Block>,
	Algorithm::Difficulty: 'static + Send,
	L: sc_consensus::JustificationSyncLink<Block>,
	sp_api::TransactionFor<C, Block>: Send + 'static,
{
	fn increment_version(&self) {
		self.version.fetch_add(1, Ordering::SeqCst);
	}

	pub(crate) fn new(
		algorithm: Algorithm,
		block_import: BoxBlockImport<Block, sp_api::TransactionFor<C, Block>>,
		justification_sync_link: L,
	) -> Self {
		Self {
			version: Arc::new(AtomicUsize::new(0)),
			algorithm: Arc::new(algorithm),
			justification_sync_link: Arc::new(justification_sync_link),
			build: Arc::new(Mutex::new(None)),
			block_import: Arc::new(Mutex::new(block_import)),
		}
	}

	pub(crate) fn on_major_syncing(&self) {
		let mut build = self.build.lock();
		*build = None;
		self.increment_version();
	}

	pub(crate) fn on_build(&self, value: MiningBuild<Block, Algorithm, C, Proof>) {
		let mut build = self.build.lock();
		*build = Some(value);
		self.increment_version();
	}

	/// Get the version of the mining worker.
	///
	/// This returns type `Version` which can only compare equality. If `Version` is unchanged, then
	/// it can be certain that `best_hash` and `metadata` were not changed.
	pub fn version(&self) -> Version {
		Version(self.version.load(Ordering::SeqCst))
	}

	/// Get the current best hash. `None` if the worker has just started or the client is doing
	/// major syncing.
	pub fn best_hash(&self) -> Option<Block::Hash> {
		self.build.lock().as_ref().map(|b| b.metadata.best_hash)
	}

	/// Get a copy of the current mining metadata, if available.
	pub fn metadata(&self) -> Option<MiningMetadata<Block::Hash, Algorithm::Difficulty>> {
		self.build.lock().as_ref().map(|b| b.metadata.clone())
	}

	/// Submit a mined seal. The seal will be validated again. Returns true if the submission is
	/// successful.
	pub async fn submit(&self, seal: Seal) -> bool {
		if let Some(metadata) = self.metadata() {
			match self.algorithm.verify(
				&BlockId::Hash(metadata.best_hash),
				&metadata.pre_hash,
				metadata.pre_runtime.as_ref().map(|v| &v[..]),
				&seal,
				metadata.difficulty,
			) {
				Ok(true) => (),
				Ok(false) => {
					warn!(target: LOG_TARGET, "Unable to import mined block: seal is invalid",);
					return false
				},
				Err(err) => {
					warn!(target: LOG_TARGET, "Unable to import mined block: {}", err,);
					return false
				},
			}
		} else {
			warn!(target: LOG_TARGET, "Unable to import mined block: metadata does not exist",);
			return false
		}

		let build = if let Some(build) = {
			let mut build = self.build.lock();
			let value = build.take();
			if value.is_some() {
				self.increment_version();
			}
			value
		} {
			build
		} else {
			warn!(target: LOG_TARGET, "Unable to import mined block: build does not exist",);
			return false
		};

		let seal = DigestItem::Seal(POW_ENGINE_ID, seal);
		let (header, body) = build.proposal.block.deconstruct();

		let mut import_block = BlockImportParams::new(BlockOrigin::Own, header);
		import_block.post_digests.push(seal);
		import_block.body = Some(body);
		import_block.state_action =
			StateAction::ApplyChanges(StorageChanges::Changes(build.proposal.storage_changes));

		let intermediate = PowIntermediate::<Algorithm::Difficulty> {
			difficulty: Some(build.metadata.difficulty),
		};
		import_block.insert_intermediate(INTERMEDIATE_KEY, intermediate);

		let header = import_block.post_header();
		let mut block_import = self.block_import.lock();

		match block_import.import_block(import_block).await {
			Ok(res) => {
				res.handle_justification(
					&header.hash(),
					*header.number(),
					&self.justification_sync_link,
				);

				info!(
					target: LOG_TARGET,
					"✅ Successfully mined block on top of: {}", build.metadata.best_hash
				);
				true
			},
			Err(err) => {
				warn!(target: LOG_TARGET, "Unable to import mined block: {}", err,);
				false
			},
		}
	}
}

impl<Block, Algorithm, C, L, Proof> Clone for MiningHandle<Block, Algorithm, C, L, Proof>
where
	Block: BlockT,
	Algorithm: PowAlgorithm<Block>,
	C: sp_api::ProvideRuntimeApi<Block>,
	L: sc_consensus::JustificationSyncLink<Block>,
{
	fn clone(&self) -> Self {
		Self {
			version: self.version.clone(),
			algorithm: self.algorithm.clone(),
			justification_sync_link: self.justification_sync_link.clone(),
			build: self.build.clone(),
			block_import: self.block_import.clone(),
		}
	}
}

/// A stream that waits for a block import or timeout.
pub struct UntilImportedOrTimeout<Block: BlockT> {
	import_notifications: ImportNotifications<Block>,
	timeout: Duration,
	inner_delay: Option<Delay>,
}

impl<Block: BlockT> UntilImportedOrTimeout<Block> {
	/// Create a new stream using the given import notification and timeout duration.
	pub fn new(import_notifications: ImportNotifications<Block>, timeout: Duration) -> Self {
		Self { import_notifications, timeout, inner_delay: None }
	}
}

impl<Block: BlockT> Stream for UntilImportedOrTimeout<Block> {
	type Item = ();

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<()>> {
		let mut fire = false;

		loop {
			match Stream::poll_next(Pin::new(&mut self.import_notifications), cx) {
				Poll::Pending => break,
				Poll::Ready(Some(_)) => {
					fire = true;
				},
				Poll::Ready(None) => return Poll::Ready(None),
			}
		}

		let timeout = self.timeout;
		let inner_delay = self.inner_delay.get_or_insert_with(|| Delay::new(timeout));

		match Future::poll(Pin::new(inner_delay), cx) {
			Poll::Pending => (),
			Poll::Ready(()) => {
				fire = true;
			},
		}

		if fire {
			self.inner_delay = None;
			Poll::Ready(Some(()))
		} else {
			Poll::Pending
		}
	}
}
