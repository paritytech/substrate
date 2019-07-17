// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
use futures::{prelude::*, future::Executor, sync::mpsc};
use runtime_primitives::{Justification, traits::{Block as BlockT, Header as HeaderT, NumberFor}};

use crate::error::Error as ConsensusError;
use crate::block_import::{BlockImport, BlockOrigin};
use crate::import_queue::{
	BlockImportResult, BlockImportError, Verifier, BoxBlockImport, BoxFinalityProofImport,
	BoxJustificationImport, ImportQueue, Link, Origin,
	IncomingBlock, import_single_block,
	buffered_link::{self, BufferedLinkSender, BufferedLinkReceiver}
};

/// Interface to a basic block import queue that is importing blocks sequentially in a separate
/// task, with pluggable verification.
pub struct BasicQueue<B: BlockT> {
	/// Channel to send messages to the background task.
	sender: mpsc::UnboundedSender<ToWorkerMsg<B>>,
	/// Results coming from the worker task.
	result_port: BufferedLinkReceiver<B>,
	/// Since we have to be in a tokio context in order to spawn background tasks, we first store
	/// the task to spawn here, then extract it as soon as we are in a tokio context.
	/// If `Some`, contains the task to spawn in the background. If `None`, the future has already
	/// been spawned.
	future_to_spawn: Option<Box<dyn Future<Item = (), Error = ()> + Send>>,
	/// If it isn't possible to spawn the future in `future_to_spawn` (which is notably the case in
	/// "no std" environment), we instead put it in `manual_poll`. It is then polled manually from
	/// `poll_actions`.
	manual_poll: Option<Box<dyn Future<Item = (), Error = ()> + Send>>,
}

impl<B: BlockT> BasicQueue<B> {
	/// Instantiate a new basic queue, with given verifier.
	///
	/// This creates a background task, and calls `on_start` on the justification importer and
	/// finality proof importer.
	pub fn new<V: 'static + Verifier<B>>(
		verifier: Arc<V>,
		block_import: BoxBlockImport<B>,
		justification_import: Option<BoxJustificationImport<B>>,
		finality_proof_import: Option<BoxFinalityProofImport<B>>,
	) -> Self {
		let (result_sender, result_port) = buffered_link::buffered_link();
		let (future, worker_sender) = BlockImportWorker::new(
			result_sender,
			verifier,
			block_import,
			justification_import,
			finality_proof_import,
		);

		Self {
			sender: worker_sender,
			result_port,
			future_to_spawn: Some(Box::new(future)),
			manual_poll: None,
		}
	}
}

impl<B: BlockT> ImportQueue<B> for BasicQueue<B> {
	fn import_blocks(&mut self, origin: BlockOrigin, blocks: Vec<IncomingBlock<B>>) {
		if blocks.is_empty() {
			return;
		}

		trace!(target: "sync", "Scheduling {} blocks for import", blocks.len());
		let _ = self.sender.unbounded_send(ToWorkerMsg::ImportBlocks(origin, blocks));
	}

	fn import_justification(
		&mut self,
		who: Origin,
		hash: B::Hash,
		number: NumberFor<B>,
		justification: Justification
	) {
		let _ = self.sender.unbounded_send(ToWorkerMsg::ImportJustification(who.clone(), hash, number, justification));
	}

	fn import_finality_proof(&mut self, who: Origin, hash: B::Hash, number: NumberFor<B>, finality_proof: Vec<u8>) {
		trace!(target: "sync", "Scheduling finality proof of {}/{} for import", number, hash);
		let _ = self.sender.unbounded_send(ToWorkerMsg::ImportFinalityProof(who, hash, number, finality_proof));
	}

	fn poll_actions(&mut self, link: &mut dyn Link<B>) {
		// Try to spawn the future in `future_to_spawn`.
		if let Some(future) = self.future_to_spawn.take() {
			if let Err(err) = tokio_executor::DefaultExecutor::current().execute(future) {
				debug_assert!(self.manual_poll.is_none());
				self.manual_poll = Some(err.into_future());
			}
		}

		// As a backup mechanism, if we failed to spawn the `future_to_spawn`, we instead poll
		// manually here.
		if let Some(manual_poll) = self.manual_poll.as_mut() {
			match manual_poll.poll() {
				Ok(Async::NotReady) => {}
				_ => self.manual_poll = None,
			}
		}

		self.result_port.poll_actions(link);
	}
}

/// Message destinated to the background worker.
#[derive(Debug)]
enum ToWorkerMsg<B: BlockT> {
	ImportBlocks(BlockOrigin, Vec<IncomingBlock<B>>),
	ImportJustification(Origin, B::Hash, NumberFor<B>, Justification),
	ImportFinalityProof(Origin, B::Hash, NumberFor<B>, Vec<u8>),
}

struct BlockImportWorker<B: BlockT, V: Verifier<B>> {
	result_sender: BufferedLinkSender<B>,
	block_import: BoxBlockImport<B>,
	justification_import: Option<BoxJustificationImport<B>>,
	finality_proof_import: Option<BoxFinalityProofImport<B>>,
	verifier: Arc<V>,
}

impl<B: BlockT, V: 'static + Verifier<B>> BlockImportWorker<B, V> {
	fn new(
		result_sender: BufferedLinkSender<B>,
		verifier: Arc<V>,
		block_import: BoxBlockImport<B>,
		justification_import: Option<BoxJustificationImport<B>>,
		finality_proof_import: Option<BoxFinalityProofImport<B>>,
	) -> (impl Future<Item = (), Error = ()> + Send, mpsc::UnboundedSender<ToWorkerMsg<B>>) {
		let (sender, mut port) = mpsc::unbounded();

		let mut worker = BlockImportWorker {
			result_sender,
			verifier,
			justification_import,
			block_import,
			finality_proof_import,
		};

		if let Some(justification_import) = worker.justification_import.as_mut() {
			for (hash, number) in justification_import.on_start() {
				worker.result_sender.request_justification(&hash, number);
			}
		}

		if let Some(finality_proof_import) = worker.finality_proof_import.as_mut() {
			for (hash, number) in finality_proof_import.on_start() {
				worker.result_sender.request_finality_proof(&hash, number);
			}
		}

		let future = futures::future::poll_fn(move || {
			loop {
				let msg = match port.poll() {
					Ok(Async::Ready(Some(msg))) => msg,
					Err(_) | Ok(Async::Ready(None)) => return Ok(Async::Ready(())),
					Ok(Async::NotReady) => return Ok(Async::NotReady),
				};

				match msg {
					ToWorkerMsg::ImportBlocks(origin, blocks) => {
						worker.import_a_batch_of_blocks(origin, blocks);
					},
					ToWorkerMsg::ImportFinalityProof(who, hash, number, proof) => {
						worker.import_finality_proof(who, hash, number, proof);
					},
					ToWorkerMsg::ImportJustification(who, hash, number, justification) => {
						worker.import_justification(who, hash, number, justification);
					}
				}
			}
		});

		(future, sender)
	}

	fn import_a_batch_of_blocks(&mut self, origin: BlockOrigin, blocks: Vec<IncomingBlock<B>>) {
		let result_sender = &self.result_sender;
		let (imported, count, results) = import_many_blocks(
			&mut *self.block_import,
			origin,
			blocks,
			self.verifier.clone(),
			|| !result_sender.is_closed(),
		);

		self.result_sender.blocks_processed(imported, count, results);
	}

	fn import_finality_proof(&mut self, who: Origin, hash: B::Hash, number: NumberFor<B>, finality_proof: Vec<u8>) {
		let verifier = &*self.verifier;
		let result = self.finality_proof_import.as_mut().map(|finality_proof_import| {
			finality_proof_import.import_finality_proof(hash, number, finality_proof, verifier)
				.map_err(|e| {
					debug!(
						"Finality proof import failed with {:?} for hash: {:?} number: {:?} coming from node: {:?}",
						e,
						hash,
						number,
						who,
					);
				})
		}).unwrap_or(Err(()));

		trace!(target: "sync", "Imported finality proof for {}/{}", number, hash);
		self.result_sender.finality_proof_imported(who, (hash, number), result);
	}

	fn import_justification(
		&mut self,
		who: Origin,
		hash: B::Hash,
		number: NumberFor<B>,
		justification: Justification
	) {
		let success = self.justification_import.as_mut().map(|justification_import| {
			justification_import.import_justification(hash, number, justification)
				.map_err(|e| {
					debug!(
						target: "sync",
						"Justification import failed with {:?} for hash: {:?} number: {:?} coming from node: {:?}",
						e,
						hash,
						number,
						who,
					);
					e
				}).is_ok()
		}).unwrap_or(false);

		self.result_sender.justification_imported(who, &hash, number, success);
	}
}

/// Import several blocks at once, returning import result for each block.
///
/// The `keep_going` closure will be called regularly. If it returns false, then the function will
/// end prematurely.
fn import_many_blocks<B: BlockT, V: Verifier<B>>(
	import_handle: &mut dyn BlockImport<B, Error = ConsensusError>,
	blocks_origin: BlockOrigin,
	blocks: Vec<IncomingBlock<B>>,
	verifier: Arc<V>,
	keep_going: impl Fn() -> bool,
) -> (usize, usize, Vec<(
	Result<BlockImportResult<NumberFor<B>>, BlockImportError>,
	B::Hash,
)>) {
	let count = blocks.len();
	let mut imported = 0;

	let blocks_range = match (
		blocks.first().and_then(|b| b.header.as_ref().map(|h| h.number())),
		blocks.last().and_then(|b| b.header.as_ref().map(|h| h.number())),
	) {
		(Some(first), Some(last)) if first != last => format!(" ({}..{})", first, last),
		(Some(first), Some(_)) => format!(" ({})", first),
		_ => Default::default(),
	};

	trace!(target: "sync", "Starting import of {} blocks {}", count, blocks_range);

	let mut results = vec![];

	let mut has_error = false;

	// Blocks in the response/drain should be in ascending order.
	for block in blocks {
		if !keep_going() {
			// Setting `has_error` to true cancels the rest of the import.
			has_error = true;
		}

		let block_number = block.header.as_ref().map(|h| h.number().clone());
		let block_hash = block.hash;
		let import_result = if has_error {
			Err(BlockImportError::Cancelled)
		} else {
			import_single_block(
				import_handle,
				blocks_origin.clone(),
				block,
				verifier.clone(),
			)
		};
		let was_ok = import_result.is_ok();
		if was_ok {
			trace!(target: "sync", "Block imported successfully {:?} ({})", block_number, block_hash);
			imported += 1;
		} else {
			has_error = true;
		}
		results.push((import_result, block_hash));
	}

	(imported, count, results)
}
