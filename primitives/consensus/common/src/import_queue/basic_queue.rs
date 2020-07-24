// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::{mem, pin::Pin, time::Duration, marker::PhantomData};
use futures::{prelude::*, task::Context, task::Poll};
use futures_timer::Delay;
use sp_runtime::{Justification, traits::{Block as BlockT, Header as HeaderT, NumberFor}};
use sp_utils::mpsc::{TracingUnboundedSender, tracing_unbounded};
use prometheus_endpoint::Registry;

use crate::{
	block_import::BlockOrigin,
	import_queue::{
		BlockImportResult, BlockImportError, Verifier, BoxBlockImport, BoxFinalityProofImport,
		BoxJustificationImport, ImportQueue, Link, Origin,
		IncomingBlock, import_single_block_metered,
		buffered_link::{self, BufferedLinkSender, BufferedLinkReceiver},
	},
	metrics::Metrics,
};

/// Interface to a basic block import queue that is importing blocks sequentially in a separate
/// task, with plugable verification.
pub struct BasicQueue<B: BlockT, Transaction> {
	/// Channel to send messages to the background task.
	sender: TracingUnboundedSender<ToWorkerMsg<B>>,
	/// Results coming from the worker task.
	result_port: BufferedLinkReceiver<B>,
	_phantom: PhantomData<Transaction>,
}

impl<B: BlockT, Transaction> Drop for BasicQueue<B, Transaction> {
	fn drop(&mut self) {
		// Flush the queue and close the receiver to terminate the future.
		self.sender.close_channel();
		self.result_port.close();
	}
}

impl<B: BlockT, Transaction: Send + 'static> BasicQueue<B, Transaction> {
	/// Instantiate a new basic queue, with given verifier.
	///
	/// This creates a background task, and calls `on_start` on the justification importer and
	/// finality proof importer.
	pub fn new<V: 'static + Verifier<B>>(
		verifier: V,
		block_import: BoxBlockImport<B, Transaction>,
		justification_import: Option<BoxJustificationImport<B>>,
		finality_proof_import: Option<BoxFinalityProofImport<B>>,
		spawner: &impl sp_core::traits::SpawnNamed,
		prometheus_registry: Option<&Registry>,
	) -> Self {
		let (result_sender, result_port) = buffered_link::buffered_link();
		let metrics = prometheus_registry.and_then(|r|
			Metrics::register(r)
			.map_err(|err| { log::warn!("Failed to register Prometheus metrics: {}", err); })
			.ok()
		);
		let (future, worker_sender) = BlockImportWorker::new(
			result_sender,
			verifier,
			block_import,
			justification_import,
			finality_proof_import,
			metrics,
		);

		spawner.spawn_blocking("basic-block-import-worker", future.boxed());

		Self {
			sender: worker_sender,
			result_port,
			_phantom: PhantomData,
		}
	}
}

impl<B: BlockT, Transaction: Send> ImportQueue<B> for BasicQueue<B, Transaction> {
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
		let _ = self.sender
			.unbounded_send(
				ToWorkerMsg::ImportJustification(who, hash, number, justification)
			);
	}

	fn import_finality_proof(
		&mut self,
		who: Origin,
		hash: B::Hash,
		number: NumberFor<B>,
		finality_proof: Vec<u8>,
	) {
		trace!(target: "sync", "Scheduling finality proof of {}/{} for import", number, hash);
		let _ = self.sender
			.unbounded_send(
				ToWorkerMsg::ImportFinalityProof(who, hash, number, finality_proof)
			);
	}

	fn poll_actions(&mut self, cx: &mut Context, link: &mut dyn Link<B>) {
		self.result_port.poll_actions(cx, link);
	}
}

/// Message destinated to the background worker.
#[derive(Debug)]
enum ToWorkerMsg<B: BlockT> {
	ImportBlocks(BlockOrigin, Vec<IncomingBlock<B>>),
	ImportJustification(Origin, B::Hash, NumberFor<B>, Justification),
	ImportFinalityProof(Origin, B::Hash, NumberFor<B>, Vec<u8>),
}

struct BlockImportWorker<B: BlockT, Transaction> {
	result_sender: BufferedLinkSender<B>,
	justification_import: Option<BoxJustificationImport<B>>,
	finality_proof_import: Option<BoxFinalityProofImport<B>>,
	delay_between_blocks: Duration,
	metrics: Option<Metrics>,
	_phantom: PhantomData<Transaction>,
}

impl<B: BlockT, Transaction: Send> BlockImportWorker<B, Transaction> {
	fn new<V: 'static + Verifier<B>>(
		result_sender: BufferedLinkSender<B>,
		verifier: V,
		block_import: BoxBlockImport<B, Transaction>,
		justification_import: Option<BoxJustificationImport<B>>,
		finality_proof_import: Option<BoxFinalityProofImport<B>>,
		metrics: Option<Metrics>,
	) -> (impl Future<Output = ()> + Send, TracingUnboundedSender<ToWorkerMsg<B>>) {
		let (sender, mut port) = tracing_unbounded("mpsc_block_import_worker");

		let mut worker = BlockImportWorker {
			result_sender,
			justification_import,
			finality_proof_import,
			delay_between_blocks: Duration::new(0, 0),
			metrics,
			_phantom: PhantomData,
		};

		// Let's initialize `justification_import` and `finality_proof_import`.
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

		// The future below has two possible states:
		//
		// - Currently importing many blocks, in which case `importing` is `Some` and contains a
		//   `Future`, and `block_import` is `None`.
		// - Something else, in which case `block_import` is `Some` and `importing` is None.
		//
		let mut block_import_verifier = Some((block_import, verifier));
		let mut importing = None;

		let future = futures::future::poll_fn(move |cx| {
			loop {
				// If the results sender is closed, that means that the import queue is shutting
				// down and we should end this future.
				if worker.result_sender.is_closed() {
					return Poll::Ready(())
				}

				// If we are in the process of importing a bunch of block, let's resume this
				// process before doing anything more.
				if let Some(imp_fut) = importing.as_mut() {
					match Future::poll(Pin::new(imp_fut), cx) {
						Poll::Pending => return Poll::Pending,
						Poll::Ready((bi, verif)) => {
							block_import_verifier = Some((bi, verif));
							importing = None;
						},
					}
				}

				debug_assert!(importing.is_none());
				debug_assert!(block_import_verifier.is_some());

				// Grab the next action request sent to the import queue.
				let msg = match Stream::poll_next(Pin::new(&mut port), cx) {
					Poll::Ready(Some(msg)) => msg,
					Poll::Ready(None) => return Poll::Ready(()),
					Poll::Pending => return Poll::Pending,
				};

				match msg {
					ToWorkerMsg::ImportBlocks(origin, blocks) => {
						// On blocks import request, we merely *start* the process and store
						// a `Future` into `importing`.
						let (bi, verif) = block_import_verifier.take()
							.expect("block_import_verifier is always Some; qed");
						importing = Some(worker.import_batch(bi, verif, origin, blocks));
					},
					ToWorkerMsg::ImportFinalityProof(who, hash, number, proof) => {
						let (_, verif) = block_import_verifier.as_mut()
							.expect("block_import_verifier is always Some; qed");
						worker.import_finality_proof(verif, who, hash, number, proof);
					},
					ToWorkerMsg::ImportJustification(who, hash, number, justification) => {
						worker.import_justification(who, hash, number, justification);
					}
				}
			}
		});

		(future, sender)
	}

	/// Returns a `Future` that imports the given blocks and sends the results on
	/// `self.result_sender`.
	///
	/// For lifetime reasons, the `BlockImport` implementation must be passed by value, and is
	/// yielded back in the output once the import is finished.
	fn import_batch<V: 'static + Verifier<B>>(
		&mut self,
		block_import: BoxBlockImport<B, Transaction>,
		verifier: V,
		origin: BlockOrigin,
		blocks: Vec<IncomingBlock<B>>,
	) -> impl Future<Output = (BoxBlockImport<B, Transaction>, V)> {
		let mut result_sender = self.result_sender.clone();
		let metrics = self.metrics.clone();

		import_many_blocks(block_import, origin, blocks, verifier, self.delay_between_blocks, metrics)
			.then(move |(imported, count, results, block_import, verifier)| {
				result_sender.blocks_processed(imported, count, results);
				future::ready((block_import, verifier))
			})
	}

	fn import_finality_proof<V: 'static + Verifier<B>>(
		&mut self,
		verifier: &mut V,
		who: Origin,
		hash: B::Hash,
		number: NumberFor<B>,
		finality_proof: Vec<u8>
	) {
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
/// For lifetime reasons, the `BlockImport` implementation must be passed by value, and is yielded
/// back in the output once the import is finished.
///
/// The returned `Future` yields at every imported block, which makes the execution more
/// fine-grained and making it possible to interrupt the process.
fn import_many_blocks<B: BlockT, V: Verifier<B>, Transaction>(
	import_handle: BoxBlockImport<B, Transaction>,
	blocks_origin: BlockOrigin,
	blocks: Vec<IncomingBlock<B>>,
	verifier: V,
	delay_between_blocks: Duration,
	metrics: Option<Metrics>,
) -> impl Future<
	Output = (
		usize,
		usize,
		Vec<(Result<BlockImportResult<NumberFor<B>>, BlockImportError>, B::Hash,)>,
		BoxBlockImport<B, Transaction>,
		V
	)
>
{
	let count = blocks.len();

	let blocks_range = match (
		blocks.first().and_then(|b| b.header.as_ref().map(|h| h.number())),
		blocks.last().and_then(|b| b.header.as_ref().map(|h| h.number())),
	) {
		(Some(first), Some(last)) if first != last => format!(" ({}..{})", first, last),
		(Some(first), Some(_)) => format!(" ({})", first),
		_ => Default::default(),
	};

	trace!(target: "sync", "Starting import of {} blocks {}", count, blocks_range);

	let mut imported = 0;
	let mut results = vec![];
	let mut has_error = false;
	let mut blocks = blocks.into_iter();
	let mut import_handle = Some(import_handle);
	let mut waiting = None;
	let mut verifier = Some(verifier);

	// Blocks in the response/drain should be in ascending order.

	future::poll_fn(move |cx| {
		// Handle the optional timer that makes us wait before the next import.
		if let Some(waiting) = &mut waiting {
			match Future::poll(Pin::new(waiting), cx) {
				Poll::Ready(_) => {},
				Poll::Pending => return Poll::Pending,
			}
		}
		waiting = None;

		// Is there any block left to import?
		let block = match blocks.next() {
			Some(b) => b,
			None => {
				// No block left to import, success!
				let import_handle = import_handle.take()
					.expect("Future polled again after it has finished (import handle is None)");
				let verifier = verifier.take()
					.expect("Future polled again after it has finished (verifier handle is None)");
				let results = mem::replace(&mut results, Vec::new());
				return Poll::Ready((imported, count, results, import_handle, verifier));
			},
		};

		// We extract the content of `import_handle` and `verifier` only when the future ends,
		// therefore `import_handle` and `verifier` are always `Some` here. It is illegal to poll
		// a `Future` again after it has ended.
		let import_handle = import_handle.as_mut()
			.expect("Future polled again after it has finished (import handle is None)");
		let verifier = verifier.as_mut()
			.expect("Future polled again after it has finished (verifier handle is None)");

		let block_number = block.header.as_ref().map(|h| h.number().clone());
		let block_hash = block.hash;
		let import_result = if has_error {
			Err(BlockImportError::Cancelled)
		} else {
			// The actual import.
			import_single_block_metered(
				&mut **import_handle,
				blocks_origin.clone(),
				block,
				verifier,
				metrics.clone(),
			)
		};

		if let Some(metrics) = metrics.as_ref() {
			metrics.report_import::<B>(&import_result);
		}

		if import_result.is_ok() {
			trace!(target: "sync", "Block imported successfully {:?} ({})", block_number, block_hash);
			imported += 1;
		} else {
			has_error = true;
		}

		results.push((import_result, block_hash));

		// Notifies the current task again so that we re-execute this closure again for the next
		// block.
		if delay_between_blocks != Duration::new(0, 0) {
			waiting = Some(Delay::new(delay_between_blocks));
		}
		cx.waker().wake_by_ref();
		Poll::Pending
	})
}
