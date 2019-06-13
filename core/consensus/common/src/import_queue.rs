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

//! Import Queue primitive: something which can verify and import blocks.
//!
//! This serves as an intermediate and abstracted step between synchronization
//! and import. Each mode of consensus will have its own requirements for block
//! verification. Some algorithms can verify in parallel, while others only
//! sequentially.
//!
//! The `ImportQueue` trait allows such verification strategies to be
//! instantiated. The `BasicQueue` and `BasicVerifier` traits allow serial
//! queues to be instantiated simply.

use crate::block_import::{
	BlockImport, BlockOrigin, ImportBlock, ImportedAux, ImportResult, JustificationImport,
	FinalityProofImport, FinalityProofRequestBuilder,
};
use crossbeam_channel::{self as channel, Sender};
use parity_codec::Encode;
use futures::{prelude::*, sync::mpsc};
use std::sync::Arc;
use std::thread;

use runtime_primitives::traits::{
	AuthorityIdFor, Block as BlockT, Header as HeaderT, NumberFor, Digest,
};
use runtime_primitives::Justification;

use crate::error::Error as ConsensusError;
use parity_codec::alloc::collections::hash_map::HashMap;

/// Reputation change for peers which send us a block with an incomplete header.
const INCOMPLETE_HEADER_REPUTATION_CHANGE: i32 = -(1 << 20);
/// Reputation change for peers which send us a block which we fail to verify.
const VERIFICATION_FAIL_REPUTATION_CHANGE: i32 = -(1 << 20);
/// Reputation change for peers which send us a bad block.
const BAD_BLOCK_REPUTATION_CHANGE: i32 = -(1 << 29);
/// Reputation change for peers which send us a block with bad justifications.
const BAD_JUSTIFICATION_REPUTATION_CHANGE: i32 = -(1 << 16);

/// Shared block import struct used by the queue.
pub type SharedBlockImport<B> = Arc<dyn BlockImport<B, Error = ConsensusError> + Send + Sync>;

/// Shared justification import struct used by the queue.
pub type SharedJustificationImport<B> = Arc<dyn JustificationImport<B, Error=ConsensusError> + Send + Sync>;

/// Shared finality proof import struct used by the queue.
pub type SharedFinalityProofImport<B> = Arc<dyn FinalityProofImport<B, Error=ConsensusError> + Send + Sync>;

/// Shared finality proof request builder struct used by the queue.
pub type SharedFinalityProofRequestBuilder<B> = Arc<dyn FinalityProofRequestBuilder<B> + Send + Sync>;

/// Maps to the Origin used by the network.
pub type Origin = libp2p::PeerId;

/// Block data used by the queue.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IncomingBlock<B: BlockT> {
	/// Block header hash.
	pub hash: <B as BlockT>::Hash,
	/// Block header if requested.
	pub header: Option<<B as BlockT>::Header>,
	/// Block body if requested.
	pub body: Option<Vec<<B as BlockT>::Extrinsic>>,
	/// Justification if requested.
	pub justification: Option<Justification>,
	/// The peer, we received this from
	pub origin: Option<Origin>,
}

/// Verify a justification of a block
pub trait Verifier<B: BlockT>: Send + Sync {
	/// Verify the given data and return the ImportBlock and an optional
	/// new set of validators to import. If not, err with an Error-Message
	/// presented to the User in the logs.
	fn verify(
		&self,
		origin: BlockOrigin,
		header: B::Header,
		justification: Option<Justification>,
		body: Option<Vec<B::Extrinsic>>,
	) -> Result<(ImportBlock<B>, Option<Vec<AuthorityIdFor<B>>>), String>;
}

/// Blocks import queue API.
///
/// The `import_*` methods can be called in order to send elements for the import queue to verify.
/// Afterwards, call `poll_actions` to determine how to respond to these elements.
pub trait ImportQueue<B: BlockT>: Send {
	/// Import bunch of blocks.
	fn import_blocks(&mut self, origin: BlockOrigin, blocks: Vec<IncomingBlock<B>>);
	/// Import a block justification.
	fn import_justification(&mut self, who: Origin, hash: B::Hash, number: NumberFor<B>, justification: Justification);
	/// Import block finality proof.
	fn import_finality_proof(&mut self, who: Origin, hash: B::Hash, number: NumberFor<B>, finality_proof: Vec<u8>);
	/// Polls for actions to perform on the network.
	///
	/// This method should behave in a way similar to `Future::poll`. It can register the current
	/// task and notify later when more actions are ready to be polled. To continue the comparison,
	/// it is as if this method always returned `Ok(Async::NotReady)`.
	fn poll_actions(&mut self, link: &mut dyn Link<B>);
}

/// Interface to a basic block import queue that is importing blocks
/// sequentially in a separate thread, with pluggable verification.
pub struct BasicQueue<B: BlockT> {
	/// Channel to send messages to the background thread.
	sender: Option<Sender<ToWorkerMsg<B>>>,
	/// Results coming from the worker thread.
	result_port: BufferedLinkReceiver<B>,
	/// Sent through the link as soon as possible.
	finality_proof_request_builder: Option<SharedFinalityProofRequestBuilder<B>>,
}

impl<B: BlockT> Drop for BasicQueue<B> {
	fn drop(&mut self) {
		if let Some(sender) = self.sender.take() {
			let (shutdown_sender, shutdown_receiver) = channel::unbounded();
			if sender.send(ToWorkerMsg::Shutdown(shutdown_sender)).is_ok() {
				let _ = shutdown_receiver.recv();
			}
		}
	}
}

/// "BasicQueue" is a wrapper around a channel sender to the "BlockImporter".
/// "BasicQueue" itself does not keep any state or do any importing work, and
/// can therefore be send to other threads.
///
/// "BasicQueue" implements "ImportQueue" by sending messages to the
/// "BlockImporter", which runs in it's own thread.
///
/// The "BlockImporter" is responsible for handling incoming requests from the
/// "BasicQueue". Some of these requests are handled by the "BlockImporter"
/// itself, such as "is_importing", "status", and justifications.
///
/// The "import block" work will be offloaded to a single "BlockImportWorker",
/// running in another thread. Offloading the work is done via a channel,
/// ensuring blocks in this implementation are imported sequentially and in
/// order (as received by the "BlockImporter").
///
/// As long as the "BasicQueue" is not dropped, the "BlockImporter" will keep
/// running. The "BlockImporter" owns a sender to the "BlockImportWorker",
/// ensuring that the worker is kept alive until that sender is dropped.
impl<B: BlockT> BasicQueue<B> {
	/// Instantiate a new basic queue, with given verifier.
	pub fn new<V: 'static + Verifier<B>>(
		verifier: Arc<V>,
		block_import: SharedBlockImport<B>,
		justification_import: Option<SharedJustificationImport<B>>,
		finality_proof_import: Option<SharedFinalityProofImport<B>>,
		finality_proof_request_builder: Option<SharedFinalityProofRequestBuilder<B>>,
	) -> Self {
		let (result_sender, result_port) = buffered_link();
		let worker_sender = BlockImportWorker::new(
			result_sender,
			verifier,
			block_import,
			justification_import,
			finality_proof_import,
		);

		Self {
			sender: Some(worker_sender),
			result_port,
			finality_proof_request_builder,
		}
	}

	/// Send synchronization request to the block import channel.
	///
	/// The caller should wait for Link::synchronized() call to ensure that it
	/// has synchronized with ImportQueue.
	#[cfg(any(test, feature = "test-helpers"))]
	pub fn synchronize(&self) {
		if let Some(ref sender) = self.sender {
			let _ = sender.send(ToWorkerMsg::Synchronize);
		}
	}
}

impl<B: BlockT> ImportQueue<B> for BasicQueue<B> {
	fn import_blocks(&mut self, origin: BlockOrigin, blocks: Vec<IncomingBlock<B>>) {
		if blocks.is_empty() {
			return;
		}

		if let Some(ref sender) = self.sender {
			trace!(target: "sync", "Scheduling {} blocks for import", blocks.len());
			let _ = sender.send(ToWorkerMsg::ImportBlocks(origin, blocks));
		}
	}

	fn import_justification(&mut self, who: Origin, hash: B::Hash, number: NumberFor<B>, justification: Justification) {
		if let Some(ref sender) = self.sender {
			let _ = sender.send(ToWorkerMsg::ImportJustification(who.clone(), hash, number, justification));
		}
	}

	fn import_finality_proof(&mut self, who: Origin, hash: B::Hash, number: NumberFor<B>, finality_proof: Vec<u8>) {
		if let Some(ref sender) = self.sender {
			trace!(target: "sync", "Scheduling finality proof of {}/{} for import", number, hash);
			let _ = sender.send(ToWorkerMsg::ImportFinalityProof(who, hash, number, finality_proof));
		}
	}

	fn poll_actions(&mut self, link: &mut dyn Link<B>) {
		if let Some(fprb) = self.finality_proof_request_builder.take() {
			link.set_finality_proof_request_builder(fprb);
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
	Shutdown(Sender<()>),
	#[cfg(any(test, feature = "test-helpers"))]
	Synchronize,
}

struct BlockImportWorker<B: BlockT, V: Verifier<B>> {
	result_sender: BufferedLinkSender<B>,
	block_import: SharedBlockImport<B>,
	justification_import: Option<SharedJustificationImport<B>>,
	finality_proof_import: Option<SharedFinalityProofImport<B>>,
	verifier: Arc<V>,
}

impl<B: BlockT, V: 'static + Verifier<B>> BlockImportWorker<B, V> {
	fn new(
		result_sender: BufferedLinkSender<B>,
		verifier: Arc<V>,
		block_import: SharedBlockImport<B>,
		justification_import: Option<SharedJustificationImport<B>>,
		finality_proof_import: Option<SharedFinalityProofImport<B>>,
	) -> Sender<ToWorkerMsg<B>> {
		let (sender, port) = channel::bounded(4);
		let _ = thread::Builder::new()
			.name("ImportQueueWorker".into())
			.spawn(move || {
				let mut worker = BlockImportWorker {
					result_sender,
					verifier,
					justification_import,
					block_import,
					finality_proof_import,
				};
				if let Some(justification_import) = worker.justification_import.as_ref() {
					justification_import.on_start(&mut worker.result_sender);
				}
				if let Some(finality_proof_import) = worker.finality_proof_import.as_ref() {
					finality_proof_import.on_start(&mut worker.result_sender);
				}
				for msg in port.iter() {
					// Working until all senders have been dropped...
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
						ToWorkerMsg::Shutdown(result_sender) => {
							let _ = result_sender.send(());
							break;
						},
						#[cfg(any(test, feature = "test-helpers"))]
						ToWorkerMsg::Synchronize => {
							trace!(target: "sync", "Sending sync message");
							worker.result_sender.synchronized();
						},
					}
				}
			})
			.expect("ImportQueueWorker thread spawning failed");
		sender
	}

	fn import_a_batch_of_blocks(&mut self, origin: BlockOrigin, blocks: Vec<IncomingBlock<B>>) {
		let (imported, count, results) = import_many_blocks(
			&*self.block_import,
			origin,
			blocks,
			self.verifier.clone(),
		);

		trace!(target: "sync", "Imported {} of {}", imported, count);

		let mut has_error = false;
		let mut hashes = vec![];
		for (result, hash) in results {
			hashes.push(hash);

			if has_error {
				continue;
			}

			if result.is_err() {
				has_error = true;
			}

			match result {
				Ok(BlockImportResult::ImportedKnown(number)) => self.result_sender.block_imported(&hash, number),
				Ok(BlockImportResult::ImportedUnknown(number, aux, who)) => {
					self.result_sender.block_imported(&hash, number);

					if aux.clear_justification_requests {
						trace!(target: "sync", "Block imported clears all pending justification requests {}: {:?}", number, hash);
						self.result_sender.clear_justification_requests();
					}

					if aux.needs_justification {
						trace!(target: "sync", "Block imported but requires justification {}: {:?}", number, hash);
						self.result_sender.request_justification(&hash, number);
					}

					if aux.bad_justification {
						if let Some(peer) = who {
							info!("Sent block with bad justification to import");
							self.result_sender.report_peer(peer, BAD_JUSTIFICATION_REPUTATION_CHANGE);
						}
					}

					if aux.needs_finality_proof {
						trace!(target: "sync", "Block imported but requires finality proof {}: {:?}", number, hash);
						self.result_sender.request_finality_proof(&hash, number);
					}
				},
				Err(BlockImportError::IncompleteHeader(who)) => {
					if let Some(peer) = who {
						info!("Peer sent block with incomplete header to import");
						self.result_sender.report_peer(peer, INCOMPLETE_HEADER_REPUTATION_CHANGE);
						self.result_sender.restart();
					}
				},
				Err(BlockImportError::VerificationFailed(who, e)) => {
					if let Some(peer) = who {
						info!("Verification failed from peer: {}", e);
						self.result_sender.report_peer(peer, VERIFICATION_FAIL_REPUTATION_CHANGE);
						self.result_sender.restart();
					}
				},
				Err(BlockImportError::BadBlock(who)) => {
					if let Some(peer) = who {
						info!("Bad block");
						self.result_sender.report_peer(peer, BAD_BLOCK_REPUTATION_CHANGE);
						self.result_sender.restart();
					}
				},
				Err(BlockImportError::UnknownParent) | Err(BlockImportError::Error) => {
					self.result_sender.restart();
				},
			};
		}

		self.result_sender.blocks_processed(hashes, has_error);
	}

	fn import_finality_proof(&mut self, who: Origin, hash: B::Hash, number: NumberFor<B>, finality_proof: Vec<u8>) {
		let result = self.finality_proof_import.as_ref().map(|finality_proof_import| {
			finality_proof_import.import_finality_proof(hash, number, finality_proof, &*self.verifier)
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

	fn import_justification(&mut self, who: Origin, hash: B::Hash, number: NumberFor<B>, justification: Justification) {
		let success = self.justification_import.as_ref().map(|justification_import| {
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

/// Hooks that the verification queue can use to influence the synchronization
/// algorithm.
pub trait Link<B: BlockT>: Send {
	/// Block imported.
	fn block_imported(&mut self, _hash: &B::Hash, _number: NumberFor<B>) {}
	/// Batch of blocks imported, with or without error.
	fn blocks_processed(&mut self, _processed_blocks: Vec<B::Hash>, _has_error: bool) {}
	/// Justification import result.
	fn justification_imported(&mut self, _who: Origin, _hash: &B::Hash, _number: NumberFor<B>, _success: bool) {}
	/// Clear all pending justification requests.
	fn clear_justification_requests(&mut self) {}
	/// Request a justification for the given block.
	fn request_justification(&mut self, _hash: &B::Hash, _number: NumberFor<B>) {}
	/// Finality proof import result.
	///
	/// Even though we have asked for finality proof of block A, provider could return proof of
	/// some earlier block B, if the proof for A was too large. The sync module should continue
	/// asking for proof of A in this case.
	fn finality_proof_imported(
		&mut self,
		_who: Origin,
		_request_block: (B::Hash, NumberFor<B>),
		_finalization_result: Result<(B::Hash, NumberFor<B>), ()>,
	) {}
	/// Request a finality proof for the given block.
	fn request_finality_proof(&mut self, _hash: &B::Hash, _number: NumberFor<B>) {}
	/// Remember finality proof request builder on start.
	fn set_finality_proof_request_builder(&mut self, _request_builder: SharedFinalityProofRequestBuilder<B>) {}
	/// Adjusts the reputation of the given peer.
	fn report_peer(&mut self, _who: Origin, _reputation_change: i32) {}
	/// Restart sync.
	fn restart(&mut self) {}
	/// Synchronization request has been processed.
	#[cfg(any(test, feature = "test-helpers"))]
	fn synchronized(&mut self) {}
}

/// Wraps around an unbounded channel from the `futures` crate. The sender implements `Link` and
/// can be used to buffer commands, and the receiver can be used to poll said commands and transfer
/// them to another link.
pub fn buffered_link<B: BlockT>() -> (BufferedLinkSender<B>, BufferedLinkReceiver<B>) {
	let (tx, rx) = mpsc::unbounded();
	let tx = BufferedLinkSender { tx };
	let rx = BufferedLinkReceiver { rx };
	(tx, rx)
}

/// See [`buffered_link`].
pub struct BufferedLinkSender<B: BlockT> {
	tx: mpsc::UnboundedSender<BlockImportWorkerMsg<B>>,
}

/// Internal buffered message.
enum BlockImportWorkerMsg<B: BlockT> {
	BlockImported(B::Hash, NumberFor<B>),
	BlocksProcessed(Vec<B::Hash>, bool),
	JustificationImported(Origin, B::Hash, NumberFor<B>, bool),
	ClearJustificationRequests,
	RequestJustification(B::Hash, NumberFor<B>),
	FinalityProofImported(Origin, (B::Hash, NumberFor<B>), Result<(B::Hash, NumberFor<B>), ()>),
	RequestFinalityProof(B::Hash, NumberFor<B>),
	SetFinalityProofRequestBuilder(SharedFinalityProofRequestBuilder<B>),
	ReportPeer(Origin, i32),
	Restart,
	#[cfg(any(test, feature = "test-helpers"))]
	Synchronized,
}

impl<B: BlockT> Link<B> for BufferedLinkSender<B> {
	fn block_imported(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self.tx.unbounded_send(BlockImportWorkerMsg::BlockImported(hash.clone(), number));
	}

	fn blocks_processed(&mut self, processed_blocks: Vec<B::Hash>, has_error: bool) {
		let _ = self.tx.unbounded_send(BlockImportWorkerMsg::BlocksProcessed(processed_blocks, has_error));
	}

	fn justification_imported(&mut self, who: Origin, hash: &B::Hash, number: NumberFor<B>, success: bool) {
		let _ = self.tx.unbounded_send(BlockImportWorkerMsg::JustificationImported(who, hash.clone(), number, success));
	}

	fn clear_justification_requests(&mut self) {
		let _ = self.tx.unbounded_send(BlockImportWorkerMsg::ClearJustificationRequests);
	}

	fn request_justification(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self.tx.unbounded_send(BlockImportWorkerMsg::RequestJustification(hash.clone(), number));
	}

	fn finality_proof_imported(
		&mut self,
		who: Origin,
		request_block: (B::Hash, NumberFor<B>),
		finalization_result: Result<(B::Hash, NumberFor<B>), ()>,
	) {
		let msg = BlockImportWorkerMsg::FinalityProofImported(who, request_block, finalization_result);
		let _ = self.tx.unbounded_send(msg);
	}

	fn request_finality_proof(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self.tx.unbounded_send(BlockImportWorkerMsg::RequestFinalityProof(hash.clone(), number));
	}

	fn set_finality_proof_request_builder(&mut self, request_builder: SharedFinalityProofRequestBuilder<B>) {
		let _ = self.tx.unbounded_send(BlockImportWorkerMsg::SetFinalityProofRequestBuilder(request_builder));
	}

	fn report_peer(&mut self, who: Origin, reputation_change: i32) {
		let _ = self.tx.unbounded_send(BlockImportWorkerMsg::ReportPeer(who, reputation_change));
	}

	fn restart(&mut self) {
		let _ = self.tx.unbounded_send(BlockImportWorkerMsg::Restart);
	}

	#[cfg(any(test, feature = "test-helpers"))]
	fn synchronized(&mut self) {
		let _ = self.tx.unbounded_send(BlockImportWorkerMsg::Synchronized);
	}
}

/// See [`buffered_link`].
pub struct BufferedLinkReceiver<B: BlockT> {
	rx: mpsc::UnboundedReceiver<BlockImportWorkerMsg<B>>,
}

impl<B: BlockT> BufferedLinkReceiver<B> {
	/// Polls for the buffered link actions. Any enqueued action will be propagated to the link
	/// passed as parameter.
	///
	/// This method should behave in a way similar to `Future::poll`. It can register the current
	/// task and notify later when more actions are ready to be polled. To continue the comparison,
	/// it is as if this method always returned `Ok(Async::NotReady)`.
	pub fn poll_actions(&mut self, link: &mut dyn Link<B>) {
		loop {
			let msg = if let Ok(Async::Ready(Some(msg))) = self.rx.poll() {
				msg
			} else {
				break
			};

			match msg {
				BlockImportWorkerMsg::BlockImported(hash, number) =>
					link.block_imported(&hash, number),
				BlockImportWorkerMsg::BlocksProcessed(blocks, has_error) =>
					link.blocks_processed(blocks, has_error),
				BlockImportWorkerMsg::JustificationImported(who, hash, number, success) =>
					link.justification_imported(who, &hash, number, success),
				BlockImportWorkerMsg::ClearJustificationRequests =>
					link.clear_justification_requests(),
				BlockImportWorkerMsg::RequestJustification(hash, number) =>
					link.request_justification(&hash, number),
				BlockImportWorkerMsg::FinalityProofImported(who, block, result) =>
					link.finality_proof_imported(who, block, result),
				BlockImportWorkerMsg::RequestFinalityProof(hash, number) =>
					link.request_finality_proof(&hash, number),
				BlockImportWorkerMsg::SetFinalityProofRequestBuilder(builder) =>
					link.set_finality_proof_request_builder(builder),
				BlockImportWorkerMsg::ReportPeer(who, reput) =>
					link.report_peer(who, reput),
				BlockImportWorkerMsg::Restart =>
					link.restart(),
				#[cfg(any(test, feature = "test-helpers"))]
				BlockImportWorkerMsg::Synchronized =>
					link.synchronized(),
			}
		}
	}
}

/// Block import successful result.
#[derive(Debug, PartialEq)]
pub enum BlockImportResult<N: ::std::fmt::Debug + PartialEq> {
	/// Imported known block.
	ImportedKnown(N),
	/// Imported unknown block.
	ImportedUnknown(N, ImportedAux, Option<Origin>),
}

/// Block import error.
#[derive(Debug, PartialEq)]
pub enum BlockImportError {
	/// Block missed header, can't be imported
	IncompleteHeader(Option<Origin>),
	/// Block verification failed, can't be imported
	VerificationFailed(Option<Origin>, String),
	/// Block is known to be Bad
	BadBlock(Option<Origin>),
	/// Block has an unknown parent
	UnknownParent,
	/// Other Error.
	Error,
}

/// Import several blocks at once, returning import result for each block.
fn import_many_blocks<B: BlockT, V: Verifier<B>>(
	import_handle: &dyn BlockImport<B, Error = ConsensusError>,
	blocks_origin: BlockOrigin,
	blocks: Vec<IncomingBlock<B>>,
	verifier: Arc<V>,
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
		let block_hash = block.hash;
		let import_result = if has_error {
			Err(BlockImportError::Error)
		} else {
			import_single_block(
				import_handle,
				blocks_origin.clone(),
				block,
				verifier.clone(),
			)
		};
		let was_ok = import_result.is_ok();
		results.push((import_result, block_hash));
		if was_ok {
			imported += 1;
		} else {
			has_error = true;
		}
	}

	(imported, count, results)
}

/// Single block import function.
pub fn import_single_block<B: BlockT, V: Verifier<B>>(
	import_handle: &dyn BlockImport<B, Error = ConsensusError>,
	block_origin: BlockOrigin,
	block: IncomingBlock<B>,
	verifier: Arc<V>,
) -> Result<BlockImportResult<NumberFor<B>>, BlockImportError> {
	let peer = block.origin;

	let (header, justification) = match (block.header, block.justification) {
		(Some(header), justification) => (header, justification),
		(None, _) => {
			if let Some(ref peer) = peer {
				debug!(target: "sync", "Header {} was not provided by {} ", block.hash, peer);
			} else {
				debug!(target: "sync", "Header {} was not provided ", block.hash);
			}
			return Err(BlockImportError::IncompleteHeader(peer))
		},
	};

	trace!(target: "sync", "Header {} has {:?} logs", block.hash, header.digest().logs().len());

	let number = header.number().clone();
	let hash = header.hash();
	let parent = header.parent_hash().clone();

	let import_error = |e| {
		match e {
			Ok(ImportResult::AlreadyInChain) => {
				trace!(target: "sync", "Block already in chain {}: {:?}", number, hash);
				Ok(BlockImportResult::ImportedKnown(number))
			},
			Ok(ImportResult::Imported(aux)) => Ok(BlockImportResult::ImportedUnknown(number, aux, peer.clone())),
			Ok(ImportResult::UnknownParent) => {
				debug!(target: "sync", "Block with unknown parent {}: {:?}, parent: {:?}", number, hash, parent);
				Err(BlockImportError::UnknownParent)
			},
			Ok(ImportResult::KnownBad) => {
				debug!(target: "sync", "Peer gave us a bad block {}: {:?}", number, hash);
				Err(BlockImportError::BadBlock(peer.clone()))
			},
			Err(e) => {
				debug!(target: "sync", "Error importing block {}: {:?}: {:?}", number, hash, e);
				Err(BlockImportError::Error)
			}
		}
	};

	match import_error(import_handle.check_block(hash, parent))? {
		BlockImportResult::ImportedUnknown { .. } => (),
		r => return Ok(r), // Any other successful result means that the block is already imported.
	}

	let (import_block, new_authorities) = verifier.verify(block_origin, header, justification, block.body)
		.map_err(|msg| {
			if let Some(ref peer) = peer {
				trace!(target: "sync", "Verifying {}({}) from {} failed: {}", number, hash, peer, msg);
			} else {
				trace!(target: "sync", "Verifying {}({}) failed: {}", number, hash, msg);
			}
			BlockImportError::VerificationFailed(peer.clone(), msg)
		})?;

	let mut cache = HashMap::new();
	if let Some(authorities) = new_authorities {
		cache.insert(crate::well_known_cache_keys::AUTHORITIES, authorities.encode());
	}

	import_error(import_handle.import_block(import_block, cache))
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::block_import::ForkChoiceStrategy;
	use libp2p::PeerId;
	use test_client::runtime::{Block, Hash};

	#[derive(Debug, PartialEq)]
	enum LinkMsg {
		BlockImported,
		FinalityProofImported,
		Disconnected,
		Restarted,
	}

	#[derive(Clone)]
	struct TestLink {
		sender: Sender<LinkMsg>,
	}

	impl TestLink {
		fn new(sender: Sender<LinkMsg>) -> TestLink {
			TestLink {
				sender,
			}
		}
	}

	impl Link<Block> for TestLink {
		fn block_imported(&mut self, _hash: &Hash, _number: NumberFor<Block>) {
			let _ = self.sender.send(LinkMsg::BlockImported);
		}
		fn finality_proof_imported(
			&mut self,
			_: Origin,
			_: (Hash, NumberFor<Block>),
			_: Result<(Hash, NumberFor<Block>), ()>,
		) {
			let _ = self.sender.send(LinkMsg::FinalityProofImported);
		}
		fn report_peer(&mut self, _: Origin, _: i32) {
			let _ = self.sender.send(LinkMsg::Disconnected);
		}
		fn restart(&mut self) {
			let _ = self.sender.send(LinkMsg::Restarted);
		}
	}

	impl<B: BlockT> Verifier<B> for () {
		fn verify(
			&self,
			origin: BlockOrigin,
			header: B::Header,
			justification: Option<Justification>,
			body: Option<Vec<B::Extrinsic>>,
		) -> Result<(ImportBlock<B>, Option<Vec<AuthorityIdFor<B>>>), String> {
			Ok((ImportBlock {
				origin,
				header,
				body,
				finalized: false,
				justification,
				post_digests: vec![],
				auxiliary: Vec::new(),
				fork_choice: ForkChoiceStrategy::LongestChain,
			}, None))
		}
	}

	#[test]
	fn process_import_result_works() {
		let (result_sender, result_port) = channel::unbounded();
		let (worker_sender, _) = channel::unbounded();
		let (link_sender, link_port) = channel::unbounded();
		let importer_sender = BlockImporter::<Block>::new(result_port, worker_sender, Arc::new(()), None, None, None);
		let link = TestLink::new(link_sender);
		let (ack_sender, start_ack_port) = channel::bounded(4);
		let _ = importer_sender.send(BlockImportMsg::Start(Box::new(link.clone()), ack_sender));

		// Ensure the importer handles Start before any result messages.
		let _ = start_ack_port.recv();

		// Send a known
		let results = vec![(Ok(BlockImportResult::ImportedKnown(Default::default())), Default::default())];
		let _ = result_sender.send(BlockImportWorkerMsg::ImportedBlocks(results)).ok().unwrap();
		assert_eq!(link_port.recv(), Ok(LinkMsg::BlockImported));

		// Send a second known
		let results = vec![(Ok(BlockImportResult::ImportedKnown(Default::default())), Default::default())];
		let _ = result_sender.send(BlockImportWorkerMsg::ImportedBlocks(results)).ok().unwrap();
		assert_eq!(link_port.recv(), Ok(LinkMsg::BlockImported));

		// Send an unknown
		let results = vec![(Ok(BlockImportResult::ImportedUnknown(Default::default(), Default::default(), None)), Default::default())];
		let _ = result_sender.send(BlockImportWorkerMsg::ImportedBlocks(results)).ok().unwrap();
		assert_eq!(link_port.recv(), Ok(LinkMsg::BlockImported));

		// Send an unknown with peer and bad justification
		let peer_id = PeerId::random();
		let results = vec![(Ok(BlockImportResult::ImportedUnknown(Default::default(),
			ImportedAux {
				needs_justification: true,
				clear_justification_requests: false,
				bad_justification: true,
				needs_finality_proof: false,
			},
			Some(peer_id.clone()))), Default::default())];
		let _ = result_sender.send(BlockImportWorkerMsg::ImportedBlocks(results)).ok().unwrap();
		assert_eq!(link_port.recv(), Ok(LinkMsg::BlockImported));
		assert_eq!(link_port.recv(), Ok(LinkMsg::Disconnected));

		// Send an incomplete header
		let results = vec![(Err(BlockImportError::IncompleteHeader(Some(peer_id.clone()))), Default::default())];
		let _ = result_sender.send(BlockImportWorkerMsg::ImportedBlocks(results)).ok().unwrap();
		assert_eq!(link_port.recv(), Ok(LinkMsg::Disconnected));
		assert_eq!(link_port.recv(), Ok(LinkMsg::Restarted));

		// Send an unknown parent
		let results = vec![(Err(BlockImportError::UnknownParent), Default::default())];
		let _ = result_sender.send(BlockImportWorkerMsg::ImportedBlocks(results)).ok().unwrap();
		assert_eq!(link_port.recv(), Ok(LinkMsg::Restarted));

		// Send a verification failed
		let results = vec![(Err(BlockImportError::VerificationFailed(Some(peer_id.clone()), String::new())), Default::default())];
		let _ = result_sender.send(BlockImportWorkerMsg::ImportedBlocks(results)).ok().unwrap();
		assert_eq!(link_port.recv(), Ok(LinkMsg::Disconnected));
		assert_eq!(link_port.recv(), Ok(LinkMsg::Restarted));

		// Send an error
		let results = vec![(Err(BlockImportError::Error), Default::default())];
		let _ = result_sender.send(BlockImportWorkerMsg::ImportedBlocks(results)).ok().unwrap();
		assert_eq!(link_port.recv(), Ok(LinkMsg::Restarted));

		// Drop the importer sender first, ensuring graceful shutdown.
		drop(importer_sender);
	}

	#[test]
	fn process_finality_proof_import_result_works() {
		let (result_sender, result_port) = channel::unbounded();
		let (worker_sender, worker_receiver) = channel::unbounded();
		let (link_sender, link_port) = channel::unbounded();
		let importer_sender = BlockImporter::<Block>::new(result_port, worker_sender, Arc::new(()), None, None, None);
		let link = TestLink::new(link_sender);
		let (ack_sender, start_ack_port) = channel::bounded(4);
		let _ = importer_sender.send(BlockImportMsg::Start(Box::new(link.clone()), ack_sender));
		let who = Origin::random();

		// Ensure the importer handles Start before any result messages.
		start_ack_port.recv().unwrap().unwrap();

		// Send finality proof import request to BlockImporter
		importer_sender.send(BlockImportMsg::ImportFinalityProof(
			who.clone(),
			Default::default(),
			1,
			vec![42],
		)).unwrap();

		// Wait until this request is redirected to the BlockImportWorker
		match worker_receiver.recv().unwrap() {
			BlockImportWorkerMsg::ImportFinalityProof(
				cwho,
				chash,
				1,
				cproof,
			) => {
				assert_eq!(cwho, who);
				assert_eq!(chash, Default::default());
				assert_eq!(cproof, vec![42]);
			},
			_ => unreachable!("Unexpected work request received"),
		}

		// Send ack of proof import from BlockImportWorker to BlockImporter
		result_sender.send(BlockImportWorkerMsg::ImportedFinalityProof(
			who.clone(),
			(Default::default(), 0),
			Ok((Default::default(), 0)),
		)).unwrap();

		// Wait for finality proof import result
		assert_eq!(link_port.recv(), Ok(LinkMsg::FinalityProofImported));

		// Drop the importer sender first, ensuring graceful shutdown.
		drop(importer_sender);
	}
}

