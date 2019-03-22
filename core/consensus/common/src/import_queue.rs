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
//! and import. Each mode of consensus will have its own requirements for block verification.
//! Some algorithms can verify in parallel, while others only sequentially.
//!
//! The `ImportQueue` trait allows such verification strategies to be instantiated.
//! The `BasicQueue` and `BasicVerifier` traits allow serial queues to be
//! instantiated simply.

use crate::block_import::{
	BlockImport, BlockOrigin, ImportBlock, ImportedAux, ImportResult, JustificationImport,
};
use crossbeam_channel::{self as channel, Receiver, Sender};

use std::sync::Arc;
use std::thread;

use runtime_primitives::traits::{
	AuthorityIdFor, Block as BlockT, Header as HeaderT, NumberFor
};
use runtime_primitives::Justification;

use crate::error::Error as ConsensusError;

/// Shared block import struct used by the queue.
pub type SharedBlockImport<B> = Arc<dyn BlockImport<B, Error = ConsensusError> + Send + Sync>;

/// Shared justification import struct used by the queue.
pub type SharedJustificationImport<B> = Arc<dyn JustificationImport<B, Error=ConsensusError> + Send + Sync>;

/// Maps to the Origin used by the network.
pub type Origin = usize;

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
pub trait Verifier<B: BlockT>: Send + Sync + Sized {
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
pub trait ImportQueue<B: BlockT>: Send + Sync + ImportQueueClone<B> {
	/// Start background work for the queue as necessary.
	///
	/// This is called automatically by the network service when synchronization
	/// begins.
	fn start(&self, _link: Box<Link<B>>) -> Result<(), std::io::Error> {
		Ok(())
	}
	/// Clears the import queue and stops importing.
	fn stop(&self);
	/// Import bunch of blocks.
	fn import_blocks(&self, origin: BlockOrigin, blocks: Vec<IncomingBlock<B>>);
	/// Import a block justification.
	fn import_justification(&self, who: Origin, hash: B::Hash, number: NumberFor<B>, justification: Justification);
}

pub trait ImportQueueClone<B: BlockT> {
	fn clone_box(&self) -> Box<ImportQueue<B>>;
}

impl<B: BlockT> Clone for Box<ImportQueue<B>> {
	fn clone(&self) -> Box<ImportQueue<B>> {
		self.clone_box()
	}
}

/// Interface to a basic block import queue that is importing blocks sequentially in a separate thread,
/// with pluggable verification.
#[derive(Clone)]
pub struct BasicQueue<B: BlockT> {
	sender: Sender<BlockImportMsg<B>>,
}

impl<B: BlockT> ImportQueueClone<B> for BasicQueue<B> {
	fn clone_box(&self) -> Box<ImportQueue<B>> {
		Box::new(self.clone())
	}
}

/// "BasicQueue" is a wrapper around a channel sender to the "BlockImporter".
/// "BasicQueue" itself does not keep any state or do any importing work, and can therefore be send to other threads.
///
/// "BasicQueue" implements "ImportQueue" by sending messages to the "BlockImporter", which runs in it's own thread.
///
/// The "BlockImporter" is responsible for handling incoming requests from the "BasicQueue",
/// some of these requests are handled by the "BlockImporter" itself, such as "is_importing" or "status",
/// and justifications are also imported by the "BlockImporter".
///
/// The "import block" work will be offloaded to a single "BlockImportWorker", running in another thread.
/// Offloading the work is done via a channel,
/// ensuring blocks in this implementation are imported sequentially and in order(as received by the "BlockImporter")
///
/// As long as the "BasicQueue" is not dropped, the "BlockImporter" will keep running.
/// The "BlockImporter" owns a sender to the "BlockImportWorker", ensuring that the worker is kept alive until that sender is dropped.
impl<B: BlockT> BasicQueue<B> {
	/// Instantiate a new basic queue, with given verifier.
	pub fn new<V: 'static + Verifier<B>>(
		verifier: Arc<V>,
		block_import: SharedBlockImport<B>,
		justification_import: Option<SharedJustificationImport<B>>
	) -> Self {
		let (result_sender, result_port) = channel::unbounded();
		let worker_sender = BlockImportWorker::new(result_sender, verifier, block_import);
		let importer_sender = BlockImporter::new(result_port, worker_sender, justification_import);

		Self {
			sender: importer_sender,
		}
	}
}

impl<B: BlockT> ImportQueue<B> for BasicQueue<B> {
	fn start(&self, link: Box<Link<B>>) -> Result<(), std::io::Error> {
		let (sender, port) = channel::unbounded();
		let _ = self
			.sender
			.send(BlockImportMsg::Start(link, sender))
			.expect("1. self is holding a sender to the Importer, 2. Importer should handle messages while there are senders around; qed");
		port.recv().expect("1. self is holding a sender to the Importer, 2. Importer should handle messages while there are senders around; qed")
	}

	fn stop(&self) {
		let _ = self
			.sender
			.send(BlockImportMsg::Stop)
			.expect("1. self is holding a sender to the Importer, 2. Importer should handle messages while there are senders around; qed");
	}

	fn import_blocks(&self, origin: BlockOrigin, blocks: Vec<IncomingBlock<B>>) {
		if blocks.is_empty() {
			return;
		}
		let _ = self
			.sender
			.send(BlockImportMsg::ImportBlocks(origin, blocks))
			.expect("1. self is holding a sender to the Importer, 2. Importer should handle messages while there are senders around; qed");
	}

	fn import_justification(&self, who: Origin, hash: B::Hash, number: NumberFor<B>, justification: Justification) {
		let _ = self
			.sender
			.send(BlockImportMsg::ImportJustification(who, hash, number, justification))
			.expect("1. self is holding a sender to the Importer, 2. Importer should handle messages while there are senders around; qed");
	}
}

pub enum BlockImportMsg<B: BlockT> {
	ImportBlocks(BlockOrigin, Vec<IncomingBlock<B>>),
	ImportJustification(Origin, B::Hash, NumberFor<B>, Justification),
	Start(Box<Link<B>>, Sender<Result<(), std::io::Error>>),
	Stop,
}

pub enum BlockImportWorkerMsg<B: BlockT> {
	ImportBlocks(BlockOrigin, Vec<IncomingBlock<B>>),
	Imported(
		Vec<(
			Result<BlockImportResult<NumberFor<B>>, BlockImportError>,
			B::Hash,
		)>,
	),
}

enum ImportMsgType<B: BlockT> {
	FromWorker(BlockImportWorkerMsg<B>),
	FromNetwork(BlockImportMsg<B>),
}

struct BlockImporter<B: BlockT> {
	port: Receiver<BlockImportMsg<B>>,
	result_port: Receiver<BlockImportWorkerMsg<B>>,
	worker_sender: Sender<BlockImportWorkerMsg<B>>,
	link: Option<Box<dyn Link<B>>>,
	justification_import: Option<SharedJustificationImport<B>>,
}

impl<B: BlockT> BlockImporter<B> {
	fn new(
		result_port: Receiver<BlockImportWorkerMsg<B>>,
		worker_sender: Sender<BlockImportWorkerMsg<B>>,
		justification_import: Option<SharedJustificationImport<B>>,
	) -> Sender<BlockImportMsg<B>> {
		let (sender, port) = channel::bounded(4);
		let _ = thread::Builder::new()
			.name("ImportQueue".into())
			.spawn(move || {
				let mut importer = BlockImporter {
					port,
					result_port,
					worker_sender,
					link: None,
					justification_import,
				};
				while importer.run() {
					// Importing until all senders have been dropped...
				}
			})
			.expect("ImportQueue thread spawning failed");
		sender
	}

	fn run(&mut self) -> bool {
		let msg = select! {
			recv(self.port) -> msg => {
				match msg {
					// Our sender has been dropped, quitting.
					Err(_) => return false,
					Ok(msg) => ImportMsgType::FromNetwork(msg)
				}
			},
			recv(self.result_port) -> msg => {
				match msg {
					Err(_) => unreachable!("1. We hold a sender to the Worker, 2. it should not quit until that sender is dropped; qed"),
					Ok(msg) => ImportMsgType::FromWorker(msg),
				}
			}
		};
		match msg {
			ImportMsgType::FromNetwork(msg) => self.handle_network_msg(msg),
			ImportMsgType::FromWorker(msg) => self.handle_worker_msg(msg),
		}
	}

	fn handle_network_msg(&mut self, msg: BlockImportMsg<B>) -> bool {
		match msg {
			BlockImportMsg::ImportBlocks(origin, incoming_blocks) => {
				self.handle_import_blocks(origin, incoming_blocks)
			},
			BlockImportMsg::ImportJustification(who, hash, number, justification) => {
				self.handle_import_justification(who, hash, number, justification)
			},
			BlockImportMsg::Start(link, sender) => {
				if let Some(justification_import) = self.justification_import.as_ref() {
					justification_import.on_start(&*link);
				}
				self.link = Some(link);
				let _ = sender.send(Ok(()));
			},
			BlockImportMsg::Stop => return false,
		}
		true
	}

	fn handle_worker_msg(&mut self, msg: BlockImportWorkerMsg<B>) -> bool {
		let results = match msg {
			BlockImportWorkerMsg::Imported(results) => (results),
			_ => unreachable!("Import Worker does not send ImportBlocks message; qed"),
		};
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

			let link = match self.link.as_ref() {
				Some(link) => link,
				None => {
					trace!(target: "sync", "Received import result for {} while import-queue has no link", hash);
					return true;
				},
			};

			match result {
				Ok(BlockImportResult::ImportedKnown(number)) => link.block_imported(&hash, number),
				Ok(BlockImportResult::ImportedUnknown(number, aux, who)) => {
					link.block_imported(&hash, number);

					if aux.clear_justification_requests {
						trace!(target: "sync", "Block imported clears all pending justification requests {}: {:?}", number, hash);
						link.clear_justification_requests();
					}

					if aux.needs_justification {
						trace!(target: "sync", "Block imported but requires justification {}: {:?}", number, hash);
						link.request_justification(&hash, number);
					}

					if aux.bad_justification {
						if let Some(peer) = who {
							link.useless_peer(peer, "Sent block with bad justification to import");
						}
					}
				},
				Err(BlockImportError::IncompleteHeader(who)) => {
					if let Some(peer) = who {
						link.note_useless_and_restart_sync(peer, "Sent block with incomplete header to import");
					}
				},
				Err(BlockImportError::VerificationFailed(who, e)) => {
					if let Some(peer) = who {
						link.note_useless_and_restart_sync(peer, &format!("Verification failed: {}", e));
					}
				},
				Err(BlockImportError::BadBlock(who)) => {
					if let Some(peer) = who {
						link.note_useless_and_restart_sync(peer, "Sent us a bad block");
					}
				},
				Err(BlockImportError::UnknownParent) | Err(BlockImportError::Error) => {
					link.restart();
				},
			};
		}
		if let Some(link) = self.link.as_ref() {
			link.blocks_processed(hashes, has_error);
		}
		true
	}

	fn handle_import_justification(&self, who: Origin, hash: B::Hash, number: NumberFor<B>, justification: Justification) {
		let success = self.justification_import.as_ref().map(|justification_import| {
			justification_import.import_justification(hash, number, justification)
				.map_err(|e| {
					debug!(target: "sync", "Justification import failed with {:?} for hash: {:?} number: {:?} coming from node: {:?}", e, hash, number, who);
					e
				}).is_ok()
		}).unwrap_or(false);

		if let Some(link) = self.link.as_ref() {
			link.justification_imported(who, &hash, number, success);
		}
	}

	fn handle_import_blocks(&mut self, origin: BlockOrigin, blocks: Vec<IncomingBlock<B>>) {
		trace!(target: "sync", "Scheduling {} blocks for import", blocks.len());
		self.worker_sender
			.send(BlockImportWorkerMsg::ImportBlocks(origin, blocks))
			.expect("1. This is holding a sender to the worker, 2. the worker should not quit while a sender is still held; qed");
	}
}

struct BlockImportWorker<B: BlockT, V: Verifier<B>> {
	result_sender: Sender<BlockImportWorkerMsg<B>>,
	block_import: SharedBlockImport<B>,
	verifier: Arc<V>,
}

impl<B: BlockT, V: 'static + Verifier<B>> BlockImportWorker<B, V> {
	pub fn new(
		result_sender: Sender<BlockImportWorkerMsg<B>>,
		verifier: Arc<V>,
		block_import: SharedBlockImport<B>,
	) -> Sender<BlockImportWorkerMsg<B>> {
		let (sender, port) = channel::bounded(4);
		let _ = thread::Builder::new()
			.name("ImportQueueWorker".into())
			.spawn(move || {
				let worker = BlockImportWorker {
					result_sender,
					verifier,
					block_import,
				};
				for msg in port.iter() {
					// Working until all senders have been dropped...
					match msg {
						BlockImportWorkerMsg::ImportBlocks(origin, blocks) => {
							worker.import_a_batch_of_blocks(origin, blocks)
						}
						_ => unreachable!("Import Worker does not receive the Imported message; qed"),
					}
				}
			})
			.expect("ImportQueueWorker thread spawning failed");
		sender
	}

	fn import_a_batch_of_blocks(&self, origin: BlockOrigin, blocks: Vec<IncomingBlock<B>>) {
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
			let import_result = if has_error {
				Err(BlockImportError::Error)
			} else {
				import_single_block(
					&*self.block_import,
					origin.clone(),
					block.clone(),
					self.verifier.clone(),
				)
			};
			let was_ok = import_result.is_ok();
			results.push((import_result, block.hash));
			if was_ok {
				imported += 1;
			} else {
				has_error = true;
			}
		}

		let _ = self
			.result_sender
			.send(BlockImportWorkerMsg::Imported(results));

		trace!(target: "sync", "Imported {} of {}", imported, count);
	}
}

/// Hooks that the verification queue can use to influence the synchronization
/// algorithm.
pub trait Link<B: BlockT>: Send {
	/// Block imported.
	fn block_imported(&self, _hash: &B::Hash, _number: NumberFor<B>) {}
	/// Batch of blocks imported, with or without error.
	fn blocks_processed(&self, _processed_blocks: Vec<B::Hash>, _has_error: bool) {}
	/// Justification import result.
	fn justification_imported(&self, _who: Origin, _hash: &B::Hash, _number: NumberFor<B>, _success: bool) {}
	/// Clear all pending justification requests.
	fn clear_justification_requests(&self) {}
	/// Request a justification for the given block.
	fn request_justification(&self, _hash: &B::Hash, _number: NumberFor<B>) {}
	/// Disconnect from peer.
	fn useless_peer(&self, _who: Origin, _reason: &str) {}
	/// Disconnect from peer and restart sync.
	fn note_useless_and_restart_sync(&self, _who: Origin, _reason: &str) {}
	/// Restart sync.
	fn restart(&self) {}
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

/// Single block import function.
pub fn import_single_block<B: BlockT, V: Verifier<B>>(
	import_handle: &BlockImport<B, Error = ConsensusError>,
	block_origin: BlockOrigin,
	block: IncomingBlock<B>,
	verifier: Arc<V>,
) -> Result<BlockImportResult<NumberFor<B>>, BlockImportError> {
	let peer = block.origin;

	let (header, justification) = match (block.header, block.justification) {
		(Some(header), justification) => (header, justification),
		(None, _) => {
			if let Some(peer) = peer {
				debug!(target: "sync", "Header {} was not provided by {} ", block.hash, peer);
			} else {
				debug!(target: "sync", "Header {} was not provided ", block.hash);
			}
			return Err(BlockImportError::IncompleteHeader(peer))
		},
	};

	let number = header.number().clone();
	let hash = header.hash();
	let parent = header.parent_hash().clone();

	let import_error = |e| {
		match e {
			Ok(ImportResult::AlreadyInChain) => {
				trace!(target: "sync", "Block already in chain {}: {:?}", number, hash);
				Ok(BlockImportResult::ImportedKnown(number))
			},
			Ok(ImportResult::Imported(aux)) => Ok(BlockImportResult::ImportedUnknown(number, aux, peer)),
			Ok(ImportResult::UnknownParent) => {
				debug!(target: "sync", "Block with unknown parent {}: {:?}, parent: {:?}", number, hash, parent);
				Err(BlockImportError::UnknownParent)
			},
			Ok(ImportResult::KnownBad) => {
				debug!(target: "sync", "Peer gave us a bad block {}: {:?}", number, hash);
				Err(BlockImportError::BadBlock(peer))
			},
			Err(e) => {
				debug!(target: "sync", "Error importing block {}: {:?}: {:?}", number, hash, e);
				Err(BlockImportError::Error)
			}
		}
	};

	match import_error(import_handle.check_block(hash, parent))? {
		BlockImportResult::ImportedUnknown { .. } => (),
		r @ _ => return Ok(r), // Any other successfull result means that the block is already imported.
	}

	let (import_block, new_authorities) = verifier.verify(block_origin, header, justification, block.body)
		.map_err(|msg| {
			if let Some(peer) = peer {
				trace!(target: "sync", "Verifying {}({}) from {} failed: {}", number, hash, peer, msg);
			} else {
				trace!(target: "sync", "Verifying {}({}) failed: {}", number, hash, msg);
			}
			BlockImportError::VerificationFailed(peer, msg)
		})?;

	import_error(import_handle.import_block(import_block, new_authorities))
}

#[cfg(test)]
mod tests {
	use super::*;
	use test_client::runtime::{Block, Hash};

	#[derive(Debug, PartialEq)]
	enum LinkMsg {
		BlockImported,
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
		fn block_imported(&self, _hash: &Hash, _number: NumberFor<Block>) {
			let _ = self.sender.send(LinkMsg::BlockImported);
		}
		fn useless_peer(&self, _: Origin, _: &str) {
			let _ = self.sender.send(LinkMsg::Disconnected);
		}
		fn note_useless_and_restart_sync(&self, id: Origin, r: &str) {
			self.useless_peer(id, r);
			self.restart();
		}
		fn restart(&self) {
			let _ = self.sender.send(LinkMsg::Restarted);
		}
	}

	#[test]
	fn process_import_result_works() {
		let (result_sender, result_port) = channel::unbounded();
		let (worker_sender, _) = channel::unbounded();
		let (link_sender, link_port) = channel::unbounded();
		let importer_sender = BlockImporter::<Block>::new(result_port, worker_sender, None);
		let link = TestLink::new(link_sender);
		let (ack_sender, start_ack_port) = channel::bounded(4);
		let _ = importer_sender.send(BlockImportMsg::Start(Box::new(link.clone()), ack_sender));

		// Ensure the importer handles Start before any result messages.
		let _ = start_ack_port.recv();

		// Send a known
		let results = vec![(Ok(BlockImportResult::ImportedKnown(Default::default())), Default::default())];
		let _ = result_sender.send(BlockImportWorkerMsg::Imported(results)).ok().unwrap();
		assert_eq!(link_port.recv(), Ok(LinkMsg::BlockImported));

		// Send a second known
		let results = vec![(Ok(BlockImportResult::ImportedKnown(Default::default())), Default::default())];
		let _ = result_sender.send(BlockImportWorkerMsg::Imported(results)).ok().unwrap();
		assert_eq!(link_port.recv(), Ok(LinkMsg::BlockImported));

		// Send an unknown
		let results = vec![(Ok(BlockImportResult::ImportedUnknown(Default::default(), Default::default(), None)), Default::default())];
		let _ = result_sender.send(BlockImportWorkerMsg::Imported(results)).ok().unwrap();
		assert_eq!(link_port.recv(), Ok(LinkMsg::BlockImported));

		// Send an unknown with peer and bad justification
		let results = vec![(Ok(BlockImportResult::ImportedUnknown(Default::default(),
			ImportedAux { needs_justification: true, clear_justification_requests: false, bad_justification: true },
			Some(0))), Default::default())];
		let _ = result_sender.send(BlockImportWorkerMsg::Imported(results)).ok().unwrap();
		assert_eq!(link_port.recv(), Ok(LinkMsg::BlockImported));
		assert_eq!(link_port.recv(), Ok(LinkMsg::Disconnected));

		// Send an incomplete header
		let results = vec![(Err(BlockImportError::IncompleteHeader(Some(Default::default()))), Default::default())];
		let _ = result_sender.send(BlockImportWorkerMsg::Imported(results)).ok().unwrap();
		assert_eq!(link_port.recv(), Ok(LinkMsg::Disconnected));
		assert_eq!(link_port.recv(), Ok(LinkMsg::Restarted));

		// Send an unknown parent
		let results = vec![(Err(BlockImportError::UnknownParent), Default::default())];
		let _ = result_sender.send(BlockImportWorkerMsg::Imported(results)).ok().unwrap();
		assert_eq!(link_port.recv(), Ok(LinkMsg::Restarted));

		// Send a verification failed
		let results = vec![(Err(BlockImportError::VerificationFailed(Some(0), String::new())), Default::default())];
		let _ = result_sender.send(BlockImportWorkerMsg::Imported(results)).ok().unwrap();
		assert_eq!(link_port.recv(), Ok(LinkMsg::Disconnected));
		assert_eq!(link_port.recv(), Ok(LinkMsg::Restarted));

		// Send an error
		let results = vec![(Err(BlockImportError::Error), Default::default())];
		let _ = result_sender.send(BlockImportWorkerMsg::Imported(results)).ok().unwrap();
		assert_eq!(link_port.recv(), Ok(LinkMsg::Restarted));

		// Drop the importer sender first, ensuring graceful shutdown.
		drop(importer_sender);
	}
}

