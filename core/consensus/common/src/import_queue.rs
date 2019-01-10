// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

use block_import::{ImportBlock, BlockImport, ImportResult, BlockOrigin};
use std::collections::{HashSet, VecDeque};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use parking_lot::{Condvar, Mutex, RwLock};

use runtime_primitives::Justification;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, NumberFor, Zero, AuthorityIdFor};

use error::Error as ConsensusError;

/// Shared block import struct used by the queue.
pub type SharedBlockImport<B> = Arc<dyn BlockImport<B, Error=ConsensusError> + Send + Sync>;

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
		body: Option<Vec<B::Extrinsic>>
	) -> Result<(ImportBlock<B>, Option<Vec<AuthorityIdFor<B>>>), String>;
}

/// Blocks import queue API.
pub trait ImportQueue<B: BlockT>: Send + Sync {
	/// Start background work for the queue as necessary.
	///
	/// This is called automatically by the network service when synchronization
	/// begins.
	fn start<L>(&self, _link: L) -> Result<(), std::io::Error> where
		Self: Sized,
		L: 'static + Link<B>,
	{
		Ok(())
	}
	/// Clear the queue when sync is restarting.
	fn clear(&self);
	/// Clears the import queue and stops importing.
	fn stop(&self);
	/// Get queue status.
	fn status(&self) -> ImportQueueStatus<B>;
	/// Is block with given hash currently in the queue.
	fn is_importing(&self, hash: &B::Hash) -> bool;
	/// Import bunch of blocks.
	fn import_blocks(&self, origin: BlockOrigin, blocks: Vec<IncomingBlock<B>>);
	/// Import a block justification.
	fn import_justification(&self, hash: B::Hash, number: NumberFor<B>, justification: Justification) -> bool;
}

/// Import queue status. It isn't completely accurate.
pub struct ImportQueueStatus<B: BlockT> {
	/// Number of blocks that are currently in the queue.
	pub importing_count: usize,
	/// The number of the best block that was ever in the queue since start/last failure.
	pub best_importing_number: <<B as BlockT>::Header as HeaderT>::Number,
}

/// Basic block import queue that is importing blocks sequentially in a separate thread,
/// with pluggable verification.
pub struct BasicQueue<B: BlockT, V: 'static + Verifier<B>> {
	handle: Mutex<Option<::std::thread::JoinHandle<()>>>,
	data: Arc<AsyncImportQueueData<B>>,
	verifier: Arc<V>,
	block_import: SharedBlockImport<B>,
}

/// Locks order: queue, queue_blocks, best_importing_number
pub struct AsyncImportQueueData<B: BlockT> {
	signal: Condvar,
	queue: Mutex<VecDeque<(BlockOrigin, Vec<IncomingBlock<B>>)>>,
	queue_blocks: RwLock<HashSet<B::Hash>>,
	best_importing_number: RwLock<<<B as BlockT>::Header as HeaderT>::Number>,
	is_stopping: AtomicBool,
}

impl<B: BlockT, V: Verifier<B>> BasicQueue<B, V> {
	/// Instantiate a new basic queue, with given verifier.
	pub fn new(verifier: Arc<V>, block_import: SharedBlockImport<B>) -> Self {
		Self {
			handle: Mutex::new(None),
			data: Arc::new(AsyncImportQueueData::new()),
			verifier,
			block_import,
		}
	}
}

impl<B: BlockT> AsyncImportQueueData<B> {
	/// Instantiate a new async import queue data.
	pub fn new() -> Self {
		Self {
			signal: Default::default(),
			queue: Mutex::new(VecDeque::new()),
			queue_blocks: RwLock::new(HashSet::new()),
			best_importing_number: RwLock::new(Zero::zero()),
			is_stopping: Default::default(),
		}
	}

	// Signals to stop importing new blocks.
	pub fn stop(&self) {
		self.is_stopping.store(true, Ordering::SeqCst);
	}
}

impl<B: BlockT, V: 'static + Verifier<B>> ImportQueue<B> for BasicQueue<B, V> {
	fn start<L: 'static + Link<B>>(
		&self,
		link: L,
	) -> Result<(), std::io::Error> {
		debug_assert!(self.handle.lock().is_none());

		let qdata = self.data.clone();
		let verifier = self.verifier.clone();
		let block_import = self.block_import.clone();
		*self.handle.lock() = Some(::std::thread::Builder::new().name("ImportQueue".into()).spawn(move || {
			import_thread(block_import, link, qdata, verifier)
		})?);
		Ok(())
	}

	fn clear(&self) {
		let mut queue = self.data.queue.lock();
		let mut queue_blocks = self.data.queue_blocks.write();
		let mut best_importing_number = self.data.best_importing_number.write();
		queue_blocks.clear();
		queue.clear();
		*best_importing_number = Zero::zero();
	}

	fn stop(&self) {
		self.clear();
		if let Some(handle) = self.handle.lock().take() {
			{
				// Perform storing the stop flag and signalling under a single lock.
				let _queue_lock = self.data.queue.lock();
				self.data.stop();
				self.data.signal.notify_one();
			}

			let _ = handle.join();
		}
	}

	fn status(&self) -> ImportQueueStatus<B> {
		ImportQueueStatus {
			importing_count: self.data.queue_blocks.read().len(),
			best_importing_number: *self.data.best_importing_number.read(),
		}
	}

	fn is_importing(&self, hash: &B::Hash) -> bool {
		self.data.queue_blocks.read().contains(hash)
	}

	fn import_blocks(&self, origin: BlockOrigin, blocks: Vec<IncomingBlock<B>>) {
		if blocks.is_empty() {
			return;
		}

		trace!(target:"sync", "Scheduling {} blocks for import", blocks.len());

		let mut queue = self.data.queue.lock();
		let mut queue_blocks = self.data.queue_blocks.write();
		let mut best_importing_number = self.data.best_importing_number.write();
		let new_best_importing_number = blocks.last().and_then(|b| b.header.as_ref().map(|h| h.number().clone())).unwrap_or_else(|| Zero::zero());
		queue_blocks.extend(blocks.iter().map(|b| b.hash.clone()));
		if new_best_importing_number > *best_importing_number {
			*best_importing_number = new_best_importing_number;
		}
		queue.push_back((origin, blocks));
		self.data.signal.notify_one();
	}

	fn import_justification(&self, hash: B::Hash, number: NumberFor<B>, justification: Justification) -> bool {
		self.block_import.import_justification(hash, number, justification).is_ok()
	}
}

impl<B: BlockT, V: 'static + Verifier<B>> Drop for BasicQueue<B, V> {
	fn drop(&mut self) {
		self.stop();
	}
}

/// Blocks import thread.
fn import_thread<B: BlockT, L: Link<B>, V: Verifier<B>>(
	block_import: SharedBlockImport<B>,
	link: L,
	qdata: Arc<AsyncImportQueueData<B>>,
	verifier: Arc<V>
) {
	trace!(target: "sync", "Starting import thread");
	loop {
		let new_blocks = {
			let mut queue_lock = qdata.queue.lock();

			// We are holding the same lock that `stop` takes so here we either see that stop flag
			// is active or wait for the signal. The latter one unlocks the mutex and this gives a chance
			// to `stop` to generate the signal.
			if qdata.is_stopping.load(Ordering::SeqCst) {
				break;
			}
			if queue_lock.is_empty() {
				qdata.signal.wait(&mut queue_lock);
			}

			match queue_lock.pop_front() {
				Some(new_blocks) => new_blocks,
				None => break,
			}
		};

		let blocks_hashes: Vec<B::Hash> = new_blocks.1.iter().map(|b| b.hash.clone()).collect();
		if !import_many_blocks(
			&*block_import,
			&link,
			Some(&*qdata),
			new_blocks,
			verifier.clone(),
		) {
			break;
		}

		let mut queue_blocks = qdata.queue_blocks.write();
		for blocks_hash in blocks_hashes {
			queue_blocks.remove(&blocks_hash);
		}
	}

	trace!(target: "sync", "Stopping import thread");
}

/// Hooks that the verification queue can use to influence the synchronization
/// algorithm.
pub trait Link<B: BlockT>: Send {
	/// Block imported.
	fn block_imported(&self, _hash: &B::Hash, _number: NumberFor<B>) { }
	/// Request a justification for the given block.
	fn request_justification(&self, _hash: &B::Hash, _number: NumberFor<B>) { }
	/// Maintain sync.
	fn maintain_sync(&self) { }
	/// Disconnect from peer.
	fn useless_peer(&self, _who: Origin, _reason: &str) { }
	/// Disconnect from peer and restart sync.
	fn note_useless_and_restart_sync(&self, _who: Origin, _reason: &str) { }
	/// Restart sync.
	fn restart(&self) { }
}

/// Block import successful result.
#[derive(Debug, PartialEq)]
pub enum BlockImportResult<H: ::std::fmt::Debug + PartialEq, N: ::std::fmt::Debug + PartialEq> {
	/// Imported known block.
	ImportedKnown(H, N),
	/// Imported unknown block.
	ImportedUnknown(H, N),
	/// Imported unknown block.
	ImportedUnjustified(H, N),
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

/// Import a bunch of blocks.
pub fn import_many_blocks<'a, B: BlockT, V: Verifier<B>>(
	import_handle: &BlockImport<B, Error=ConsensusError>,
	link: &Link<B>,
	qdata: Option<&AsyncImportQueueData<B>>,
	blocks: (BlockOrigin, Vec<IncomingBlock<B>>),
	verifier: Arc<V>
) -> bool
{
	let (blocks_origin, blocks) = blocks;
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
	trace!(target:"sync", "Starting import of {} blocks {}", count, blocks_range);

	// Blocks in the response/drain should be in ascending order.
	for block in blocks {
		let import_result = import_single_block(
			import_handle,
			blocks_origin.clone(),
			block,
			verifier.clone(),
		);
		let is_import_failed = import_result.is_err();
		imported += process_import_result(link, import_result);
		if is_import_failed {
			qdata.map(|qdata| *qdata.best_importing_number.write() = Zero::zero());
			return true;
		}

		if qdata.map(|qdata| qdata.is_stopping.load(Ordering::SeqCst)).unwrap_or_default() {
			return false;
		}
	}

	trace!(target: "sync", "Imported {} of {}", imported, count);
	link.maintain_sync();
	true
}

/// Single block import function.
pub fn import_single_block<B: BlockT, V: Verifier<B>>(
	import_handle: &BlockImport<B,Error=ConsensusError>,
	block_origin: BlockOrigin,
	block: IncomingBlock<B>,
	verifier: Arc<V>
) -> Result<BlockImportResult<B::Hash, <<B as BlockT>::Header as HeaderT>::Number>, BlockImportError>
{
	let peer = block.origin;

	let (header, justification) = match (block.header, block.justification) {
		(Some(header), justification) => (header, justification),
		(None, _) => {
			if let Some(peer) = peer {
				debug!(target: "sync", "Header {} was not provided by {} ", block.hash, peer);
			} else {
				debug!(target: "sync", "Header {} was not provided ", block.hash);
			}
			return Err(BlockImportError::IncompleteHeader(peer)) //TODO: use persistent ID
		},
	};

	let number = header.number().clone();
	let hash = header.hash();
	let parent = header.parent_hash().clone();
	let (import_block, new_authorities) = verifier.verify(block_origin, header, justification, block.body)
		.map_err(|msg| {
			if let Some(peer) = peer {
				trace!(target: "sync", "Verifying {}({}) from {} failed: {}", number, hash, peer, msg);
			} else {
				trace!(target: "sync", "Verifying {}({}) failed: {}", number, hash, msg);
			}
			BlockImportError::VerificationFailed(peer, msg)
		})?;

	match import_handle.import_block(import_block, new_authorities) {
		Ok(ImportResult::AlreadyInChain) => {
			trace!(target: "sync", "Block already in chain {}: {:?}", number, hash);
			Ok(BlockImportResult::ImportedKnown(hash, number))
		},
		Ok(ImportResult::AlreadyQueued) => {
			trace!(target: "sync", "Block already queued {}: {:?}", number, hash);
			Ok(BlockImportResult::ImportedKnown(hash, number))
		},
		Ok(ImportResult::Queued) => {
			trace!(target: "sync", "Block queued {}: {:?}", number, hash);
			Ok(BlockImportResult::ImportedUnknown(hash, number))
		},
		Ok(ImportResult::NeedsJustification) => {
			trace!(target: "sync", "Block queued but requires justification {}: {:?}", number, hash);
			Ok(BlockImportResult::ImportedUnjustified(hash, number))
		},
		Ok(ImportResult::UnknownParent) => {
			debug!(target: "sync", "Block with unknown parent {}: {:?}, parent: {:?}", number, hash, parent);
			Err(BlockImportError::UnknownParent)
		},
		Ok(ImportResult::KnownBad) => {
			debug!(target: "sync", "Peer gave us a bad block {}: {:?}", number, hash);
			Err(BlockImportError::BadBlock(peer)) //TODO: use persistent ID
		},
		Err(e) => {
			debug!(target: "sync", "Error importing block {}: {:?}: {:?}", number, hash, e);
			Err(BlockImportError::Error)
		}
	}
}

/// Process single block import result.
pub fn process_import_result<B: BlockT>(
	link: &Link<B>,
	result: Result<BlockImportResult<B::Hash, <<B as BlockT>::Header as HeaderT>::Number>, BlockImportError>
) -> usize
{
	match result {
		Ok(BlockImportResult::ImportedKnown(hash, number)) => {
			link.block_imported(&hash, number);
			1
		},
		Ok(BlockImportResult::ImportedUnknown(hash, number)) => {
			link.block_imported(&hash, number);
			1
		},
		Ok(BlockImportResult::ImportedUnjustified(hash, number)) => {
			link.block_imported(&hash, number);
			link.request_justification(&hash, number);
			1
		},
		Err(BlockImportError::IncompleteHeader(who)) => {
			if let Some(peer) = who {
				link.useless_peer(peer, "Sent block with incomplete header to import");
			}
			0
		},
		Err(BlockImportError::VerificationFailed(who, e)) => {
			if let Some(peer) = who {
				link.useless_peer(peer, &format!("Verification failed: {}", e));
			}
			0
		},
		Err(BlockImportError::BadBlock(who)) => {
			if let Some(peer) = who {
				link.note_useless_and_restart_sync(peer, "Sent us a bad block");
			}
			0
		},
		Err(BlockImportError::UnknownParent) | Err(BlockImportError::Error) => {
			link.restart();
			0
		},
	}
}
