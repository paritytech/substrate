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

use std::collections::{HashSet, VecDeque};
use std::sync::{Arc, Weak};
use std::sync::atomic::{AtomicBool, Ordering};
use parking_lot::{Condvar, Mutex, RwLock};
use network_libp2p::{NodeIndex, Severity};
use primitives::AuthorityId;

use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, NumberFor, Zero};

pub use blocks::BlockData;
use client::error::Error as ClientError;
use error::{ErrorKind, Error};
use protocol::Context;
use service::ExecuteInContext;
use sync::ChainSync;

pub use consensus::{ImportBlock, BlockImport, ImportResult, BlockOrigin};

/// Shared block import struct used by the queue.
pub type SharedBlockImport<B> = Arc<dyn BlockImport<B,Error=ClientError> + Send + Sync>;

#[cfg(any(test, feature = "test-helpers"))]
use std::cell::RefCell;

/// Verify a justification of a block
pub trait Verifier<B: BlockT>: Send + Sync + Sized {
	/// Verify the given data and return the ImportBlock and an optional
	/// new set of validators to import. If not, err with an Error-Message
	/// presented to the User in the logs.
	fn verify(
		&self,
		origin: BlockOrigin,
		header: B::Header,
		justification: Vec<u8>,
		body: Option<Vec<B::Extrinsic>>
	) -> Result<(ImportBlock<B>, Option<Vec<AuthorityId>>), String>;
}

/// Blocks import queue API.
pub trait ImportQueue<B: BlockT>: Send + Sync {
	/// Start background work for the queue as necessary.
	///
	/// This is called automatically by the network service when synchronization
	/// begins.
	fn start<L>(&self, _link: L) -> Result<(), Error> where
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
	fn import_blocks(&self, origin: BlockOrigin, blocks: Vec<BlockData<B>>);
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
struct AsyncImportQueueData<B: BlockT> {
	signal: Condvar,
	queue: Mutex<VecDeque<(BlockOrigin, Vec<BlockData<B>>)>>,
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
	fn new() -> Self {
		Self {
			signal: Default::default(),
			queue: Mutex::new(VecDeque::new()),
			queue_blocks: RwLock::new(HashSet::new()),
			best_importing_number: RwLock::new(Zero::zero()),
			is_stopping: Default::default(),
		}
	}
}

impl<B: BlockT, V: 'static + Verifier<B>> ImportQueue<B> for BasicQueue<B, V> {
	fn start<L: 'static + Link<B>>(
		&self,
		link: L,
	) -> Result<(), Error> {
		debug_assert!(self.handle.lock().is_none());

		let qdata = self.data.clone();
		let verifier = self.verifier.clone();
		let block_import = self.block_import.clone();
		*self.handle.lock() = Some(::std::thread::Builder::new().name("ImportQueue".into()).spawn(move || {
			import_thread(block_import, link, qdata, verifier)
		}).map_err(|err| Error::from(ErrorKind::Io(err)))?);
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
				self.data.is_stopping.store(true, Ordering::SeqCst);
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

	fn import_blocks(&self, origin: BlockOrigin, blocks: Vec<BlockData<B>>) {
		if blocks.is_empty() {
			return;
		}

		trace!(target:"sync", "Scheduling {} blocks for import", blocks.len());

		let mut queue = self.data.queue.lock();
		let mut queue_blocks = self.data.queue_blocks.write();
		let mut best_importing_number = self.data.best_importing_number.write();
		let new_best_importing_number = blocks.last().and_then(|b| b.block.header.as_ref().map(|h| h.number().clone())).unwrap_or_else(|| Zero::zero());
		queue_blocks.extend(blocks.iter().map(|b| b.block.hash.clone()));
		if new_best_importing_number > *best_importing_number {
			*best_importing_number = new_best_importing_number;
		}
		queue.push_back((origin, blocks));
		self.data.signal.notify_one();
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

		let blocks_hashes: Vec<B::Hash> = new_blocks.1.iter().map(|b| b.block.hash.clone()).collect();
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
	/// Maintain sync.
	fn maintain_sync(&self) { }
	/// Disconnect from peer.
	fn useless_peer(&self, _who: NodeIndex, _reason: &str) { }
	/// Disconnect from peer and restart sync.
	fn note_useless_and_restart_sync(&self, _who: NodeIndex, _reason: &str) { }
	/// Restart sync.
	fn restart(&self) { }
}

/// A link implementation that does nothing.
pub struct NoopLink;

impl<B: BlockT> Link<B> for NoopLink { }

/// A link implementation that connects to the network.
pub struct NetworkLink<B: BlockT, E: ExecuteInContext<B>> {
	/// The chain-sync handle
	pub(crate) sync: Weak<RwLock<ChainSync<B>>>,
	/// Network context.
	pub(crate) context: Weak<E>,
}

impl<B: BlockT, E: ExecuteInContext<B>> NetworkLink<B, E> {
	/// Execute closure with locked ChainSync.
	fn with_sync<F: Fn(&mut ChainSync<B>, &mut Context<B>)>(&self, closure: F) {
		if let (Some(sync), Some(service)) = (self.sync.upgrade(), self.context.upgrade()) {
			service.execute_in_context(move |protocol| {
				let mut sync = sync.write();
				closure(&mut *sync, protocol)
			});
		}
	}
}

impl<B: BlockT, E: ExecuteInContext<B>> Link<B> for NetworkLink<B, E> {
	fn block_imported(&self, hash: &B::Hash, number: NumberFor<B>) {
		self.with_sync(|sync, _| sync.block_imported(&hash, number))
	}

	fn maintain_sync(&self) {
		self.with_sync(|sync, protocol| sync.maintain_sync(protocol))
	}

	fn useless_peer(&self, who: NodeIndex, reason: &str) {
		self.with_sync(|_, protocol| protocol.report_peer(who, Severity::Useless(reason)))
	}

	fn note_useless_and_restart_sync(&self, who: NodeIndex, reason: &str) {
		self.with_sync(|sync, protocol| {
			protocol.report_peer(who, Severity::Useless(reason));	// is this actually malign or just useless?
			sync.restart(protocol);
		})
	}

	fn restart(&self) {
		self.with_sync(|sync, protocol| sync.restart(protocol))
	}
}

/// Block import successful result.
#[derive(Debug, PartialEq)]
enum BlockImportResult<H: ::std::fmt::Debug + PartialEq, N: ::std::fmt::Debug + PartialEq> {
	/// Imported known block.
	ImportedKnown(H, N),
	/// Imported unknown block.
	ImportedUnknown(H, N),
}

/// Block import error.
#[derive(Debug, PartialEq)]
enum BlockImportError {
	/// Block missed header, can't be imported
	IncompleteHeader(Option<NodeIndex>),
	/// Block missed justification, can't be imported
	IncompleteJustification(Option<NodeIndex>),
	/// Block verification failed, can't be imported
	VerificationFailed(Option<NodeIndex>, String),
	/// Block is known to be Bad
	BadBlock(Option<NodeIndex>),
	/// Block has an unknown parent
	UnknownParent,
	/// Other Error.
	Error,
}

/// Import a bunch of blocks.
fn import_many_blocks<'a, B: BlockT, V: Verifier<B>>(
	import_handle: &BlockImport<B, Error=ClientError>,
	link: &Link<B>,
	qdata: Option<&AsyncImportQueueData<B>>,
	blocks: (BlockOrigin, Vec<BlockData<B>>),
	verifier: Arc<V>
) -> bool
{
	let (blocks_origin, blocks) = blocks;
	let count = blocks.len();
	let mut imported = 0;

	let blocks_range = match (
			blocks.first().and_then(|b| b.block.header.as_ref().map(|h| h.number())),
			blocks.last().and_then(|b| b.block.header.as_ref().map(|h| h.number())),
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
fn import_single_block<B: BlockT, V: Verifier<B>>(
	import_handle: &BlockImport<B,Error=ClientError>,
	block_origin: BlockOrigin,
	block: BlockData<B>,
	verifier: Arc<V>
) -> Result<BlockImportResult<B::Hash, <<B as BlockT>::Header as HeaderT>::Number>, BlockImportError>
{
	let peer = block.origin;
	let block = block.block;

	let (header, justification) = match (block.header, block.justification) {
		(Some(header), Some(justification)) => (header, justification),
		(None, _) => {
			if let Some(peer) = peer {
				debug!(target: "sync", "Header {} was not provided by {} ", block.hash, peer);
			} else {
				debug!(target: "sync", "Header {} was not provided ", block.hash);
			}
			return Err(BlockImportError::IncompleteHeader(peer)) //TODO: use persistent ID
		},
		(_, None) => {
			if let Some(peer) = peer {
				debug!(target: "sync", "Justification set for block {} was not provided by {} ", block.hash, peer);
			} else {
				debug!(target: "sync", "Justification set for block {} was not provided", block.hash);
			}
			return Err(BlockImportError::IncompleteJustification(peer)) //TODO: use persistent ID
		}
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
		Ok(ImportResult::UnknownParent) => {
			debug!(target: "sync", "Block with unknown parent {}: {:?}, parent: {:?}", number, hash, parent);
			Err(BlockImportError::UnknownParent)
		},
		Ok(ImportResult::KnownBad) => {
			debug!(target: "sync", "Peer gave us a bad block {}: {:?}", number, hash);
			Err(BlockImportError::BadBlock(peer)) //TODO: use persistent ID
		}
		Err(e) => {
			debug!(target: "sync", "Error importing block {}: {:?}: {:?}", number, hash, e);
			Err(BlockImportError::Error)
		}
	}
}

/// Process single block import result.
fn process_import_result<B: BlockT>(
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
		Err(BlockImportError::IncompleteJustification(who)) => {
			if let Some(peer) = who {
				link.useless_peer(peer, "Sent block with incomplete justification to import");
			}
			0
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


#[cfg(any(test, feature = "test-helpers"))]
struct ImportCB<B: BlockT>(RefCell<Option<Box<dyn Fn(BlockOrigin, Vec<BlockData<B>>) -> bool>>>);

#[cfg(any(test, feature = "test-helpers"))]
impl<B: BlockT> ImportCB<B> {
	fn new() -> Self {
		ImportCB(RefCell::new(None))
	}
	fn set<F>(&self, cb: Box<F>)
		where F: 'static + Fn(BlockOrigin, Vec<BlockData<B>>) -> bool
	{
		*self.0.borrow_mut() = Some(cb);
	}
	fn call(&self, origin: BlockOrigin, data: Vec<BlockData<B>>) -> bool {
		let b = self.0.borrow();
		b.as_ref().expect("The Callback has been set before. qed.")(origin, data)
	}
}

#[cfg(any(test, feature = "test-helpers"))]
unsafe impl<B: BlockT> Send for ImportCB<B> {}
#[cfg(any(test, feature = "test-helpers"))]
unsafe impl<B: BlockT> Sync for ImportCB<B> {}


#[cfg(any(test, feature = "test-helpers"))]
/// A Verifier that accepts all blocks and passes them on with the configured
/// finality to be imported.
pub struct PassThroughVerifier(pub bool);

#[cfg(any(test, feature = "test-helpers"))]
/// This Verifiyer accepts all data as valid
impl<B: BlockT> Verifier<B> for PassThroughVerifier {
	fn verify(
		&self,
		origin: BlockOrigin,
		header: B::Header,
		justification: Vec<u8>,
		body: Option<Vec<B::Extrinsic>>
	) -> Result<(ImportBlock<B>, Option<Vec<AuthorityId>>), String> {
		Ok((ImportBlock {
			origin,
			header,
			body,
			finalized: self.0,
			justification: justification,
			post_digests: vec![],
			auxiliary: Vec::new(),
		}, None))
	}
}

/// Blocks import queue that is importing blocks in the same thread.
/// The boolean value indicates whether blocks should be imported without instant finality.
#[cfg(any(test, feature = "test-helpers"))]
pub struct SyncImportQueue<B: BlockT, V: Verifier<B>> {
	verifier: Arc<V>,
	link: ImportCB<B>,
	block_import: SharedBlockImport<B>,
}

#[cfg(any(test, feature = "test-helpers"))]
impl<B: 'static + BlockT, V: 'static + Verifier<B>> SyncImportQueue<B, V> {
	/// Create a new SyncImportQueue wrapping the given Verifier and block import
	/// handle.
	pub fn new(verifier: Arc<V>, block_import: SharedBlockImport<B>) -> Self {
		let queue = SyncImportQueue {
			verifier,
			link: ImportCB::new(),
			block_import,
		};

		let v = queue.verifier.clone();
		let import_handle = queue.block_import.clone();
		queue.link.set(Box::new(move |origin, new_blocks| {
			let verifier = v.clone();
			import_many_blocks(
				&*import_handle,
				&NoopLink,
				None,
				(origin, new_blocks),
				verifier,
			)
		}));

		queue
	}
}

#[cfg(any(test, feature = "test-helpers"))]
impl<B: 'static + BlockT, V: 'static + Verifier<B>> ImportQueue<B> for SyncImportQueue<B, V>
{
	fn start<L: 'static + Link<B>>(
		&self,
		link: L,
	) -> Result<(), Error> {
		let v = self.verifier.clone();
		let import_handle = self.block_import.clone();
		self.link.set(Box::new(move |origin, new_blocks| {
			let verifier = v.clone();
			import_many_blocks(
				&*import_handle,
				&link,
				None,
				(origin, new_blocks),
				verifier,
			)
		}));
		Ok(())
	}
	fn clear(&self) { }

	fn stop(&self) { }

	fn status(&self) -> ImportQueueStatus<B> {
		ImportQueueStatus {
			importing_count: 0,
			best_importing_number: Zero::zero(),
		}
	}

	fn is_importing(&self, _hash: &B::Hash) -> bool {
		false
	}

	fn import_blocks(&self, origin: BlockOrigin, blocks: Vec<BlockData<B>>) {
		self.link.call(origin, blocks);
	}
}

#[cfg(test)]
pub mod tests {
	use client;
	use message;
	use test_client::{self, TestClient};
	use test_client::runtime::{Block, Hash};
	use runtime_primitives::generic::BlockId;
	use std::cell::Cell;
	use super::*;

	struct TestLink {
		imported: Cell<usize>,
		maintains: Cell<usize>,
		disconnects: Cell<usize>,
		restarts: Cell<usize>,
	}

	impl TestLink {
		fn new() -> TestLink {
			TestLink {
				imported: Cell::new(0),
				maintains: Cell::new(0),
				disconnects: Cell::new(0),
				restarts: Cell::new(0),
			}
		}

		fn total(&self) -> usize {
			self.imported.get() + self.maintains.get() + self.disconnects.get() + self.restarts.get()
		}
	}

	impl Link<Block> for TestLink {
		fn block_imported(&self, _hash: &Hash, _number: NumberFor<Block>) {
			self.imported.set(self.imported.get() + 1);
		}
		fn maintain_sync(&self) {
			self.maintains.set(self.maintains.get() + 1);
		}
		fn useless_peer(&self, _: NodeIndex, _: &str) {
			self.disconnects.set(self.disconnects.get() + 1);
		}
		fn note_useless_and_restart_sync(&self, id: NodeIndex, r: &str) {
			self.useless_peer(id, r);
			self.restart();
		}
		fn restart(&self) {
			self.restarts.set(self.restarts.get() + 1);
		}
	}

	fn prepare_good_block() -> (client::Client<test_client::Backend, test_client::Executor, Block, test_client::runtime::RuntimeApi>, Hash, u64, BlockData<Block>) {
		let client = test_client::new();
		let block = client.new_block().unwrap().bake().unwrap();
		client.justify_and_import(BlockOrigin::File, block).unwrap();

		let (hash, number) = (client.block_hash(1).unwrap().unwrap(), 1);
		let block = message::BlockData::<Block> {
			hash: client.block_hash(1).unwrap().unwrap(),
			header: client.header(&BlockId::Number(1)).unwrap(),
			body: None,
			receipt: None,
			message_queue: None,
			justification: client.justification(&BlockId::Number(1)).unwrap(),
		};

		(client, hash, number, BlockData { block, origin: Some(0) })
	}

	#[test]
	fn import_single_good_block_works() {
		let (_, hash, number, block) = prepare_good_block();
		assert_eq!(
			import_single_block(&test_client::new(), BlockOrigin::File, block, Arc::new(PassThroughVerifier(true))),
			Ok(BlockImportResult::ImportedUnknown(hash, number))
		);
	}

	#[test]
	fn import_single_good_known_block_is_ignored() {
		let (client, hash, number, block) = prepare_good_block();
		assert_eq!(
			import_single_block(&client, BlockOrigin::File, block, Arc::new(PassThroughVerifier(true))),
			Ok(BlockImportResult::ImportedKnown(hash, number))
		);
	}

	#[test]
	fn import_single_good_block_without_header_fails() {
		let (_, _, _, mut block) = prepare_good_block();
		block.block.header = None;
		assert_eq!(
			import_single_block(&test_client::new(), BlockOrigin::File, block, Arc::new(PassThroughVerifier(true))),
			Err(BlockImportError::IncompleteHeader(Some(0)))
		);
	}

	#[test]
	fn import_single_good_block_without_justification_fails() {
		let (_, _, _, mut block) = prepare_good_block();
		block.block.justification = None;
		assert_eq!(
			import_single_block(&test_client::new(), BlockOrigin::File, block, Arc::new(PassThroughVerifier(true))),
			Err(BlockImportError::IncompleteJustification(Some(0)))
		);
	}

	#[test]
	fn process_import_result_works() {
		let link = TestLink::new();
		assert_eq!(process_import_result::<Block>(&link, Ok(BlockImportResult::ImportedKnown(Default::default(), 0))), 1);
		assert_eq!(link.total(), 1);

		let link = TestLink::new();
		assert_eq!(process_import_result::<Block>(&link, Ok(BlockImportResult::ImportedKnown(Default::default(), 0))), 1);
		assert_eq!(link.total(), 1);
		assert_eq!(link.imported.get(), 1);

		let link = TestLink::new();
		assert_eq!(process_import_result::<Block>(&link, Ok(BlockImportResult::ImportedUnknown(Default::default(), 0))), 1);
		assert_eq!(link.total(), 1);
		assert_eq!(link.imported.get(), 1);

		let link = TestLink::new();
		assert_eq!(process_import_result::<Block>(&link, Err(BlockImportError::IncompleteHeader(Some(0)))), 0);
		assert_eq!(link.total(), 1);
		assert_eq!(link.disconnects.get(), 1);

		let link = TestLink::new();
		assert_eq!(process_import_result::<Block>(&link, Err(BlockImportError::IncompleteJustification(Some(0)))), 0);
		assert_eq!(link.total(), 1);
		assert_eq!(link.disconnects.get(), 1);

		let link = TestLink::new();
		assert_eq!(process_import_result::<Block>(&link, Err(BlockImportError::UnknownParent)), 0);
		assert_eq!(link.total(), 1);
		assert_eq!(link.restarts.get(), 1);

		let link = TestLink::new();
		assert_eq!(process_import_result::<Block>(&link, Err(BlockImportError::Error)), 0);
		assert_eq!(link.total(), 1);
		assert_eq!(link.restarts.get(), 1);
	}

	#[test]
	fn import_many_blocks_stops_when_stopping() {
		let (_, _, _, block) = prepare_good_block();
		let qdata = AsyncImportQueueData::new();
		let verifier = Arc::new(PassThroughVerifier(true));
		qdata.is_stopping.store(true, Ordering::SeqCst);
		let client = test_client::new();
		assert!(!import_many_blocks(
			&client,
			&mut TestLink::new(),
			Some(&qdata),
			(BlockOrigin::File, vec![block.clone(), block]),
			verifier
		));
	}

	#[test]
	fn async_import_queue_drops() {
		// Perform this test multiple times since it exhibits non-deterministic behavior.
		for _ in 0..100 {
			let verifier = Arc::new(PassThroughVerifier(true));
			let queue = BasicQueue::new(verifier, Arc::new(test_client::new()));
			queue.start(TestLink::new()).unwrap();
			drop(queue);
		}
	}
}
