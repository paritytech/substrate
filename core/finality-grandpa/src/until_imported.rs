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

//! Helper stream for waiting until one or more blocks are imported before
//! passing through inner items. This is done in a generic way to support
//! many different kinds of items.
//!
//! This is used for votes and commit messages currently.

use super::{BlockStatus, Error, SignedMessage, CompactCommit};

use log::{debug, warn};
use client::ImportNotifications;
use futures::prelude::*;
use futures::stream::Fuse;
use parking_lot::Mutex;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, NumberFor};
use substrate_primitives::ed25519::Public as AuthorityId;
use tokio::timer::Interval;

use std::collections::{HashMap, VecDeque};
use std::sync::{atomic::{AtomicUsize, Ordering}, Arc};
use std::time::{Duration, Instant};

const LOG_PENDING_INTERVAL: Duration = Duration::from_secs(15);

// something which will block until imported.
pub(crate) trait BlockUntilImported<Block: BlockT>: Sized {
	// the type that is blocked on.
	type Blocked;

	/// new incoming item. For all internal items,
	/// check if they require to be waited for.
	/// if so, call the `Wait` closure.
	/// if they are ready, call the `Ready` closure.
	fn schedule_wait<S, Wait, Ready>(
		input: Self::Blocked,
		status_check: &S,
		wait: Wait,
		ready: Ready,
	) -> Result<(), Error> where
		S: BlockStatus<Block>,
		Wait: FnMut(Block::Hash, Self),
		Ready: FnMut(Self::Blocked);

	/// called when the wait has completed. The canonical number is passed through
	/// for further checks.
	fn wait_completed(self, canon_number: NumberFor<Block>) -> Option<Self::Blocked>;
}

/// Buffering imported messages until blocks with given hashes are imported.
pub(crate) struct UntilImported<Block: BlockT, Status, I, M: BlockUntilImported<Block>> {
	import_notifications: Fuse<ImportNotifications<Block>>,
	status_check: Status,
	inner: Fuse<I>,
	ready: VecDeque<M::Blocked>,
	check_pending: Interval,
	pending: HashMap<Block::Hash, (Instant, Vec<M>)>,
}

impl<Block: BlockT, Status, I: Stream, M> UntilImported<Block, Status, I, M>
	where Status: BlockStatus<Block>, M: BlockUntilImported<Block>
{
	/// Create a new `UntilImported` wrapper.
	pub(crate) fn new(
		import_notifications: ImportNotifications<Block>,
		status_check: Status,
		stream: I,
	) -> Self {
		// how often to check if pending messages that are waiting for blocks to be
		// imported can be checked.
		//
		// the import notifications interval takes care of most of this; this is
		// used in the event of missed import notifications
		const CHECK_PENDING_INTERVAL: Duration = Duration::from_secs(5);
		let now = Instant::now();

		let check_pending = Interval::new(now + CHECK_PENDING_INTERVAL, CHECK_PENDING_INTERVAL);
		UntilImported {
			import_notifications: import_notifications.fuse(),
			status_check,
			inner: stream.fuse(),
			ready: VecDeque::new(),
			check_pending,
			pending: HashMap::new(),
		}
	}
}

impl<Block: BlockT, Status, I, M> Stream for UntilImported<Block, Status, I, M> where
	Status: BlockStatus<Block>,
	I: Stream<Item=M::Blocked,Error=Error>,
	M: BlockUntilImported<Block>,
{
	type Item = M::Blocked;
	type Error = Error;

	fn poll(&mut self) -> Poll<Option<M::Blocked>, Error> {
		loop {
			match self.inner.poll()? {
				Async::Ready(None) => return Ok(Async::Ready(None)),
				Async::Ready(Some(input)) => {
					// new input: schedule wait of any parts which require
					// blocks to be known.
					let ready = &mut self.ready;
					let pending = &mut self.pending;
					M::schedule_wait(
						input,
						&self.status_check,
						|target_hash, wait| pending
							.entry(target_hash)
							.or_insert_with(|| (Instant::now(), Vec::new()))
							.1
							.push(wait),
						|ready_item| ready.push_back(ready_item),
					)?;
				}
				Async::NotReady => break,
			}
		}

		loop {
			match self.import_notifications.poll() {
				Err(_) => return Err(Error::Network(format!("Failed to get new message"))),
				Ok(Async::Ready(None)) => return Ok(Async::Ready(None)),
				Ok(Async::Ready(Some(notification))) => {
					// new block imported. queue up all messages tied to that hash.
					if let Some((_, messages)) = self.pending.remove(&notification.hash) {
						let canon_number = notification.header.number().clone();
						let ready_messages = messages.into_iter()
							.filter_map(|m| m.wait_completed(canon_number));

						self.ready.extend(ready_messages);
				 	}
				}
				Ok(Async::NotReady) => break,
			}
		}

		let mut update_interval = false;
		while let Async::Ready(Some(_)) = self.check_pending.poll().map_err(Error::Timer)? {
			update_interval = true;
		}

		if update_interval {
			let mut known_keys = Vec::new();
			for (&block_hash, &mut (ref mut last_log, ref v)) in &mut self.pending {
				if let Some(number) = self.status_check.block_number(block_hash)? {
					known_keys.push((block_hash, number));
				} else {
					let next_log = *last_log + LOG_PENDING_INTERVAL;
					if Instant::now() <= next_log {
						debug!(
							target: "afg",
							"Waiting to import block {} before {} votes can be imported. \
							Possible fork?",
							block_hash,
							v.len(),
						);

						*last_log = next_log;
					}
				}
			}

			for (known_hash, canon_number) in known_keys {
				if let Some((_, pending_messages)) = self.pending.remove(&known_hash) {
					let ready_messages = pending_messages.into_iter()
						.filter_map(|m| m.wait_completed(canon_number));

					self.ready.extend(ready_messages);
				}
			}
		}

		if let Some(ready) = self.ready.pop_front() {
			return Ok(Async::Ready(Some(ready)))
		}

		if self.import_notifications.is_done() && self.inner.is_done() {
			Ok(Async::Ready(None))
		} else {

			Ok(Async::NotReady)
		}
	}
}

fn warn_authority_wrong_target<H: ::std::fmt::Display>(hash: H, id: AuthorityId) {
	warn!(
		target: "afg",
		"Authority {:?} signed GRANDPA message with \
		wrong block number for hash {}",
		id,
		hash,
	);
}

impl<Block: BlockT> BlockUntilImported<Block> for SignedMessage<Block> {
	type Blocked = Self;

	fn schedule_wait<S, Wait, Ready>(
		msg: Self::Blocked,
		status_check: &S,
		mut wait: Wait,
		mut ready: Ready,
	) -> Result<(), Error> where
		S: BlockStatus<Block>,
		Wait: FnMut(Block::Hash, Self),
		Ready: FnMut(Self::Blocked),
	{
		let (&target_hash, target_number) = msg.target();

		if let Some(number) = status_check.block_number(target_hash)? {
			if number != target_number {
				warn_authority_wrong_target(target_hash, msg.id);
			} else {
				ready(msg);
			}
		} else {
			wait(target_hash, msg)
		}

		Ok(())
	}

	fn wait_completed(self, canon_number: NumberFor<Block>) -> Option<Self::Blocked> {
		let (&target_hash, target_number) = self.target();
		if canon_number != target_number {
			warn_authority_wrong_target(target_hash, self.id);

			None
		} else {
			Some(self)
		}
	}
}

/// Helper type definition for the stream which waits until vote targets for
/// signed messages are imported.
pub(crate) type UntilVoteTargetImported<Block, Status, I> = UntilImported<Block, Status, I, SignedMessage<Block>>;

/// This blocks a commit message's import until all blocks
/// referenced in its votes are known.
///
/// This is used for compact commits which have already been checked for
/// structural soundness.
pub(crate) struct BlockCommitMessage<Block: BlockT, U> {
	inner: Arc<(AtomicUsize, Mutex<Option<(u64, CompactCommit<Block>, U)>>)>,
	target_number: NumberFor<Block>,
}

impl<Block: BlockT, U> BlockUntilImported<Block> for BlockCommitMessage<Block, U> {
	type Blocked = (u64, CompactCommit<Block>, U);

	fn schedule_wait<S, Wait, Ready>(
		input: Self::Blocked,
		status_check: &S,
		mut wait: Wait,
		mut ready: Ready,
	) -> Result<(), Error> where
		S: BlockStatus<Block>,
		Wait: FnMut(Block::Hash, Self),
		Ready: FnMut(Self::Blocked),
	{
		use std::collections::hash_map::Entry;

		enum KnownOrUnknown<N> {
			Known(N),
			Unknown(N),
		}

		impl<N> KnownOrUnknown<N> {
			fn number(&self) -> &N {
				match *self {
					KnownOrUnknown::Known(ref n) => n,
					KnownOrUnknown::Unknown(ref n) => n,
				}
			}
		}

		let mut checked_hashes: HashMap<_, KnownOrUnknown<NumberFor<Block>>> = HashMap::new();
		let mut unknown_count = 0;

		{
			// returns false when should early exit.
			let mut query_known = |target_hash, perceived_number| -> Result<bool, Error> {
				// check integrity: all precommits for same hash have same number.
				let canon_number = match checked_hashes.entry(target_hash) {
					Entry::Occupied(entry) => entry.get().number().clone(),
					Entry::Vacant(entry) => {
						if let Some(number) = status_check.block_number(target_hash)? {
							entry.insert(KnownOrUnknown::Known(number));
							number

						} else {
							entry.insert(KnownOrUnknown::Unknown(perceived_number));
							unknown_count += 1;
							perceived_number
						}
					}
				};

				if canon_number != perceived_number {
					// invalid commit: messages targeting wrong number or
					// at least different from other vote. in same commit.
					return Ok(false);
				}

				Ok(true)
			};

			let commit = &input.1;

			// add known hashes from the precommits.
			for precommit in &commit.precommits {
				let target_number = precommit.target_number;
				let target_hash = precommit.target_hash;

				if !query_known(target_hash, target_number)? {
					return Ok(())
				}
			}

			// see if commit target hash is known.
			if !query_known(commit.target_hash, commit.target_number)? {
				return Ok(())
			}
		}

		// none of the hashes in the commit message were unknown.
		// we can just return the commit directly.
		if unknown_count == 0 {
			ready(input);
			return Ok(())
		}

		let locked_commit = Arc::new((AtomicUsize::new(unknown_count), Mutex::new(Some(input))));

		// schedule waits for all unknown messages.
		// when the last one of these has `wait_completed` called on it,
		// the commit will be returned.
		//
		// in the future, we may want to issue sync requests to the network
		// if this is taking a long time.
		for (hash, is_known) in checked_hashes {
			if let KnownOrUnknown::Unknown(target_number) = is_known {
				wait(hash, BlockCommitMessage {
					inner: locked_commit.clone(),
					target_number,
				})
			}
		}

		Ok(())
	}

	fn wait_completed(self, canon_number: NumberFor<Block>) -> Option<Self::Blocked> {
		if self.target_number != canon_number {
			// if we return without deducting the counter, then none of the other
			// handles can return the commit message.
			return None;
		}

		let mut last_count = self.inner.0.load(Ordering::Acquire);

		// CAS loop to ensure that we always have a last reader.
		loop {
			if last_count == 1 { // we are the last one left.
				return self.inner.1.lock().take();
			}

			let prev_value = self.inner.0.compare_and_swap(
				last_count,
				last_count - 1,
				Ordering::SeqCst,
			);

			if prev_value == last_count {
				return None;
			} else {
				last_count = prev_value;
			}
		}
	}
}

/// A stream which gates off incoming commit messages until all referenced
/// block hashes have been imported.
pub(crate) type UntilCommitBlocksImported<Block, Status, I, U> = UntilImported<
	Block,
	Status,
	I,
	BlockCommitMessage<Block, U>,
>;

#[cfg(test)]
mod tests {
	use super::*;
	use tokio::runtime::current_thread::Runtime;
	use tokio::timer::Delay;
	use test_client::runtime::{Block, Hash, Header};
	use consensus_common::BlockOrigin;
	use client::BlockImportNotification;
	use futures::future::Either;
	use futures::sync::mpsc;
	use grandpa::Precommit;

	#[derive(Clone)]
	struct TestChainState {
		sender: mpsc::UnboundedSender<BlockImportNotification<Block>>,
		known_blocks: Arc<Mutex<HashMap<Hash, u64>>>,
	}

	impl TestChainState {
		fn new() -> (Self, ImportNotifications<Block>) {
			let (tx, rx) = mpsc::unbounded();
			let state = TestChainState {
				sender: tx,
				known_blocks: Arc::new(Mutex::new(HashMap::new())),
			};

			(state, rx)
		}

		fn block_status(&self) -> TestBlockStatus {
			TestBlockStatus { inner: self.known_blocks.clone() }
		}

		fn import_header(&self, header: Header) {
			let hash = header.hash();
			let number = header.number().clone();

			self.known_blocks.lock().insert(hash, number);
			self.sender.unbounded_send(BlockImportNotification {
				hash,
				origin: BlockOrigin::File,
				header,
				is_new_best: false,
			}).unwrap();
		}
	}

	struct TestBlockStatus {
		inner: Arc<Mutex<HashMap<Hash, u64>>>,
	}

	impl BlockStatus<Block> for TestBlockStatus {
		fn block_number(&self, hash: Hash) -> Result<Option<u64>, Error> {
			Ok(self.inner.lock().get(&hash).map(|x| x.clone()))
		}
	}

	fn make_header(number: u64) -> Header {
		Header::new(
			number,
			Default::default(),
			Default::default(),
			Default::default(),
			Default::default(),
		)
	}

	#[test]
	fn blocking_commit_message() {
		let h1 = make_header(5);
		let h2 = make_header(6);
		let h3 = make_header(7);

		let (chain_state, import_notifications) = TestChainState::new();
		let block_status = chain_state.block_status();

		let unknown_commit = CompactCommit::<Block> {
			target_hash: h1.hash(),
			target_number: 5,
			precommits: vec![
				Precommit {
					target_hash: h2.hash(),
					target_number: 6,
				},
				Precommit {
					target_hash: h3.hash(),
					target_number: 7,
				},
			],
			auth_data: Vec::new(), // not used
		};

		let (commit_tx, commit_rx) = mpsc::unbounded();

		let until_imported = UntilCommitBlocksImported::new(
			import_notifications,
			block_status,
			commit_rx.map_err(|_| panic!("should never error")),
		);

		commit_tx.unbounded_send((0, unknown_commit.clone(), ())).unwrap();

		let inner_chain_state = chain_state.clone();
		let work = until_imported
			.into_future()
			.select2(Delay::new(Instant::now() + Duration::from_millis(100)))
			.then(move |res| match res {
				Err(_) => panic!("neither should have had error"),
				Ok(Either::A(_)) => panic!("timeout should have fired first"),
				Ok(Either::B((_, until_imported))) => {
					// timeout fired. push in the headers.
					inner_chain_state.import_header(h1);
					inner_chain_state.import_header(h2);
					inner_chain_state.import_header(h3);

					until_imported
				}
			});

		let mut runtime = Runtime::new().unwrap();
		assert_eq!(runtime.block_on(work).map_err(|(e, _)| e).unwrap().0, Some((0, unknown_commit, ())));
	}

	#[test]
	fn commit_message_all_known() {
		let h1 = make_header(5);
		let h2 = make_header(6);
		let h3 = make_header(7);

		let (chain_state, import_notifications) = TestChainState::new();
		let block_status = chain_state.block_status();

		let known_commit = CompactCommit::<Block> {
			target_hash: h1.hash(),
			target_number: 5,
			precommits: vec![
				Precommit {
					target_hash: h2.hash(),
					target_number: 6,
				},
				Precommit {
					target_hash: h3.hash(),
					target_number: 7,
				},
			],
			auth_data: Vec::new(), // not used
		};

		chain_state.import_header(h1);
		chain_state.import_header(h2);
		chain_state.import_header(h3);

		let (commit_tx, commit_rx) = mpsc::unbounded();

		let until_imported = UntilCommitBlocksImported::new(
			import_notifications,
			block_status,
			commit_rx.map_err(|_| panic!("should never error")),
		);

		commit_tx.unbounded_send((0, known_commit.clone(), ())).unwrap();

		let work = until_imported.into_future();

		let mut runtime = Runtime::new().unwrap();
		assert_eq!(runtime.block_on(work).map_err(|(e, _)| e).unwrap().0, Some((0, known_commit, ())));
	}
}
