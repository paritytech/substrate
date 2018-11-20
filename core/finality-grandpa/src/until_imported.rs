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

//! Helper stream for waiting until one or more blocks are imported before
//! passing through inner items.
//!
//! This is used for votes and commit messages currently.

use super::{BlockStatus, Error, SignedMessage, CompactCommit};

use client::ImportNotifications;
use futures::prelude::*;
use futures::stream::Fuse;
use parking_lot::Mutex;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, NumberFor};
use substrate_primitives::AuthorityId;
use tokio::timer::Interval;

use std::collections::{HashMap, VecDeque};
use std::sync::{atomic::{AtomicUsize, Ordering}, Arc};
use std::time::{Duration, Instant};

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
	pending: HashMap<Block::Hash, Vec<M>>,
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
			match self.inner.poll() {
				Err(e) => return Err(e),
				Ok(Async::Ready(None)) => return Ok(Async::Ready(None)),
				Ok(Async::Ready(Some(input))) => {
					// new input: schedule wait of any parts which require
					// blocks to be known.
					let mut ready = &mut self.ready;
					let mut pending = &mut self.pending;
					M::schedule_wait(
						input,
						&self.status_check,
						|target_hash, wait| pending
							.entry(target_hash)
							.or_insert_with(Vec::new)
							.push(wait),
						|ready_item| ready.push_back(ready_item),
					)?;
				}
				Ok(Async::NotReady) => break,
			}
		}

		loop {
			match self.import_notifications.poll() {
				Err(_) => return Err(Error::Network(format!("Failed to get new message"))),
				Ok(Async::Ready(None)) => return Ok(Async::Ready(None)),
				Ok(Async::Ready(Some(notification))) => {
					// new block imported. queue up all messages tied to that hash.
					if let Some(messages) = self.pending.remove(&notification.hash) {
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
			for &block_hash in self.pending.keys() {
				if let Some(number) = self.status_check.block_number(block_hash)? {
					known_keys.push((block_hash, number));
				}
			}

			for (known_hash, canon_number) in known_keys {
				if let Some(pending_messages) = self.pending.remove(&known_hash) {
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
pub(crate) struct BlockCommitMessage<Block: BlockT> {
	inner: Arc<(AtomicUsize, Mutex<Option<CompactCommit<Block>>>)>,
	target_number: NumberFor<Block>,
}

impl<Block: BlockT> BlockUntilImported<Block> for BlockCommitMessage<Block> {
	type Blocked = CompactCommit<Block>;

	fn schedule_wait<S, Wait, Ready>(
		commit: Self::Blocked,
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
					Entry::Vacant(mut entry) => {
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
			ready(commit);
			return Ok(())
		}

		let locked_commit = Arc::new((AtomicUsize::new(unknown_count), Mutex::new(Some(commit))));

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

	fn wait_completed(self, canon_number: NumberFor<Block>) -> Option<CompactCommit<Block>> {
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
