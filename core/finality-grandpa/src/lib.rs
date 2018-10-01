// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Integration of the GRANDPA finality gadget into substrate.
//!
//! This is a long-running future that produces finality notifications.

extern crate finality_grandpa as grandpa;
extern crate futures;
extern crate substrate_client as client;
extern crate sr_primitives as runtime_primitives;
extern crate substrate_primitives;
extern crate tokio;

#[macro_use]
extern crate log;

use futures::prelude::*;
use futures::stream::Fuse;
use client::{Client, ImportNotifications, backend::Backend, CallExecutor};
use runtime_primitives::traits::{As, NumberFor, Block as BlockT, Header as HeaderT};
use runtime_primitives::generic::BlockId;
use substrate_primitives::{ed25519, AuthorityId, Blake2Hasher};
use tokio::timer::Interval;

use grandpa::Error as GrandpaError;
use grandpa::{voter, round::State as RoundState, Prevote, Precommit, Equivocation};

use std::collections::{VecDeque, HashMap};
use std::sync::Arc;
use std::time::{Instant, Duration};

/// A GRANDPA message for a substrate chain.
pub type Message<Block> = grandpa::Message<<Block as BlockT>::Hash>;
/// A signed message.
pub type SignedMessage<Block> = grandpa::SignedMessage<<Block as BlockT>::Hash, ed25519::Signature, AuthorityId>;

/// Configuration for the GRANDPA service.
pub struct Config {
	/// The expected duration for a message to be gossiped across the network.
	pub gossip_duration: Duration,
	/// The voters.
	pub voters: Vec<AuthorityId>,
	/// The local ID.
	pub local_id: Option<AuthorityId>,
}

/// A handle to the network. This is generally implemented by providing some
pub trait Network {
	/// A stream of input messages for a topic.
	type In: Stream<Item=Vec<u8>,Error=()>;

	/// Get a stream of messages for a specific round. This stream should
	/// never logically conclude.
	fn messages_for(&self, round: u64) -> Self::In;

	/// Send a message at a specific round out.
	fn send_message(&self, round: u64, message: Vec<u8>);
}

/// Something which can determine if a block is known.
pub trait BlockStatus<Block: BlockT> {
	/// Return `Ok(Some(number))` or `Ok(None)` depending on whether the block
	/// is definitely known and has been imported.
	/// If an unexpected error occurs, return that.
	fn block_number(&self, hash: Block::Hash) -> Result<Option<u32>, Error>;
}

impl<B, E, Block: BlockT> BlockStatus<Block> for Client<B, E, Block> where
	B: Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher>,
	NumberFor<Block>: As<u32>,
{
	fn block_number(&self, hash: Block::Hash) -> Result<Option<u32>, Error> {
		self.block_number_from_id(&BlockId::Hash(hash))
			.map_err(|e| Error::Blockchain(format!("{:?}", e)))
			.map(|num| num.map(|n| n.as_()))
	}
}

/// Buffering imported messages until blocks with given hashes are imported.
pub struct UntilImported<Block: BlockT, Status, I> {
	import_notifications: Fuse<ImportNotifications<Block>>,
	status_check: Status,
	inner: Fuse<I>,
	ready: VecDeque<SignedMessage<Block>>,
	check_pending: Interval,
	pending: HashMap<Block::Hash, Vec<SignedMessage<Block>>>,
}

impl<Block: BlockT, Status: BlockStatus<Block>, I: Stream> UntilImported<Block, Status, I> {
	fn new(
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

impl<Block: BlockT, Status: BlockStatus<Block>, I> Stream for UntilImported<Block, Status, I>
	where I: Stream<Item=SignedMessage<Block>,Error=Error>
{
	type Item = SignedMessage<Block>;
	type Error = Error;

	fn poll(&mut self) -> Poll<Option<SignedMessage<Block>>, Error> {
		loop {
			match self.inner.poll() {
				Err(e) => return Err(e),
				Ok(Async::Ready(None)) => return Ok(Async::Ready(None)),
				Ok(Async::Ready(Some(signed_message))) => {
					let (&target_hash, target_number) = signed_message.target();

					// new message: hold it until the block is known.
					if let Some(number) = self.status_check.block_number(target_hash)? {
						if number != target_number {
							warn!(
								target: "afg",
								"Authority {:?} signed GRANDPA message with \
								wrong block number for hash {}",
								signed_message.id,
								target_hash
							);
						} else {
							self.ready.push_back(signed_message)
						}
					} else {
						self.pending.entry(target_hash)
							.or_insert_with(Vec::new)
							.push(signed_message);
					}
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
						self.ready.extend(messages);
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
				if let Some(mut pending_messages) = self.pending.remove(&known_hash) {
					// verify canonicality of pending messages.
					pending_messages.retain(|msg| {
						let number_correct = msg.target().1 == canon_number;
						if !number_correct {
							warn!(
								target: "afg",
								"Authority {:?} signed GRANDPA message with \
								wrong block number for hash {}",
								msg.id,
								known_hash,
							);
						}
						number_correct
					});
					self.ready.extend(pending_messages);
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

/// The environment we run GRANDPA in.
pub struct Environment<B, E, Block: BlockT> {
	inner: Arc<Client<B, E, Block>>,
	gossip_duration: Duration,
	config: Config,
}

impl<Block: BlockT, B, E> grandpa::Chain<Block::Hash> for Environment<B, E, Block> where
	B: Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher>,
	NumberFor<Block>: As<u32>,
{
	fn ancestry(&self, base: Block::Hash, block: Block::Hash) -> Result<Vec<Block::Hash>, GrandpaError> {
		let tree_route_res = ::client::blockchain::tree_route(
			self.inner.backend().blockchain(),
			BlockId::Hash(block),
			BlockId::Hash(base),
		);

		let tree_route = match tree_route_res {
			Ok(tree_route) => tree_route,
			Err(e) => {
				debug!(target: "afg", "Encountered error computing ancestry between block {:?} and base {:?}: {:?}",
					block, base, e);

				return Err(GrandpaError::NotDescendent);
			}
		};

		if tree_route.common_block().hash != base {
			return Err(GrandpaError::NotDescendent);
		}

		// skip one because our ancestry is meant to start from the parent of `block`,
		// and `tree_route` includes it.
		Ok(tree_route.retracted().iter().skip(1).map(|e| e.hash).collect())
	}

	fn best_chain_containing(&self, block: Block::Hash) -> Option<(Block::Hash, u32)> {
		match self.inner.best_containing(block, None) {
			Ok(Some(hash)) => {
				let header = self.inner.header(&BlockId::Hash(hash)).ok()?
					.expect("Header known to exist after `best_containing` call; qed");

				Some((hash, header.number().as_()))
			}
			Ok(None) => None,
			Err(e) => {
				debug!(target: "afg", "Encountered error finding best chain containing {:?}: {:?}", block, e);
				None
			}
		}
	}
}

/// Errors that can occur while voting in GRANDPA.
pub enum Error {
	/// An error within grandpa.
	Grandpa(GrandpaError),
	/// A network error.
	Network(String),
	/// A blockchain error.
	Blockchain(String),
	/// A timer failed to fire.
	Timer(::tokio::timer::Error),
}

impl From<GrandpaError> for Error {
	fn from(e: GrandpaError) -> Self {
		Error::Grandpa(e)
	}
}

impl<B, E, Block: BlockT> voter::Environment<Block::Hash> for Environment<B, E, Block> where
	B: Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher>,
	NumberFor<Block>: As<u32>,
{
    type Timer = Box<Future<Item = (), Error = Self::Error>>;
    type Id = AuthorityId;
    type Signature = ed25519::Signature;
    type In = Box<Stream<Item = ::grandpa::SignedMessage<Block::Hash, Self::Signature, Self::Id>, Error = Self::Error>>;
    type Out = Box<Sink<SinkItem = ::grandpa::Message<Block::Hash>, SinkError = Self::Error>>;
    type Error = Error;

    fn round_data(
        &self,
        round: u64
    ) -> voter::RoundData<Self::Timer, Self::Id, Self::In, Self::Out> {
		use tokio::timer::Delay;

		let now = Instant::now();
		let prevote_timer = Delay::new(now + self.config.gossip_duration * 2);
		let precommit_timer = Delay::new(now + self.config.gossip_duration * 4);
		voter::RoundData {
			prevote_timer: Box::new(prevote_timer.map_err(Error::Timer)),
    		precommit_timer: Box::new(precommit_timer.map_err(Error::Timer)),
    		voters: HashMap::new(),
    		incoming: unimplemented!(),
    		outgoing: unimplemented!(),
		}
	}

    fn completed(&self, round: u64, state: RoundState<Block::Hash>) {
		// need to persist this.
		unimplemented!()
	}

    fn finalize_block(&self, hash: Block::Hash, number: u32) {
		// TODO: don't unconditionally notify.
		if let Err(e) = self.inner.finalize_block(BlockId::Hash(hash), true) {
			warn!(target: "afg", "Error applying finality to block {:?}: {:?}", (hash, number), e);
		}
	}

    fn prevote_equivocation(
        &self,
        round: u64,
        equivocation: ::grandpa::Equivocation<Self::Id, Prevote<Block::Hash>, Self::Signature>
    ) {
		warn!(target: "afg", "Detected prevote equivocation in the finality worker: {:?}", equivocation);
		// nothing yet; this could craft misbehavior reports of some kind.
	}

    fn precommit_equivocation(
        &self,
        round: u64,
        equivocation: Equivocation<Self::Id, Precommit<Block::Hash>, Self::Signature>
    ) {
		warn!(target: "afg", "Detected precommit equivocation in the finality worker: {:?}", equivocation);
		// nothing yet
	}
}

/// Run a GRANDPA voter as a task. This future should be executed in a tokio runtime.
pub fn run_voter<B, E, Block: BlockT, N>(
	config: Config,
	client: Arc<Client<B, E, Block>>,
	network: N,
) -> impl Future<Item=(),Error=()> where
	B: Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher>,
	N: Network,
	NumberFor<Block>: As<u32>,
{
	Ok(()).into_future()
}
