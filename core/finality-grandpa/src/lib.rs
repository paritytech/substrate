// Copyright 2018 Parity Technologies (UK) Ltd.
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
extern crate parity_codec as codec;

#[macro_use]
extern crate log;

#[cfg(test)]
extern crate substrate_network as network;

#[cfg(test)]
extern crate parking_lot;

#[cfg(test)]
extern crate substrate_keyring as keyring;

use futures::prelude::*;
use futures::stream::Fuse;
use futures::sync::mpsc;
use client::{Client, ImportNotifications, backend::Backend, CallExecutor};
use codec::{Encode, Decode};
use runtime_primitives::traits::{As, NumberFor, Block as BlockT, Header as HeaderT};
use runtime_primitives::generic::BlockId;
use substrate_primitives::{ed25519, AuthorityId, Blake2Hasher};
use tokio::timer::Interval;

use grandpa::Error as GrandpaError;
use grandpa::{voter, round::State as RoundState, Prevote, Precommit, Equivocation};

use std::collections::{VecDeque, HashMap};
use std::sync::Arc;
use std::time::{Instant, Duration};

const LAST_COMPLETED_KEY: &[u8] = b"grandpa_completed_round";

/// A GRANDPA message for a substrate chain.
pub type Message<Block> = grandpa::Message<<Block as BlockT>::Hash>;
/// A signed message.
pub type SignedMessage<Block> = grandpa::SignedMessage<<Block as BlockT>::Hash, ed25519::Signature, AuthorityId>;

/// Configuration for the GRANDPA service.
pub struct Config {
	/// The expected duration for a message to be gossiped across the network.
	pub gossip_duration: Duration,
	/// The voters.
	// TODO: make dynamic
	pub voters: Vec<AuthorityId>,
	/// The local signing key.
	pub local_key: Option<Arc<ed25519::Pair>>,
}

/// Errors that can occur while voting in GRANDPA.
#[derive(Debug)]
pub enum Error {
	/// An error within grandpa.
	Grandpa(GrandpaError),
	/// A network error.
	Network(String),
	/// A blockchain error.
	Blockchain(String),
	/// Could not complete a round on disk.
	CouldNotCompleteRound(::client::error::Error),
	/// A timer failed to fire.
	Timer(::tokio::timer::Error),
}

impl From<GrandpaError> for Error {
	fn from(e: GrandpaError) -> Self {
		Error::Grandpa(e)
	}
}

/// A handle to the network. This is generally implemented by providing some
/// handle to a gossip service or similar.
///
/// Intended to be a lightweight handle such as an `Arc`.
pub trait Network: Clone {
	/// A stream of input messages for a topic.
	type In: Stream<Item=Vec<u8>,Error=()>;

	/// Get a stream of messages for a specific round. This stream should
	/// never logically conclude.
	fn messages_for(&self, round: u64) -> Self::In;

	/// Send a message at a specific round out.
	fn send_message(&self, round: u64, message: Vec<u8>);

	/// Clean up messages for a round.
	fn drop_messages(&self, round: u64);
}

/// Something which can determine if a block is known.
pub trait BlockStatus<Block: BlockT> {
	/// Return `Ok(Some(number))` or `Ok(None)` depending on whether the block
	/// is definitely known and has been imported.
	/// If an unexpected error occurs, return that.
	fn block_number(&self, hash: Block::Hash) -> Result<Option<u32>, Error>;
}

impl<B, E, Block: BlockT> BlockStatus<Block> for Arc<Client<B, E, Block>> where
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

// clears the network messages for inner round on drop.
struct ClearOnDrop<I, N: Network> {
	round: u64,
	inner: I,
	network: N,
}

impl<I: Sink, N: Network> Sink for ClearOnDrop<I, N> {
	type SinkItem = I::SinkItem;
	type SinkError = I::SinkError;

	fn start_send(&mut self, item: Self::SinkItem) -> StartSend<Self::SinkItem, Self::SinkError> {
		self.inner.start_send(item)
	}

	fn poll_complete(&mut self) -> Poll<(), Self::SinkError> {
		self.inner.poll_complete()
	}

	fn close(&mut self) -> Poll<(), Self::SinkError> {
		self.inner.close()
	}
}

impl<I, N: Network> Drop for ClearOnDrop<I, N> {
	fn drop(&mut self) {
		self.network.drop_messages(self.round);
	}
}

// converts a message stream into a stream of signed messages.
// the output stream checks signatures also.
fn checked_message_stream<Block: BlockT, S>(inner: S, voters: Vec<AuthorityId>)
	-> impl Stream<Item=SignedMessage<Block>,Error=Error> where
	S: Stream<Item=Vec<u8>,Error=()>
{
	inner
		.filter_map(|raw| {
			let decoded = SignedMessage::<Block>::decode(&mut &raw[..]);
			if decoded.is_none() {
				debug!(target: "afg", "Skipping malformed message {:?}", raw);
			}
			decoded
		})
		.and_then(move |msg| {
			// check signature.
			if !voters.contains(&msg.id) {
				debug!(target: "afg", "Skipping message from unknown voter {}", msg.id);
				return Ok(None);
			}

			let as_public = ::ed25519::Public::from_raw(msg.id.0);
			let encoded_raw = msg.message.encode();
			if ::ed25519::verify_strong(&msg.signature, &encoded_raw, as_public) {
				Ok(Some(msg))
			} else {
				debug!(target: "afg", "Skipping message with bad signature");
				Ok(None)
			}
		})
		.filter_map(|x| x)
		.map_err(|()| Error::Network(format!("Failed to receive message on unbounded stream")))
}

fn outgoing_messages<Block: BlockT, N: Network>(
	local_key: Option<Arc<ed25519::Pair>>,
	voters: Vec<AuthorityId>,
	round: u64,
	network: N,
) -> (
	impl Stream<Item=SignedMessage<Block>,Error=Error>,
	impl Sink<SinkItem=Message<Block>,SinkError=Error>,
) {
	let locals = local_key.and_then(|pair| {
		let public = pair.public();
		voters.iter().find(|id| id.0 == public.0).map(move |id| (pair, id.clone()))
	});

	let (tx, rx) = mpsc::unbounded();
	let rx = rx
		.map(move |msg: Message<Block>| {
			// when locals exist. sign messages on import
			if let Some((ref pair, local_id)) = locals {
				let encoded = msg.encode();
				let signature = pair.sign(&encoded[..]);
				let signed = SignedMessage::<Block> {
					message: msg,
					signature,
					id: local_id,
				};

				// forward to network.
				network.send_message(round, signed.encode());
				Some(signed)
			} else {
				None
			}
		})
		.filter_map(|x| x)
		.map_err(move |()| Error::Network(
			format!("Failed to receive on unbounded receiver for round {}", round)
		));

	let tx = tx.sink_map_err(move |e| Error::Network(format!("Failed to broadcast message \
		to network in round {}: {:?}", round, e)));

	(rx, tx)
}

/// The environment we run GRANDPA in.
pub struct Environment<B, E, Block: BlockT, N: Network> {
	inner: Arc<Client<B, E, Block>>,
	voters: HashMap<AuthorityId, usize>,
	config: Config,
	network: N,
}

impl<Block: BlockT, B, E, N> grandpa::Chain<Block::Hash> for Environment<B, E, Block, N> where
	Block: 'static,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static,
	N: Network + 'static,
	N::In: 'static,
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

impl<B, E, Block: BlockT, N> voter::Environment<Block::Hash> for Environment<B, E, Block, N> where
	Block: 'static,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static,
	N: Network + 'static,
	N::In: 'static,
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
		use client::BlockchainEvents;
		use tokio::timer::Delay;

		let now = Instant::now();
		let prevote_timer = Delay::new(now + self.config.gossip_duration * 2);
		let precommit_timer = Delay::new(now + self.config.gossip_duration * 4);

		// TODO: dispatch this with `mpsc::spawn`.
		let incoming = checked_message_stream::<Block, _>(
			self.network.messages_for(round),
			self.config.voters.clone(),
		);

		let (out_rx, outgoing) = outgoing_messages::<Block, _>(
			self.config.local_key.clone(),
			self.config.voters.clone(),
			round,
			self.network.clone(),
		);

		// schedule incoming messages from the network to be held until
		// corresponding blocks are imported.
		let incoming = UntilImported::new(
			self.inner.import_notification_stream(),
			self.inner.clone(),
			incoming,
		);

		// join incoming network messages with locally originating ones.
		let incoming = Box::new(incoming.select(out_rx));

		// schedule network message cleanup when sink drops.
		let outgoing = Box::new(ClearOnDrop {
			round,
			network: self.network.clone(),
			inner: outgoing,
		});

		voter::RoundData {
			prevote_timer: Box::new(prevote_timer.map_err(Error::Timer)),
			precommit_timer: Box::new(precommit_timer.map_err(Error::Timer)),
			voters: self.voters.clone(),
			incoming,
			outgoing,
		}
	}

	fn completed(&self, round: u64, state: RoundState<Block::Hash>) -> Result<(), Self::Error> {
		let encoded_state = (round, state).encode();
		if let Err(e) = self.inner.backend()
			.insert_aux(&[(LAST_COMPLETED_KEY, &encoded_state[..])], &[])
		{
			warn!(target: "afg", "Shutting down voter due to error bookkeeping last completed round in DB: {:?}", e);
			Err(Error::CouldNotCompleteRound(e))
		} else {
			Ok(())
		}
	}

	fn finalize_block(&self, hash: Block::Hash, number: u32) -> Result<(), Self::Error> {
		// TODO: don't unconditionally notify.
		if let Err(e) = self.inner.finalize_block(BlockId::Hash(hash), true) {
			warn!(target: "afg", "Error applying finality to block {:?}: {:?}", (hash, number), e);
		}

		// we return without error in all cases because not being able to finalize is
		// non-fatal.
		Ok(())
	}

	fn prevote_equivocation(
		&self,
		_round: u64,
		equivocation: ::grandpa::Equivocation<Self::Id, Prevote<Block::Hash>, Self::Signature>
	) {
		warn!(target: "afg", "Detected prevote equivocation in the finality worker: {:?}", equivocation);
		// nothing yet; this could craft misbehavior reports of some kind.
	}

	fn precommit_equivocation(
		&self,
		_round: u64,
		equivocation: Equivocation<Self::Id, Precommit<Block::Hash>, Self::Signature>
	) {
		warn!(target: "afg", "Detected precommit equivocation in the finality worker: {:?}", equivocation);
		// nothing yet
	}
}

/// Run a GRANDPA voter as a task. The returned future should be executed in a tokio runtime.
pub fn run_grandpa<B, E, Block: BlockT, N>(
	config: Config,
	client: Arc<Client<B, E, Block>>,
	voters: HashMap<AuthorityId, usize>,
	network: N,
) -> Result<impl Future<Item=(),Error=()>,client::error::Error> where
	Block::Hash: Ord,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static,
	N: Network + 'static,
	N::In: 'static,
	NumberFor<Block>: As<u32>,
{
	let chain_info = client.info()?;
	let genesis_hash = chain_info.chain.genesis_hash;
	let last_finalized = (
		chain_info.chain.finalized_hash,
		chain_info.chain.finalized_number.as_()
	);

	let (last_round_number, last_state) = match client.backend().get_aux(LAST_COMPLETED_KEY)? {
		None => (0, RoundState::genesis((genesis_hash, 0))),
		Some(raw) => <(u64, RoundState<Block::Hash>)>::decode(&mut &raw[..])
			.ok_or_else(|| ::client::error::ErrorKind::Backend(
				format!("Last GRANDPA round state kept in invalid format")
			))?
	};

	let environment = Arc::new(Environment {
		inner: client,
		config,
		voters,
		network,
	});

	let voter = voter::Voter::new(
		environment,
		last_round_number,
		last_state,
		last_finalized,
	);

	Ok(voter.map_err(|e| warn!("GRANDPA Voter failed: {:?}", e)))
}

#[cfg(test)]
mod tests {
	use super::*;
	use network::test::*;
	use parking_lot::Mutex;
	use tokio::runtime::current_thread;
	use keyring::Keyring;
	use client::BlockchainEvents;

	#[derive(Clone)]
	struct TestGrandpaNetwork {
		inner: Arc<Mutex<TestNet>>,
		peer_id: usize,
	}

	impl TestGrandpaNetwork {
		fn new(inner: Arc<Mutex<TestNet>>, peer_id: usize,) -> Self {
			TestGrandpaNetwork {
				inner,
				peer_id,
			}
		}
	}

	fn round_to_topic(round: u64) -> Hash {
		let mut hash = Hash::default();
		round.using_encoded(|s| {
			let raw = hash.as_mut();
			raw[..8].copy_from_slice(s);
		});
		hash
	}

	impl Network for TestGrandpaNetwork {
		type In = Box<Stream<Item=Vec<u8>,Error=()>>;

		fn messages_for(&self, round: u64) -> Self::In {
			let messages = self.inner.lock().peer(self.peer_id)
				.with_spec(|spec, _| spec.gossip.messages_for(round_to_topic(round)));

			let messages = messages.map_err(
				move |_| panic!("Messages for round {} dropped too early", round)
			);

			Box::new(messages)
		}

		fn send_message(&self, round: u64, message: Vec<u8>) {
			let mut inner = self.inner.lock();
			inner.peer(self.peer_id).gossip_message(round_to_topic(round), message);
			inner.route();
		}

		fn drop_messages(&self, round: u64) {
			let topic = round_to_topic(round);
			self.inner.lock().peer(self.peer_id)
				.with_spec(|spec, _| spec.gossip.collect_garbage(|t| t == &topic));
		}
	}

	const TEST_GOSSIP_DURATION: Duration = Duration::from_millis(500);
	const TEST_ROUTING_INTERVAL: Duration = Duration::from_millis(50);

	#[test]
	fn finalize_20_unanimous_3_peers() {
		let mut net = TestNet::new(3);
		net.peer(0).push_blocks(20, false);
		net.sync();

		let net = Arc::new(Mutex::new(net));
		let peers = &[
			(0, Keyring::Alice),
			(1, Keyring::Bob),
			(2, Keyring::Charlie),
		];

		let voters: Vec<_> = peers.iter()
			.map(|&(_, ref key)| AuthorityId(key.to_raw_public()))
			.collect();

		let mut finality_notifications = Vec::new();

		let mut runtime = current_thread::Runtime::new().unwrap();
		for (peer_id, key) in peers {
			let client = net.lock().peer(*peer_id).client().clone();
			finality_notifications.push(
				client.finality_notification_stream()
					.take_while(|n| Ok(n.header.number() < &20))
					.for_each(move |_| Ok(()))
			);
			let voter = run_grandpa(
				Config {
					gossip_duration: TEST_GOSSIP_DURATION,
					voters: voters.clone(),
					local_key: Some(Arc::new(key.clone().into())),
				},
				client,
				voters.iter().map(|&id| (id, 1)).collect(),
				TestGrandpaNetwork::new(net.clone(), *peer_id),
			).expect("all in order with client and network");

			runtime.spawn(voter);
		}

		// wait for all finalized on each.
		let wait_for = ::futures::future::join_all(finality_notifications)
			.map(|_| ())
			.map_err(|_| ());

		let drive_to_completion = ::tokio::timer::Interval::new_interval(TEST_ROUTING_INTERVAL)
			.for_each(move |_| { net.lock().route_until_complete(); Ok(()) })
			.map(|_| ())
			.map_err(|_| ());

		runtime.block_on(wait_for.select(drive_to_completion).map_err(|_| ())).unwrap();
	}

	#[test]
	fn observer_can_finalize() {
		let mut net = TestNet::new(4);
		net.peer(0).push_blocks(20, false);
		net.sync();

		let net = Arc::new(Mutex::new(net));
		let peers = &[
			(0, Keyring::Alice),
			(1, Keyring::Bob),
			(2, Keyring::Charlie),
		];

		let voters: HashMap<_, _> = peers.iter()
			.map(|&(_, ref key)| (AuthorityId(key.to_raw_public()), 1))
			.collect();

		let mut finality_notifications = Vec::new();

		let mut runtime = current_thread::Runtime::new().unwrap();
		let all_peers = peers.iter()
			.cloned()
			.map(|(id, key)| (id, Some(Arc::new(key.into()))))
			.chain(::std::iter::once((3, None)));

		for (peer_id, local_key) in all_peers {
			let client = net.lock().peer(peer_id).client().clone();
			finality_notifications.push(
				client.finality_notification_stream()
					.take_while(|n| Ok(n.header.number() < &20))
					.for_each(move |_| Ok(()))
			);
			let voter = run_grandpa(
				Config {
					gossip_duration: TEST_GOSSIP_DURATION,
					voters: voters.keys().cloned().collect(),
					local_key,
				},
				client,
				voters.clone(),
				TestGrandpaNetwork::new(net.clone(), peer_id),
			).expect("all in order with client and network");

			runtime.spawn(voter);
		}

		// wait for all finalized on each.
		let wait_for = ::futures::future::join_all(finality_notifications)
			.map(|_| ())
			.map_err(|_| ());

		let drive_to_completion = ::tokio::timer::Interval::new_interval(TEST_ROUTING_INTERVAL)
			.for_each(move |_| { net.lock().route_until_complete(); Ok(()) })
			.map(|_| ())
			.map_err(|_| ());

		runtime.block_on(wait_for.select(drive_to_completion).map_err(|_| ())).unwrap();
	}
}
