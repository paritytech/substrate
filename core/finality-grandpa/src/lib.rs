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

// tag::description[]
//! Integration of the GRANDPA finality gadget into substrate.
//!
//! This is a long-running future that produces finality notifications.
// end::description[]

extern crate finality_grandpa as grandpa;
extern crate futures;
extern crate substrate_client as client;
extern crate sr_primitives as runtime_primitives;
extern crate substrate_consensus_common as consensus_common;
extern crate substrate_primitives;
extern crate tokio;
extern crate parking_lot;
extern crate parity_codec as codec;

#[macro_use]
extern crate log;

#[cfg(test)]
extern crate substrate_network as network;

#[cfg(test)]
extern crate substrate_keyring as keyring;

#[macro_use]
extern crate parity_codec_derive;

use futures::prelude::*;
use futures::stream::Fuse;
use futures::sync::mpsc;
use client::{Client, error::Error as ClientError, ImportNotifications, backend::Backend, CallExecutor};
use codec::{Encode, Decode};
use consensus_common::{BlockImport, ImportBlock, ImportResult};
use runtime_primitives::traits::{
	NumberFor, Block as BlockT, Header as HeaderT, DigestItemFor,
};
use runtime_primitives::generic::BlockId;
use substrate_primitives::{ed25519, AuthorityId, Blake2Hasher};
use tokio::timer::Interval;

use grandpa::Error as GrandpaError;
use grandpa::{voter, round::State as RoundState, Equivocation, BlockNumberOps};

use std::collections::{VecDeque, HashMap};
use std::sync::Arc;
use std::time::{Instant, Duration};

use authorities::SharedAuthoritySet;

mod authorities;

const LAST_COMPLETED_KEY: &[u8] = b"grandpa_completed_round";
const AUTHORITY_SET_KEY: &[u8] = b"grandpa_voters";

/// round-number, round-state
type LastCompleted<H, N> = (u64, RoundState<H, N>);

/// A GRANDPA message for a substrate chain.
pub type Message<Block> = grandpa::Message<<Block as BlockT>::Hash, NumberFor<Block>>;
/// A signed message.
pub type SignedMessage<Block> = grandpa::SignedMessage<
	<Block as BlockT>::Hash,
	NumberFor<Block>,
	ed25519::Signature,
	AuthorityId,
>;
/// A prevote message for this chain's block type.
pub type Prevote<Block> = grandpa::Prevote<<Block as BlockT>::Hash, NumberFor<Block>>;
/// A precommit message for this chain's block type.
pub type Precommit<Block> = grandpa::Precommit<<Block as BlockT>::Hash, NumberFor<Block>>;

/// Configuration for the GRANDPA service.
#[derive(Clone)]
pub struct Config {
	/// The expected duration for a message to be gossiped across the network.
	pub gossip_duration: Duration,
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
	Client(ClientError),
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
	fn block_number(&self, hash: Block::Hash) -> Result<Option<NumberFor<Block>>, Error>;
}

impl<B, E, Block: BlockT> BlockStatus<Block> for Arc<Client<B, E, Block>> where
	B: Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher>,
	NumberFor<Block>: BlockNumberOps,
{
	fn block_number(&self, hash: Block::Hash) -> Result<Option<NumberFor<Block>>, Error> {
		self.block_number_from_id(&BlockId::Hash(hash))
			.map_err(|e| Error::Blockchain(format!("{:?}", e)))
	}
}

/// Buffering imported messages until blocks with given hashes are imported.
struct UntilImported<Block: BlockT, Status, I> {
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

fn localized_payload<E: Encode>(round: u64, set_id: u64, message: &E) -> Vec<u8> {
	let mut v = message.encode();

	round.using_encoded(|s| v.extend(s));
	set_id.using_encoded(|s| v.extend(s));

	v
}

// converts a message stream into a stream of signed messages.
// the output stream checks signatures also.
fn checked_message_stream<Block: BlockT, S>(
	round: u64,
	set_id: u64,
	inner: S,
	voters: Arc<HashMap<AuthorityId, u64>>,
)
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
			if !voters.contains_key(&msg.id) {
				debug!(target: "afg", "Skipping message from unknown voter {}", msg.id);
				return Ok(None);
			}

			let as_public = ::ed25519::Public::from_raw(msg.id.0);
			let encoded_raw = localized_payload(round, set_id, &msg.message);
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
	round: u64,
	set_id: u64,
	local_key: Option<Arc<ed25519::Pair>>,
	voters: Arc<HashMap<AuthorityId, u64>>,
	network: N,
) -> (
	impl Stream<Item=SignedMessage<Block>,Error=Error>,
	impl Sink<SinkItem=Message<Block>,SinkError=Error>,
) {
	let locals = local_key.and_then(|pair| {
		let public = pair.public();
		let id = AuthorityId(public.0);
		if voters.contains_key(&id) {
			Some((pair, id))
		} else {
			None
		}
	});

	let (tx, rx) = mpsc::unbounded();
	let rx = rx
		.map(move |msg: Message<Block>| {
			// when locals exist, sign messages on import
			if let Some((ref pair, local_id)) = locals {
				let encoded = localized_payload(round, set_id, &msg);
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
struct Environment<B, E, Block: BlockT, N: Network> {
	inner: Arc<Client<B, E, Block>>,
	voters: Arc<HashMap<AuthorityId, u64>>,
	config: Config,
	authority_set: SharedAuthoritySet<Block::Hash, NumberFor<Block>>,
	network: N,
	set_id: u64,
}

impl<Block: BlockT, B, E, N> grandpa::Chain<Block::Hash, NumberFor<Block>> for Environment<B, E, Block, N> where
	Block: 'static,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static,
	N: Network + 'static,
	N::In: 'static,
	NumberFor<Block>: BlockNumberOps,
	DigestItemFor<Block>: CompatibleDigestItem<NumberFor<Block>>,
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

	fn best_chain_containing(&self, block: Block::Hash) -> Option<(Block::Hash, NumberFor<Block>)> {
		// we refuse to vote beyond the current limit number where transitions are scheduled to
		// occur.
		// once blocks are finalized that make that transition irrelevant or activate it,
		// we will proceed onwards. most of the time there will be no pending transition.
		let limit = self.authority_set.current_limit();
		match self.inner.best_containing(block, limit) {
			Ok(Some(hash)) => {
				let header = self.inner.header(&BlockId::Hash(hash)).ok()?
					.expect("Header known to exist after `best_containing` call; qed");

				Some((hash, header.number().clone()))
			}
			// Ok(None) can be returned when `block` is after `limit`. That might cause issues.
			// might be better to return the header itself in this (rare) case.
			Ok(None) => None,
			Err(e) => {
				debug!(target: "afg", "Encountered error finding best chain containing {:?}: {:?}", block, e);
				None
			}
		}
	}
}

/// A scheduled change of authority set.
#[derive(Debug, PartialEq)]
pub struct ScheduledChange<N> {
	/// The new authorities after the change, along with their respective weights.
	pub next_authorities: Vec<(AuthorityId, u64)>,
	/// The number of blocks to delay.
	pub delay: N,
}

/// A GRANDPA-compatible DigestItem. This can describe when GRANDPA set changes
/// are scheduled.
//
// With specialization, could do a blanket implementation so this trait
// doesn't have to be implemented by users.
pub trait CompatibleDigestItem<N> {
	/// If this digest item notes a GRANDPA set change, return information about
	/// the scheduled change.
	fn scheduled_change(&self) -> Option<ScheduledChange<N>> { None }
}

/// A new authority set along with the canonical block it changed at.
#[derive(Debug)]
struct NewAuthoritySet<H, N> {
	canon_number: N,
	canon_hash: H,
	set_id: u64,
	authorities: Vec<(AuthorityId, u64)>,
}

/// Signals either an early exit of a voter or an error.
#[derive(Debug)]
enum ExitOrError<H, N> {
	/// An error occurred.
	Error(Error),
	/// Early exit of the voter: the new set ID and the new authorities along with respective weights.
	AuthoritiesChanged(NewAuthoritySet<H, N>),
}

impl<H, N> From<Error> for ExitOrError<H, N> {
	fn from(e: Error) -> Self {
		ExitOrError::Error(e)
	}
}

impl<H, N> From<ClientError> for ExitOrError<H, N> {
	fn from(e: ClientError) -> Self {
		ExitOrError::Error(Error::Client(e))
	}
}

impl<H, N> From<grandpa::Error> for ExitOrError<H, N> {
	fn from(e: grandpa::Error) -> Self {
		ExitOrError::Error(Error::from(e))
	}
}

impl<B, E, Block: BlockT, N> voter::Environment<Block::Hash, NumberFor<Block>> for Environment<B, E, Block, N> where
	Block: 'static,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static,
	N: Network + 'static,
	N::In: 'static,
	NumberFor<Block>: BlockNumberOps,
	DigestItemFor<Block>: CompatibleDigestItem<NumberFor<Block>>,
{
	type Timer = Box<Future<Item = (), Error = Self::Error>>;
	type Id = AuthorityId;
	type Signature = ed25519::Signature;
	type In = Box<Stream<
		Item = ::grandpa::SignedMessage<Block::Hash, NumberFor<Block>, Self::Signature, Self::Id>,
		Error = Self::Error,
	>>;
	type Out = Box<Sink<
		SinkItem = ::grandpa::Message<Block::Hash, NumberFor<Block>>,
		SinkError = Self::Error,
	>>;
	type Error = ExitOrError<Block::Hash, NumberFor<Block>>;

	#[allow(unreachable_code)]
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
			round,
			self.set_id,
			self.network.messages_for(round),
			self.voters.clone(),
		);

		let (out_rx, outgoing) = outgoing_messages::<Block, _>(
			round,
			self.set_id,
			self.config.local_key.clone(),
			self.voters.clone(),
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
		let incoming = Box::new(incoming.select(out_rx).map_err(Into::into));

		// schedule network message cleanup when sink drops.
		let outgoing = Box::new(ClearOnDrop {
			round,
			network: self.network.clone(),
			inner: outgoing.sink_map_err(Into::into),
		});

		voter::RoundData {
			prevote_timer: Box::new(prevote_timer.map_err(|e| Error::Timer(e).into())),
			precommit_timer: Box::new(precommit_timer.map_err(|e| Error::Timer(e).into())),
			voters: (&*self.voters).clone(),
			incoming,
			outgoing,
		}
	}

	fn completed(&self, round: u64, state: RoundState<Block::Hash, NumberFor<Block>>) -> Result<(), Self::Error> {
		let encoded_state = (round, state).encode();
		if let Err(e) = self.inner.backend()
			.insert_aux(&[(LAST_COMPLETED_KEY, &encoded_state[..])], &[])
		{
			warn!(target: "afg", "Shutting down voter due to error bookkeeping last completed round in DB: {:?}", e);
			Err(Error::Client(e).into())
		} else {
			Ok(())
		}
	}

	fn finalize_block(&self, hash: Block::Hash, number: NumberFor<Block>) -> Result<(), Self::Error> {
		// ideally some handle to a synchronization oracle would be used
		// to avoid unconditionally notifying.
		if let Err(e) = self.inner.finalize_block(BlockId::Hash(hash), true) {
			warn!(target: "afg", "Error applying finality to block {:?}: {:?}", (hash, number), e);

			// we return without error because not being able to finalize (temporarily) is
			// non-fatal.
			return Ok(());
		}

		self.authority_set.with_mut(|authority_set| {
			let client = &self.inner;
			let status = authority_set.apply_changes(number, |canon_number| {
				client.block_hash_from_id(&BlockId::number(canon_number))
					.map(|h| h.expect("given number always less than newly-finalized number; \
						thus there is a block with that number finalized already; qed"))
			})?;

			if status.changed {
				// TODO [now]: write to disk. if it fails, exit the node.
				// write `authorities.encode()`

				if let Some((ref canon_hash, ref canon_number)) = status.new_set_block {
					// write `LastFinalized` entry with `RoundState::genesis(canon)`.
				}
			}

			if let Some((canon_hash, canon_number)) = status.new_set_block {
				// the authority set has changed.
				let (new_id, set_ref) = authority_set.current();
				return Err(ExitOrError::AuthoritiesChanged(NewAuthoritySet {
					canon_hash,
					canon_number,
					set_id: new_id,
					authorities: set_ref.to_vec(),
				}));
			}

			Ok(())
		})
	}

	fn prevote_equivocation(
		&self,
		_round: u64,
		equivocation: ::grandpa::Equivocation<Self::Id, Prevote<Block>, Self::Signature>
	) {
		warn!(target: "afg", "Detected prevote equivocation in the finality worker: {:?}", equivocation);
		// nothing yet; this could craft misbehavior reports of some kind.
	}

	fn precommit_equivocation(
		&self,
		_round: u64,
		equivocation: Equivocation<Self::Id, Precommit<Block>, Self::Signature>
	) {
		warn!(target: "afg", "Detected precommit equivocation in the finality worker: {:?}", equivocation);
		// nothing yet
	}
}

/// A block-import handler for GRANDPA.
///
/// This scans each imported block for signals of changing authority set.
/// When using GRANDPA, the block import worker should be using this block import
/// object.
pub struct GrandpaBlockImport<B, E, Block: BlockT> {
	inner: Arc<Client<B, E, Block>>,
	authority_set: SharedAuthoritySet<Block::Hash, NumberFor<Block>>,
}

impl<B, E, Block: BlockT> BlockImport<Block> for GrandpaBlockImport<B, E, Block> where
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static + Clone,
	DigestItemFor<Block>: CompatibleDigestItem<NumberFor<Block>>,
{
	type Error = ClientError;

	fn import_block(&self, block: ImportBlock<Block>, new_authorities: Option<Vec<AuthorityId>>)
		-> Result<ImportResult, Self::Error>
	{
		use runtime_primitives::traits::Digest;
		use authorities::PendingChange;

		let maybe_event = block.header.digest().logs().iter()
			.filter_map(|log| log.scheduled_change())
			.next()
			.map(|change| (block.header.hash(), *block.header.number(), change));

		let result = self.inner.import_block(block, new_authorities);
		if let (true, Some((hash, number, change))) = (result.is_ok(), maybe_event) {
			self.authority_set.add_pending_change(PendingChange {
				next_authorities: change.next_authorities,
				finalization_depth: number + change.delay,
				canon_height: number,
				canon_hash: hash,
			});

			// TODO [now]: write to DB, and what to do on failure?
		}

		result
	}
}

/// Run a GRANDPA voter as a task. This returns two pieces of data: a task to run,
/// and a `BlockImport` implementation.
pub fn run_grandpa<B, E, Block: BlockT, N>(
	config: Config,
	client: Arc<Client<B, E, Block>>,
	voters: HashMap<AuthorityId, u64>,
	network: N,
) -> ::client::error::Result<(
	impl Future<Item=(),Error=()>,
	GrandpaBlockImport<B, E, Block>,
)> where
	Block::Hash: Ord,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static,
	N: Network + 'static,
	N::In: 'static,
	NumberFor<Block>: BlockNumberOps,
	DigestItemFor<Block>: CompatibleDigestItem<NumberFor<Block>>,
{
	use futures::future::{self, Loop as FutureLoop};

	use runtime_primitives::traits::Zero;

	let chain_info = client.info()?;
	let genesis_hash = chain_info.chain.genesis_hash;

	// TODO [now]: attempt to load from disk.
	let authority_set = SharedAuthoritySet::genesis(
		voters.iter().map(|(&id, &weight)| (id, weight)).collect(),
	);

	let block_import = GrandpaBlockImport {
		inner: client.clone(),
		authority_set: authority_set.clone(),
	};

	let (last_round_number, last_state) = match client.backend().get_aux(LAST_COMPLETED_KEY)? {
		None => (0, RoundState::genesis((genesis_hash, <NumberFor<Block>>::zero()))),
		Some(raw) => LastCompleted::decode(&mut &raw[..])
			.ok_or_else(|| ::client::error::ErrorKind::Backend(
				format!("Last GRANDPA round state kept in invalid format")
			))?
	};

	let initial_environment = Arc::new(Environment {
		inner: client.clone(),
		config: config.clone(),
		voters: Arc::new(voters),
		network: network.clone(),
		set_id: authority_set.set_id(),
		authority_set: authority_set.clone(),
	});

	let voters = future::loop_fn((initial_environment, last_round_number, last_state), move |params| {
		let (env, last_round_number, last_state) = params;
		let chain_info = match client.info() {
			Ok(i) => i,
			Err(e) => return future::Either::B(future::err(Error::Client(e))),
		};

		let last_finalized = (
			chain_info.chain.finalized_hash,
			chain_info.chain.finalized_number,
		);

		let voter = voter::Voter::new(env, last_round_number, last_state, last_finalized);
		let client = client.clone();
		let config = config.clone();
		let network = network.clone();
		let authority_set = authority_set.clone();
		future::Either::A(voter.then(move |res| match res {
			// voters don't conclude naturally; this could reasonably be an error.
			Ok(()) => Ok(FutureLoop::Break(())),
			Err(ExitOrError::Error(e)) => Err(e),
			Err(ExitOrError::AuthoritiesChanged(new)) => {
				let env = Arc::new(Environment {
					inner: client,
					config,
					voters: Arc::new(new.authorities.into_iter().collect()),
					set_id: new.set_id,
					network,
					authority_set,
				});

				// start the new authority set using the block where the
				// set changed (not where the signal happened!) as the base.
				Ok(FutureLoop::Continue((
					env,
					0, // always start at round 0 when changing sets.
					RoundState::genesis((new.canon_hash, new.canon_number)),
				)))
			}
		}))
	});

	let work = voters.map_err(|e| warn!("GRANDPA Voter failed: {:?}", e));

	Ok((work, block_import))
}

#[cfg(test)]
mod tests {
	use super::*;
	use network::test::*;
	use parking_lot::Mutex;
	use tokio::runtime::current_thread;
	use keyring::Keyring;
	use client::BlockchainEvents;

	impl CompatibleDigestItem<NumberFor<Block>> for DigestItemFor<Block> { }

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
			let (voter, _) = run_grandpa(
				Config {
					gossip_duration: TEST_GOSSIP_DURATION,
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
			let (voter, _) = run_grandpa(
				Config {
					gossip_duration: TEST_GOSSIP_DURATION,
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
