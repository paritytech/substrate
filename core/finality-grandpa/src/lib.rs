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
//! This crate provides a long-running future that produces finality notifications.
//!
//! # Usage
//!
//! First, create a block-import wrapper with the `block_import` function.
//! The GRANDPA worker needs to be linked together with this block import object,
//! so a `LinkHalf` is returned as well. All blocks imported (from network or consensus or otherwise)
//! must pass through this wrapper, otherwise consensus is likely to break in
//! unexpected ways.
//!
//! Next, use the `LinkHalf` and a local configuration to `run_grandpa`. This requires a
//! `Network` implementation. The returned future should be driven to completion and
//! will finalize blocks in the background.
//!
//! # Changing authority sets
//!
//! The rough idea behind changing authority sets in GRANDPA is that at some point,
//! we obtain agreement for some maximum block height that the current set can
//! finalize, and once a block with that height is finalized the next set will
//! pick up finalization from there.
//!
//! Technically speaking, this would be implemented as a voting rule which says,
//! "if there is a signal for a change in N blocks in block B, only vote on
//! chains with length NUM(B) + N if they contain B". This conditional-inclusion
//! logic is complex to compute because it requires looking arbitrarily far
//! back in the chain.
//!
//! Instead, we keep track of a list of all signals we've seen so far,
//! sorted ascending by the block number they would be applied at. We never vote
//! on chains with number higher than the earliest handoff block number
//! (this is num(signal) + N). When finalizing a block, we either apply or prune
//! any signaled changes based on whether the signaling block is included in the
//! newly-finalized chain.

extern crate finality_grandpa as grandpa;
extern crate futures;
extern crate substrate_client as client;
extern crate sr_primitives as runtime_primitives;
extern crate substrate_consensus_common as consensus_common;
extern crate substrate_primitives;
extern crate tokio;
extern crate parking_lot;
extern crate parity_codec as codec;
extern crate substrate_fg_primitives as fg_primitives;

#[macro_use]
extern crate log;

#[cfg(test)]
extern crate substrate_network as network;

#[cfg(test)]
extern crate substrate_keyring as keyring;

#[cfg(test)]
extern crate substrate_test_client as test_client;

#[cfg(test)]
extern crate env_logger;

#[macro_use]
extern crate parity_codec_derive;

use futures::prelude::*;
use futures::stream::Fuse;
use futures::sync::mpsc;
use client::{Client, error::Error as ClientError, ImportNotifications, backend::Backend, CallExecutor};
use client::blockchain::HeaderBackend;
use client::runtime_api::TaggedTransactionQueue;
use codec::{Encode, Decode};
use consensus_common::{BlockImport, ImportBlock, ImportResult};
use runtime_primitives::traits::{
	NumberFor, Block as BlockT, Header as HeaderT, DigestFor, ProvideRuntimeApi
};
use fg_primitives::GrandpaApi;
use runtime_primitives::generic::BlockId;
use substrate_primitives::{ed25519, H256, AuthorityId, Blake2Hasher};
use tokio::timer::Interval;

use grandpa::Error as GrandpaError;
use grandpa::{voter, round::State as RoundState, Equivocation, BlockNumberOps};

use std::collections::{VecDeque, HashMap};
use std::sync::Arc;
use std::time::{Instant, Duration};

use authorities::SharedAuthoritySet;

pub use fg_primitives::ScheduledChange;

mod authorities;

#[cfg(test)]
mod tests;

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
	/// Some local identifier of the voter.
	pub name: Option<String>,
}

impl Config {
	fn name(&self) -> &str {
		self.name.as_ref().map(|s| s.as_str()).unwrap_or("<unknown>")
	}
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
	fn messages_for(&self, round: u64, set_id: u64) -> Self::In;

	/// Send a message at a specific round out.
	fn send_message(&self, round: u64, set_id: u64, message: Vec<u8>);

	/// Clean up messages for a round.
	fn drop_messages(&self, round: u64, set_id: u64);
}

/// Something which can determine if a block is known.
pub trait BlockStatus<Block: BlockT> {
	/// Return `Ok(Some(number))` or `Ok(None)` depending on whether the block
	/// is definitely known and has been imported.
	/// If an unexpected error occurs, return that.
	fn block_number(&self, hash: Block::Hash) -> Result<Option<NumberFor<Block>>, Error>;
}

impl<B, E, Block: BlockT<Hash=H256>, RA> BlockStatus<Block> for Arc<Client<B, E, Block, RA>> where
	B: Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync,
	RA: Send + Sync,
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
	set_id: u64,
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
		self.network.drop_messages(self.round, self.set_id);
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
				network.send_message(round, set_id, signed.encode());
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
struct Environment<B, E, Block: BlockT, N: Network, RA> {
	inner: Arc<Client<B, E, Block, RA>>,
	voters: Arc<HashMap<AuthorityId, u64>>,
	config: Config,
	authority_set: SharedAuthoritySet<Block::Hash, NumberFor<Block>>,
	network: N,
	set_id: u64,
}

impl<Block: BlockT<Hash=H256>, B, E, N, RA> grandpa::Chain<Block::Hash, NumberFor<Block>> for Environment<B, E, Block, N, RA> where
	Block: 'static,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static,
	N: Network + 'static,
	N::In: 'static,
	NumberFor<Block>: BlockNumberOps,
{
	fn ancestry(&self, base: Block::Hash, block: Block::Hash) -> Result<Vec<Block::Hash>, GrandpaError> {
		if base == block { return Err(NotDescendent) }

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
		trace!(target: "afg", "Finding best chain containing block {:?} with number limit {:?}", block, limit);

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

impl<B, E, Block: BlockT<Hash=H256>, N, RA> voter::Environment<Block::Hash, NumberFor<Block>> for Environment<B, E, Block, N, RA> where
	Block: 'static,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static + Send + Sync,
	N: Network + 'static,
	N::In: 'static,
	RA: 'static + Send + Sync,
	NumberFor<Block>: BlockNumberOps,
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
			self.network.messages_for(round, self.set_id),
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
		let incoming = Box::new(out_rx.select(incoming).map_err(Into::into));

		// schedule network message cleanup when sink drops.
		let outgoing = Box::new(ClearOnDrop {
			round,
			set_id: self.set_id,
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
		debug!(
			target: "afg", "Voter {} completed round {} in set {}. Estimate = {:?}, Finalized in round = {:?}",
			self.config.name(),
			round,
			self.set_id,
			state.estimate.as_ref().map(|e| e.1),
			state.finalized.as_ref().map(|e| e.1),
		);

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

		// lock must be held through writing to DB to avoid race
		let mut authority_set = self.authority_set.inner().write();
		let client = &self.inner;
		let status = authority_set.apply_changes(number, |canon_number| {
			client.block_hash_from_id(&BlockId::number(canon_number))
				.map(|h| h.expect("given number always less than newly-finalized number; \
					thus there is a block with that number finalized already; qed"))
		})?;

		if status.changed {
			// write new authority set state to disk.
			let encoded_set = authority_set.encode();

			let write_result = if let Some((ref canon_hash, ref canon_number)) = status.new_set_block {
				// we also overwrite the "last completed round" entry with a blank slate
				// because from the perspective of the finality gadget, the chain has
				// reset.
				let round_state = RoundState::genesis((*canon_hash, *canon_number));
				let last_completed: LastCompleted<_, _> = (0, round_state);
				let encoded = last_completed.encode();

				client.backend().insert_aux(
					&[
						(AUTHORITY_SET_KEY, &encoded_set[..]),
						(LAST_COMPLETED_KEY, &encoded[..]),
					],
					&[]
				)
			} else {
				client.backend().insert_aux(&[(AUTHORITY_SET_KEY, &encoded_set[..])], &[])
			};

			if let Err(e) = write_result {
				warn!(target: "finality", "Failed to write updated authority set to disk. Bailing.");
				warn!(target: "finality", "Node is in a potentially inconsistent state.");

				return Err(e.into());
			}
		}

		if let Some((canon_hash, canon_number)) = status.new_set_block {
			// the authority set has changed.
			let (new_id, set_ref) = authority_set.current();

			if set_ref.len() > 16 {
				info!("Applying GRANDPA set change to new set with {} authorities", set_ref.len());
			} else {
				info!("Applying GRANDPA set change to new set {:?}", set_ref);
			}
			Err(ExitOrError::AuthoritiesChanged(NewAuthoritySet {
				canon_hash,
				canon_number,
				set_id: new_id,
				authorities: set_ref.to_vec(),
			}))
		} else {
			Ok(())
		}
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
pub struct GrandpaBlockImport<B, E, Block: BlockT<Hash=H256>, RA> {
	inner: Arc<Client<B, E, Block, RA>>,
	authority_set: SharedAuthoritySet<Block::Hash, NumberFor<Block>>,
}

impl<B, E, Block: BlockT<Hash=H256>, RA> BlockImport<Block> for GrandpaBlockImport<B, E, Block, RA> where
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
	DigestFor<Block>: Encode,
	RA: GrandpaApi<Block> + TaggedTransactionQueue<Block>,
{
	type Error = ClientError;

	fn import_block(&self, mut block: ImportBlock<Block>, new_authorities: Option<Vec<AuthorityId>>)
		-> Result<ImportResult, Self::Error>
	{
		use authorities::PendingChange;

		let maybe_change = self.inner.runtime_api().grandpa_pending_change(
			&BlockId::hash(*block.header.parent_hash()),
			&block.header.digest().clone(),
		)?;

		// when we update the authorities, we need to hold the lock
		// until the block is written to prevent a race if we need to restore
		// the old authority set on error.
		let just_in_case = maybe_change.map(|change| {
			let hash = block.header.hash();
			let number = block.header.number().clone();

			let mut authorities = self.authority_set.inner().write();
			let old_set = authorities.clone();
			authorities.add_pending_change(PendingChange {
				next_authorities: change.next_authorities,
				finalization_depth: change.delay,
				canon_height: number,
				canon_hash: hash,
			});

			block.auxiliary.push((AUTHORITY_SET_KEY.to_vec(), Some(authorities.encode())));
			(old_set, authorities)
		});

		let result = self.inner.import_block(block, new_authorities);
		if let Err(ref e) = result {
			if let Some((old_set, mut authorities)) = just_in_case {
				debug!(target: "afg", "Restoring old set after block import error: {:?}", e);
				*authorities = old_set;
			}
		}

		result
	}
}

/// Half of a link between a block-import worker and a the background voter.
// This should remain non-clone.
pub struct LinkHalf<B, E, Block: BlockT<Hash=H256>, RA> {
	client: Arc<Client<B, E, Block, RA>>,
	authority_set: SharedAuthoritySet<Block::Hash, NumberFor<Block>>,
}

/// Make block importer and link half necessary to tie the background voter
/// to it.
pub fn block_import<B, E, Block: BlockT<Hash=H256>, RA>(client: Arc<Client<B, E, Block, RA>>)
	-> Result<(GrandpaBlockImport<B, E, Block, RA>, LinkHalf<B, E, Block, RA>), ClientError>
	where
		B: Backend<Block, Blake2Hasher> + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		RA: GrandpaApi<Block>,
{
	use runtime_primitives::traits::Zero;
	let authority_set = match client.backend().get_aux(AUTHORITY_SET_KEY)? {
		None => {
			info!(target: "afg", "Loading GRANDPA authorities \
				from genesis on what appears to be first startup.");

			// no authority set on disk: fetch authorities from genesis state.
			// if genesis state is not available, we may be a light client, but these
			// are unsupported for following GRANDPA directly.
			let genesis_authorities = client.runtime_api()
				.grandpa_authorities(&BlockId::number(Zero::zero()))?;

			let authority_set = SharedAuthoritySet::genesis(genesis_authorities);
			let encoded = authority_set.inner().read().encode();
			client.backend().insert_aux(&[(AUTHORITY_SET_KEY, &encoded[..])], &[])?;

			authority_set
		}
		Some(raw) => ::authorities::AuthoritySet::decode(&mut &raw[..])
			.ok_or_else(|| ::client::error::ErrorKind::Backend(
				format!("GRANDPA authority set kept in invalid format")
			))?
			.into(),
	};

	Ok((
		GrandpaBlockImport { inner: client.clone(), authority_set: authority_set.clone() },
		LinkHalf { client, authority_set },
	))
}

/// Run a GRANDPA voter as a task. Provide configuration and a link to a
/// block import worker that has already been instantiated with `block_import`.
pub fn run_grandpa<B, E, Block: BlockT<Hash=H256>, N, RA>(
	config: Config,
	link: LinkHalf<B, E, Block, RA>,
	network: N,
) -> ::client::error::Result<impl Future<Item=(),Error=()>> where
	Block::Hash: Ord,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
	N: Network + 'static,
	N::In: 'static,
	NumberFor<Block>: BlockNumberOps,
	DigestFor<Block>: Encode,
	RA: Send + Sync + 'static,
{
	use futures::future::{self, Loop as FutureLoop};
	use runtime_primitives::traits::Zero;

	let LinkHalf { client, authority_set } = link;
	let chain_info = client.info()?;
	let genesis_hash = chain_info.chain.genesis_hash;

	let (last_round_number, last_state) = match client.backend().get_aux(LAST_COMPLETED_KEY)? {
		None => (0, RoundState::genesis((genesis_hash, <NumberFor<Block>>::zero()))),
		Some(raw) => LastCompleted::decode(&mut &raw[..])
			.ok_or_else(|| ::client::error::ErrorKind::Backend(
				format!("Last GRANDPA round state kept in invalid format")
			))?
	};

	let voters = authority_set.inner().read().current().1.iter()
		.cloned()
		.collect();

	let initial_environment = Arc::new(Environment {
		inner: client.clone(),
		config: config.clone(),
		voters: Arc::new(voters),
		network: network.clone(),
		set_id: authority_set.set_id(),
		authority_set: authority_set.clone(),
	});

	let work = future::loop_fn((initial_environment, last_round_number, last_state), move |params| {
		let (env, last_round_number, last_state) = params;
		debug!(target: "afg", "{}: Starting new voter with set ID {}", config.name(), env.set_id);

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

	Ok(work.map_err(|e| warn!("GRANDPA Voter failed: {:?}", e)))
}
