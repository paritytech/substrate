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
extern crate substrate_network as network;
extern crate substrate_primitives;
extern crate tokio;
extern crate parking_lot;
extern crate parity_codec as codec;
extern crate substrate_finality_grandpa_primitives as fg_primitives;
extern crate rand;

#[macro_use]
extern crate log;

#[cfg(feature="service-integration")]
extern crate substrate_service as service;

#[cfg(test)]
extern crate substrate_keyring as keyring;

#[cfg(test)]
extern crate substrate_test_client as test_client;

#[cfg(test)]
extern crate env_logger;

#[macro_use]
extern crate parity_codec_derive;

use futures::prelude::*;
use futures::sync::mpsc;
use client::{
	Client, error::Error as ClientError, backend::Backend, CallExecutor, BlockchainEvents
};
use client::blockchain::HeaderBackend;
use client::runtime_api::TaggedTransactionQueue;
use codec::{Encode, Decode};
use consensus_common::{BlockImport, ImportBlock, ImportResult, Authorities};
use runtime_primitives::traits::{
	NumberFor, Block as BlockT, Header as HeaderT, DigestFor, ProvideRuntimeApi, Hash as HashT,
};
use fg_primitives::GrandpaApi;
use runtime_primitives::generic::BlockId;
use substrate_primitives::{ed25519, H256, AuthorityId, Blake2Hasher};
use tokio::timer::Delay;

use grandpa::Error as GrandpaError;
use grandpa::{voter, round::State as RoundState, Equivocation, BlockNumberOps};

use network::{Service as NetworkService, ExHashT};
use network::consensus_gossip::{ConsensusMessage};
use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;
use std::time::{Instant, Duration};

use authorities::SharedAuthoritySet;
use until_imported::{UntilCommitBlocksImported, UntilVoteTargetImported};

pub use fg_primitives::ScheduledChange;

mod authorities;
mod communication;
mod until_imported;

#[cfg(feature="service-integration")]
mod service_integration;
#[cfg(feature="service-integration")]
pub use service_integration::{LinkHalfForService, BlockImportForService};

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
/// A commit message for this chain's block type.
pub type Commit<Block> = grandpa::Commit<
	<Block as BlockT>::Hash,
	NumberFor<Block>,
	ed25519::Signature,
	AuthorityId
>;
/// A compact commit message for this chain's block type.
pub type CompactCommit<Block> = grandpa::CompactCommit<
	<Block as BlockT>::Hash,
	NumberFor<Block>,
	ed25519::Signature,
	AuthorityId
>;

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

	/// Get a stream of commit messages for a specific set-id. This stream
	/// should never logically conclude.
	fn commit_messages(&self, set_id: u64) -> Self::In;

	/// Send message over the commit channel.
	fn send_commit(&self, set_id: u64, message: Vec<u8>);
}

///  Bridge between NetworkService, gossiping consensus messages and Grandpa
pub struct NetworkBridge<B: BlockT, S: network::specialization::NetworkSpecialization<B>, H: ExHashT> {
	service: Arc<NetworkService<B, S, H>>
}

impl<B: BlockT, S: network::specialization::NetworkSpecialization<B>, H: ExHashT> NetworkBridge<B, S, H> {
	/// Create a new NetworkBridge to the given NetworkService
	pub fn new(service: Arc<NetworkService<B, S, H>>) -> Self {
		NetworkBridge { service }
	}
}

impl<B: BlockT, S: network::specialization::NetworkSpecialization<B>, H: ExHashT> Clone for NetworkBridge<B, S, H> {
	fn clone(&self) -> Self {
		NetworkBridge {
			service: Arc::clone(&self.service)
		}
	}
}

fn message_topic<B: BlockT>(round: u64, set_id: u64) -> B::Hash {
	<<B::Header as HeaderT>::Hashing as HashT>::hash(format!("{}-{}", set_id, round).as_bytes())
}

fn commit_topic<B: BlockT>(set_id: u64) -> B::Hash {
	<<B::Header as HeaderT>::Hashing as HashT>::hash(format!("{}-COMMITS", set_id).as_bytes())
}

impl<B: BlockT, S: network::specialization::NetworkSpecialization<B>, H: ExHashT> Network for NetworkBridge<B, S, H> {
	type In = mpsc::UnboundedReceiver<ConsensusMessage>;
	fn messages_for(&self, round: u64, set_id: u64) -> Self::In {
		self.service.consensus_gossip().write().messages_for(message_topic::<B>(round, set_id))
	}

	fn send_message(&self, round: u64, set_id: u64, message: Vec<u8>) {
		let topic = message_topic::<B>(round, set_id);
		self.service.gossip_consensus_message(topic, message);
	}

	fn drop_messages(&self, round: u64, set_id: u64) {
		let topic = message_topic::<B>(round, set_id);
		self.service.consensus_gossip().write().collect_garbage(|t| t == &topic);
	}

	fn commit_messages(&self, set_id: u64) -> Self::In {
		self.service.consensus_gossip().write().messages_for(commit_topic::<B>(set_id))
	}

	fn send_commit(&self, set_id: u64, message: Vec<u8>) {
		let topic = commit_topic::<B>(set_id);
		self.service.gossip_consensus_message(topic, message);
	}
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
		if base == block { return Err(GrandpaError::NotDescendent) }

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
		debug!(target: "afg", "Finding best chain containing block {:?} with number limit {:?}", block, limit);

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

impl<H: fmt::Debug, N: fmt::Debug> ::std::error::Error for ExitOrError<H, N> { }

impl<H, N> fmt::Display for ExitOrError<H, N> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			ExitOrError::Error(ref e) => write!(f, "{:?}", e),
			ExitOrError::AuthoritiesChanged(_) => write!(f, "restarting voter on new authorities"),
		}
	}
}

impl<B, E, Block: BlockT<Hash=H256>, N, RA> voter::Environment<Block::Hash, NumberFor<Block>> for Environment<B, E, Block, N, RA> where
	Block: 'static,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static + Send + Sync,
	N: Network + 'static + Send,
	N::In: 'static + Send,
	RA: 'static + Send + Sync,
	NumberFor<Block>: BlockNumberOps,
{
	type Timer = Box<dyn Future<Item = (), Error = Self::Error> + Send>;
	type Id = AuthorityId;
	type Signature = ed25519::Signature;

	// regular round message streams
	type In = Box<dyn Stream<
		Item = ::grandpa::SignedMessage<Block::Hash, NumberFor<Block>, Self::Signature, Self::Id>,
		Error = Self::Error,
	> + Send>;
	type Out = Box<dyn Sink<
		SinkItem = ::grandpa::Message<Block::Hash, NumberFor<Block>>,
		SinkError = Self::Error,
	> + Send>;

	type Error = ExitOrError<Block::Hash, NumberFor<Block>>;

	fn round_data(
		&self,
		round: u64
	) -> voter::RoundData<Self::Timer, Self::In, Self::Out> {
		let now = Instant::now();
		let prevote_timer = Delay::new(now + self.config.gossip_duration * 2);
		let precommit_timer = Delay::new(now + self.config.gossip_duration * 4);

		// TODO: dispatch this with `mpsc::spawn`.
		let incoming = ::communication::checked_message_stream::<Block, _>(
			round,
			self.set_id,
			self.network.messages_for(round, self.set_id),
			self.voters.clone(),
		);

		let (out_rx, outgoing) = ::communication::outgoing_messages::<Block, _>(
			round,
			self.set_id,
			self.config.local_key.clone(),
			self.voters.clone(),
			self.network.clone(),
		);

		// schedule incoming messages from the network to be held until
		// corresponding blocks are imported.
		let incoming = UntilVoteTargetImported::new(
			self.inner.import_notification_stream(),
			self.inner.clone(),
			incoming,
		);

		// join incoming network messages with locally originating ones.
		let incoming = Box::new(out_rx.select(incoming).map_err(Into::into));

		// schedule network message cleanup when sink drops.
		let outgoing = Box::new(outgoing.sink_map_err(Into::into));

		voter::RoundData {
			prevote_timer: Box::new(prevote_timer.map_err(|e| Error::Timer(e).into())),
			precommit_timer: Box::new(precommit_timer.map_err(|e| Error::Timer(e).into())),
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

	fn finalize_block(&self, hash: Block::Hash, number: NumberFor<Block>, _commit: Commit<Block>) -> Result<(), Self::Error> {
		// ideally some handle to a synchronization oracle would be used
		// to avoid unconditionally notifying.
		if let Err(e) = self.inner.finalize_block(BlockId::Hash(hash), true) {
			warn!(target: "afg", "Error applying finality to block {:?}: {:?}", (hash, number), e);

			// we return without error because not being able to finalize (temporarily) is
			// non-fatal.
			return Ok(());
		}

		debug!(target: "afg", "Finalizing blocks up to ({:?}, {})", number, hash);

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

	fn round_commit_timer(&self) -> Self::Timer {
		use rand::{thread_rng, Rng};

		//random between 0-1 seconds.
		let delay: u64 = thread_rng().gen_range(0, 1000);
		Box::new(Delay::new(
			Instant::now() + Duration::from_millis(delay)
		).map_err(|e| Error::Timer(e).into()))
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
pub struct GrandpaBlockImport<B, E, Block: BlockT<Hash=H256>, RA, PRA> {
	inner: Arc<Client<B, E, Block, RA>>,
	authority_set: SharedAuthoritySet<Block::Hash, NumberFor<Block>>,
	api: Arc<PRA>,
}

impl<B, E, Block: BlockT<Hash=H256>, RA, PRA> BlockImport<Block>
	for GrandpaBlockImport<B, E, Block, RA, PRA> where
		B: Backend<Block, Blake2Hasher> + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		DigestFor<Block>: Encode,
		RA: TaggedTransactionQueue<Block>,
		PRA: ProvideRuntimeApi,
		PRA::Api: GrandpaApi<Block>
{
	type Error = ClientError;

	fn import_block(&self, mut block: ImportBlock<Block>, new_authorities: Option<Vec<AuthorityId>>)
		-> Result<ImportResult, Self::Error>
	{
		use authorities::PendingChange;

		let maybe_change = self.api.runtime_api().grandpa_pending_change(
			&BlockId::hash(*block.header.parent_hash()),
			&block.header.digest().clone(),
		)?;

		// when we update the authorities, we need to hold the lock
		// until the block is written to prevent a race if we need to restore
		// the old authority set on error.
		let just_in_case = maybe_change.map(|change| {
			let hash = block.post_header().hash();
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

impl<B, E, Block: BlockT<Hash=H256>, RA, PRA> Authorities<Block> for GrandpaBlockImport<B, E, Block, RA, PRA>
where
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
	RA: TaggedTransactionQueue<Block>, // necessary for client to import `BlockImport`.
{

	type Error = <Client<B, E, Block, RA> as Authorities<Block>>::Error;
	fn authorities(&self, at: &BlockId<Block>) -> Result<Vec<AuthorityId>, Self::Error> {
		self.inner.authorities_at(at)
	}
}

/// Half of a link between a block-import worker and a the background voter.
// This should remain non-clone.
pub struct LinkHalf<B, E, Block: BlockT<Hash=H256>, RA> {
	client: Arc<Client<B, E, Block, RA>>,
	authority_set: SharedAuthoritySet<Block::Hash, NumberFor<Block>>,
}
impl<B, E, Block: BlockT<Hash=H256>, RA> Clone for LinkHalf<B, E, Block, RA>
where
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
	RA: TaggedTransactionQueue<Block>, // necessary for client to import `BlockImport`.
{
	fn clone(&self) -> Self {
		LinkHalf {
			client: self.client.clone(),
			authority_set: self.authority_set.clone()
		}
	}
}

/// Make block importer and link half necessary to tie the background voter
/// to it.
pub fn block_import<B, E, Block: BlockT<Hash=H256>, RA, PRA>(
	client: Arc<Client<B, E, Block, RA>>,
	api: Arc<PRA>
) -> Result<(GrandpaBlockImport<B, E, Block, RA, PRA>, LinkHalf<B, E, Block, RA>), ClientError>
	where
		B: Backend<Block, Blake2Hasher> + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		RA: Send + Sync,
		PRA: ProvideRuntimeApi,
		PRA::Api: GrandpaApi<Block>
{
	use runtime_primitives::traits::Zero;
	let authority_set = match client.backend().get_aux(AUTHORITY_SET_KEY)? {
		None => {
			info!(target: "afg", "Loading GRANDPA authorities \
				from genesis on what appears to be first startup.");

			// no authority set on disk: fetch authorities from genesis state.
			// if genesis state is not available, we may be a light client, but these
			// are unsupported for following GRANDPA directly.
			let genesis_authorities = api.runtime_api()
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
		GrandpaBlockImport {
			inner: client.clone(),
			authority_set: authority_set.clone(),
			api
		},
		LinkHalf { client, authority_set },
	))
}

fn committer_communication<Block: BlockT<Hash=H256>, B, E, N, RA>(
	set_id: u64,
	voters: &Arc<HashMap<AuthorityId, u64>>,
	client: &Arc<Client<B, E, Block, RA>>,
	network: &N,
) -> (
	impl Stream<
		Item = (u64, ::grandpa::CompactCommit<H256, NumberFor<Block>, ed25519::Signature, AuthorityId>),
		Error = ExitOrError<H256, NumberFor<Block>>,
	>,
	impl Sink<
		SinkItem = (u64, ::grandpa::Commit<H256, NumberFor<Block>, ed25519::Signature, AuthorityId>),
		SinkError = ExitOrError<H256, NumberFor<Block>>,
	>,
) where
	B: Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync,
	N: Network,
	RA: Send + Sync,
	NumberFor<Block>: BlockNumberOps,
{
	// verification stream
	let commit_in = ::communication::checked_commit_stream::<Block, _>(
		set_id,
		network.commit_messages(set_id),
		voters.clone(),
	);

	// block commit messages until relevant blocks are imported.
	let commit_in = UntilCommitBlocksImported::new(
		client.import_notification_stream(),
		client.clone(),
		commit_in,
	);

	let commit_out = ::communication::CommitsOut::<Block, _>::new(
		network.clone(),
		set_id,
	);

	let commit_in = commit_in.map_err(Into::into);
	let commit_out = commit_out.sink_map_err(Into::into);

	(commit_in, commit_out)
}

/// Run a GRANDPA voter as a task. Provide configuration and a link to a
/// block import worker that has already been instantiated with `block_import`.
pub fn run_grandpa<B, E, Block: BlockT<Hash=H256>, N, RA>(
	config: Config,
	link: LinkHalf<B, E, Block, RA>,
	network: N,
) -> ::client::error::Result<impl Future<Item=(),Error=()> + Send + 'static> where
	Block::Hash: Ord,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
	N: Network + Send + Sync + 'static,
	N::In: Send + 'static,
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

		let committer_data = committer_communication(
			env.set_id,
			&env.voters,
			&client,
			&network,
		);

		let voters = (*env.voters).clone();

		let voter = voter::Voter::new(
			env,
			voters,
			committer_data,
			last_round_number,
			last_state,
			last_finalized,
		);
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
