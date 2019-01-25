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
//! This crate is unstable and the API and usage may change.
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
	BlockchainEvents, CallExecutor, Client, backend::Backend,
	error::Error as ClientError, error::ErrorKind as ClientErrorKind,
};
use client::blockchain::HeaderBackend;
use codec::{Encode, Decode};
use consensus_common::{BlockImport, JustificationImport, Error as ConsensusError, ErrorKind as ConsensusErrorKind, ImportBlock, ImportResult};
use runtime_primitives::Justification;
use runtime_primitives::traits::{
	NumberFor, Block as BlockT, Header as HeaderT, DigestFor, ProvideRuntimeApi, Hash as HashT,
	DigestItemFor, DigestItem, As, One, Zero,
};
use fg_primitives::GrandpaApi;
use runtime_primitives::generic::BlockId;
use substrate_primitives::{ed25519, H256, Ed25519AuthorityId, Blake2Hasher};
use tokio::timer::Delay;

use grandpa::Error as GrandpaError;
use grandpa::{voter, round::State as RoundState, Equivocation, BlockNumberOps};

use network::{Service as NetworkService, ExHashT};
use network::consensus_gossip::{ConsensusMessage};
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::Arc;
use std::time::{Instant, Duration};

use authorities::SharedAuthoritySet;
use until_imported::{UntilCommitBlocksImported, UntilVoteTargetImported};

pub use fg_primitives::ScheduledChange;

mod authorities;
mod communication;
mod finality_proof;
mod until_imported;

#[cfg(feature="service-integration")]
mod service_integration;
#[cfg(feature="service-integration")]
pub use service_integration::{LinkHalfForService, BlockImportForService};

pub use finality_proof::{prove_finality, check_finality_proof};

#[cfg(test)]
mod tests;

const LAST_COMPLETED_KEY: &[u8] = b"grandpa_completed_round";
const AUTHORITY_SET_KEY: &[u8] = b"grandpa_voters";
const CONSENSUS_CHANGES_KEY: &[u8] = b"grandpa_consensus_changes";

/// round-number, round-state
type LastCompleted<H, N> = (u64, RoundState<H, N>);

/// A GRANDPA message for a substrate chain.
pub type Message<Block> = grandpa::Message<<Block as BlockT>::Hash, NumberFor<Block>>;
/// A signed message.
pub type SignedMessage<Block> = grandpa::SignedMessage<
	<Block as BlockT>::Hash,
	NumberFor<Block>,
	ed25519::Signature,
	Ed25519AuthorityId,
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
	Ed25519AuthorityId
>;
/// A compact commit message for this chain's block type.
pub type CompactCommit<Block> = grandpa::CompactCommit<
	<Block as BlockT>::Hash,
	NumberFor<Block>,
	ed25519::Signature,
	Ed25519AuthorityId
>;

/// Configuration for the GRANDPA service.
#[derive(Clone)]
pub struct Config {
	/// The expected duration for a message to be gossiped across the network.
	pub gossip_duration: Duration,
	/// Justification generation period (in blocks). GRANDPA will try to generate justifications
	/// at least every justification_period blocks. There are some other events which might cause
	/// justification generation.
	pub justification_period: u64,
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

impl From<ClientError> for Error {
	fn from(e: ClientError) -> Self {
		Error::Client(e)
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
	fn send_commit(&self, round: u64, set_id: u64, message: Vec<u8>);
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
		self.service.gossip_consensus_message(topic, message, false);
	}

	fn drop_messages(&self, round: u64, set_id: u64) {
		let topic = message_topic::<B>(round, set_id);
		self.service.consensus_gossip().write().collect_garbage(|t| t == &topic);
	}

	fn commit_messages(&self, set_id: u64) -> Self::In {
		self.service.consensus_gossip().write().messages_for(commit_topic::<B>(set_id))
	}

	fn send_commit(&self, _round: u64, set_id: u64, message: Vec<u8>) {
		let topic = commit_topic::<B>(set_id);
		self.service.gossip_consensus_message(topic, message, true);
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

/// Consensus-related data changes tracker.
#[derive(Clone, Debug, Encode, Decode)]
struct ConsensusChanges<H, N> {
	pending_changes: Vec<(N, H)>,
}

impl<H: Copy + PartialEq, N: Copy + Ord> ConsensusChanges<H, N> {
	/// Create empty consensus changes.
	pub fn empty() -> Self {
		ConsensusChanges { pending_changes: Vec::new(), }
	}

	/// Note unfinalized change of consensus-related data.
	pub fn note_change(&mut self, at: (N, H)) {
		let idx = self.pending_changes
			.binary_search_by_key(&at.0, |change| change.0)
			.unwrap_or_else(|i| i);
		self.pending_changes.insert(idx, at);
	}

	/// Finalize all pending consensus changes that are finalized by given block.
	/// Returns true if there any changes were finalized.
	pub fn finalize<F: Fn(N) -> ::client::error::Result<Option<H>>>(
		&mut self,
		block: (N, H),
		canonical_at_height: F,
	) -> ::client::error::Result<(bool, bool)> {
		let (split_idx, has_finalized_changes) = self.pending_changes.iter()
			.enumerate()
			.take_while(|(_, &(at_height, _))| at_height <= block.0)
			.fold((None, Ok(false)), |(_, has_finalized_changes), (idx, ref at)|
				(
					Some(idx),
					has_finalized_changes
						.and_then(|has_finalized_changes| if has_finalized_changes {
							Ok(has_finalized_changes)
						} else {
							canonical_at_height(at.0).map(|can_hash| Some(at.1) == can_hash)
						}),
				));

		let altered_changes = split_idx.is_some();
		if let Some(split_idx) = split_idx {
			self.pending_changes = self.pending_changes.split_off(split_idx + 1);
		}
		has_finalized_changes.map(|has_finalized_changes| (altered_changes, has_finalized_changes))
	}
}

/// Thread-safe consensus changes tracker reference.
type SharedConsensusChanges<H, N> = Arc<parking_lot::Mutex<ConsensusChanges<H, N>>>;

/// The environment we run GRANDPA in.
struct Environment<B, E, Block: BlockT, N: Network, RA> {
	inner: Arc<Client<B, E, Block, RA>>,
	voters: Arc<HashMap<Ed25519AuthorityId, u64>>,
	config: Config,
	authority_set: SharedAuthoritySet<Block::Hash, NumberFor<Block>>,
	consensus_changes: SharedConsensusChanges<Block::Hash, NumberFor<Block>>,
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

		match self.inner.best_containing(block, None) {
			Ok(Some(mut best_hash)) => {
				let base_header = self.inner.header(&BlockId::Hash(block)).ok()?
					.expect("Header known to exist after `best_containing` call; qed");

				if let Some(limit) = limit {
					// this is a rare case which might cause issues,
					// might be better to return the header itself.
					if *base_header.number() > limit {
						debug!(target: "afg", "Encountered error finding best chain containing {:?} with limit {:?}: target block is after limit",
							block,
							limit,
						);
						return None;
					}
				}

				let mut best_header = self.inner.header(&BlockId::Hash(best_hash)).ok()?
					.expect("Header known to exist after `best_containing` call; qed");

				// we target a vote towards 3/4 of the unfinalized chain (rounding up)
				let target = {
					let two = NumberFor::<Block>::one() + One::one();
					let three = two + One::one();
					let four = three + One::one();

					let diff = *best_header.number() - *base_header.number();
					let diff = ((diff * three) + two) / four;

					*base_header.number() + diff
				};

				// unless our vote is currently being limited due to a pending change
				let target = limit.map(|limit| limit.min(target)).unwrap_or(target);

				// walk backwards until we find the target block
				loop {
					if *best_header.number() < target { unreachable!(); }
					if *best_header.number() == target {
						return Some((best_hash, *best_header.number()));
					}

					best_hash = *best_header.parent_hash();
					best_header = self.inner.header(&BlockId::Hash(best_hash)).ok()?
						.expect("Header known to exist after `best_containing` call; qed");
				}
			},
			Ok(None) => {
				debug!(target: "afg", "Encountered error finding best chain containing {:?}: couldn't find target block", block);
				None
			}
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
	authorities: Vec<(Ed25519AuthorityId, u64)>,
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
	type Id = Ed25519AuthorityId;
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

		let local_key = self.config.local_key.as_ref()
			.filter(|pair| self.voters.contains_key(&pair.public().into()));

		let (out_rx, outgoing) = ::communication::outgoing_messages::<Block, _>(
			round,
			self.set_id,
			local_key.cloned(),
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
		let res = Backend::insert_aux(&**self.inner.backend(), &[(LAST_COMPLETED_KEY, &encoded_state[..])], &[]);
		if let Err(e) = res {
			warn!(target: "afg", "Shutting down voter due to error bookkeeping last completed round in DB: {:?}", e);
			Err(Error::Client(e).into())
		} else {
			Ok(())
		}
	}

	fn finalize_block(&self, hash: Block::Hash, number: NumberFor<Block>, round: u64, commit: Commit<Block>) -> Result<(), Self::Error> {
		finalize_block(
			&*self.inner,
			&self.authority_set,
			&self.consensus_changes,
			Some(As::sa(self.config.justification_period)),
			hash,
			number,
			(round, commit).into(),
		)
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

/// A GRANDPA justification for block finality, it includes a commit message and
/// an ancestry proof including all headers routing all precommit target blocks
/// to the commit target block. Due to the current voting strategy the precommit
/// targets should be the same as the commit target, since honest voters don't
/// vote past authority set change blocks.
///
/// This is meant to be stored in the db and passed around the network to other
/// nodes, and are used by syncing nodes to prove authority set handoffs.
#[derive(Encode, Decode)]
struct GrandpaJustification<Block: BlockT> {
	round: u64,
	commit: Commit<Block>,
	votes_ancestries: Vec<Block::Header>,
}

impl<Block: BlockT<Hash=H256>> GrandpaJustification<Block> {
	/// Create a GRANDPA justification from the given commit. This method
	/// assumes the commit is valid and well-formed.
	fn from_commit<B, E, RA>(
		client: &Client<B, E, Block, RA>,
		round: u64,
		commit: Commit<Block>,
	) -> Result<GrandpaJustification<Block>, Error> where
		B: Backend<Block, Blake2Hasher>,
		E: CallExecutor<Block, Blake2Hasher> + Send + Sync,
		RA: Send + Sync,
	{
		let mut votes_ancestries_hashes = HashSet::new();
		let mut votes_ancestries = Vec::new();

		let error = || {
			let msg = "invalid precommits for target commit".to_string();
			Err(Error::Client(ClientErrorKind::BadJustification(msg).into()))
		};

		for signed in commit.precommits.iter() {
			let mut current_hash = signed.precommit.target_hash.clone();
			loop {
				if current_hash == commit.target_hash { break; }

				match client.backend().blockchain().header(BlockId::Hash(current_hash))? {
					Some(current_header) => {
						if *current_header.number() <= commit.target_number {
							return error();
						}

						let parent_hash = current_header.parent_hash().clone();
						if votes_ancestries_hashes.insert(current_hash) {
							votes_ancestries.push(current_header);
						}
						current_hash = parent_hash;
					},
					_ => return error(),
				}
			}
		}

		Ok(GrandpaJustification { round, commit, votes_ancestries })
	}

	/// Decode a GRANDPA justification and validate the commit and the votes'
	/// ancestry proofs.
	fn decode_and_verify(
		encoded: Vec<u8>,
		set_id: u64,
		voters: &HashMap<Ed25519AuthorityId, u64>,
	) -> Result<GrandpaJustification<Block>, ClientError> where
		NumberFor<Block>: grandpa::BlockNumberOps,
	{
		GrandpaJustification::<Block>::decode(&mut &*encoded).ok_or_else(|| {
			let msg = "failed to decode grandpa justification".to_string();
			ClientErrorKind::BadJustification(msg).into()
		}).and_then(|just| just.verify(set_id, voters).map(|_| just))
	}

	/// Validate the commit and the votes' ancestry proofs.
	fn verify(&self, set_id: u64, voters: &HashMap<Ed25519AuthorityId, u64>) -> Result<(), ClientError>
	where
		NumberFor<Block>: grandpa::BlockNumberOps,
	{
		use grandpa::Chain;

		let ancestry_chain = AncestryChain::<Block>::new(&self.votes_ancestries);

		match grandpa::validate_commit(
			&self.commit,
			voters,
			None,
			&ancestry_chain,
		) {
			Ok(Some(_)) => {},
			_ => {
				let msg = "invalid commit in grandpa justification".to_string();
				return Err(ClientErrorKind::BadJustification(msg).into());
			}
		}

		let mut visited_hashes = HashSet::new();
		for signed in self.commit.precommits.iter() {
			if let Err(_) = communication::check_message_sig::<Block>(
				&grandpa::Message::Precommit(signed.precommit.clone()),
				&signed.id,
				&signed.signature,
				self.round,
				set_id,
			) {
				return Err(ClientErrorKind::BadJustification(
					"invalid signature for precommit in grandpa justification".to_string()).into());
			}

			if self.commit.target_hash == signed.precommit.target_hash {
				continue;
			}

			match ancestry_chain.ancestry(self.commit.target_hash, signed.precommit.target_hash) {
				Ok(route) => {
					// ancestry starts from parent hash but the precommit target hash has been visited
					visited_hashes.insert(signed.precommit.target_hash);
					for hash in route {
						visited_hashes.insert(hash);
					}
				},
				_ => {
					return Err(ClientErrorKind::BadJustification(
						"invalid precommit ancestry proof in grandpa justification".to_string()).into());
				},
			}
		}

		let ancestry_hashes = self.votes_ancestries
			.iter()
			.map(|h: &Block::Header| h.hash())
			.collect();

		if visited_hashes != ancestry_hashes {
			return Err(ClientErrorKind::BadJustification(
				"invalid precommit ancestries in grandpa justification with unused headers".to_string()).into());
		}

		Ok(())
	}
}

enum JustificationOrCommit<Block: BlockT> {
	Justification(GrandpaJustification<Block>),
	Commit((u64, Commit<Block>)),
}

impl<Block: BlockT> From<(u64, Commit<Block>)> for JustificationOrCommit<Block> {
	fn from(commit: (u64, Commit<Block>)) -> JustificationOrCommit<Block> {
		JustificationOrCommit::Commit(commit)
	}
}

impl<Block: BlockT> From<GrandpaJustification<Block>> for JustificationOrCommit<Block> {
	fn from(justification: GrandpaJustification<Block>) -> JustificationOrCommit<Block> {
		JustificationOrCommit::Justification(justification)
	}
}

/// Finalize the given block and apply any authority set changes. If an
/// authority set change is enacted then a justification is created (if not
/// given) and stored with the block when finalizing it.
fn finalize_block<B, Block: BlockT<Hash=H256>, E, RA>(
	client: &Client<B, E, Block, RA>,
	authority_set: &SharedAuthoritySet<Block::Hash, NumberFor<Block>>,
	consensus_changes: &SharedConsensusChanges<Block::Hash, NumberFor<Block>>,
	justification_period: Option<NumberFor<Block>>,
	hash: Block::Hash,
	number: NumberFor<Block>,
	justification_or_commit: JustificationOrCommit<Block>,
) -> Result<(), ExitOrError<Block::Hash, NumberFor<Block>>> where
	B: Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync,
	RA: Send + Sync,
{
	// lock must be held through writing to DB to avoid race
	let mut authority_set = authority_set.inner().write();

	// TODO [andre]: clone only when changed (#1483)
	let old_authority_set = authority_set.clone();
	// needed in case there is an authority set change, used for reverting in
	// case of error
	let mut old_last_completed = None;

	let mut consensus_changes = consensus_changes.lock();
	let status = authority_set.apply_changes(number, |canon_number| {
		canonical_at_height(client, (hash, number), canon_number)
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

			old_last_completed = Backend::get_aux(&**client.backend(), LAST_COMPLETED_KEY)?;

			Backend::insert_aux(
				&**client.backend(),
				&[
					(AUTHORITY_SET_KEY, &encoded_set[..]),
					(LAST_COMPLETED_KEY, &encoded[..]),
				],
				&[]
			)
		} else {
			Backend::insert_aux(&**client.backend(), &[(AUTHORITY_SET_KEY, &encoded_set[..])], &[])
		};

		if let Err(e) = write_result {
			warn!(target: "finality", "Failed to write updated authority set to disk. Bailing.");
			warn!(target: "finality", "Node is in a potentially inconsistent state.");

			return Err(e.into());
		}
	}

	// check if this is this is the first finalization of some consensus changes
	let (alters_consensus_changes, finalizes_consensus_changes) = consensus_changes
		.finalize((number, hash), |at_height| canonical_at_height(client, (hash, number), at_height))?;

	// holds the old consensus changes in case it is changed below, needed for
	// reverting in case of failure
	let mut old_consensus_changes = None;
	if alters_consensus_changes {
		old_consensus_changes = Some(consensus_changes.clone());

		let encoded = consensus_changes.encode();
		let write_result = Backend::insert_aux(&**client.backend(), &[(CONSENSUS_CHANGES_KEY, &encoded[..])], &[]);
		if let Err(e) = write_result {
			warn!(target: "finality", "Failed to write updated consensus changes to disk. Bailing.");
			warn!(target: "finality", "Node is in a potentially inconsistent state.");

			return Err(e.into());
		}
	}

	let aux = |authority_set: &authorities::AuthoritySet<Block::Hash, NumberFor<Block>>| {
		// NOTE: this code assumes that honest voters will never vote past a
		// transition block, thus we don't have to worry about the case where
		// we have a transition with `effective_block = N`, but we finalize
		// `N+1`. this assumption is required to make sure we store
		// justifications for transition blocks which will be requested by
		// syncing clients.
		let justification = match justification_or_commit {
			JustificationOrCommit::Justification(justification) => Some(justification.encode()),
			JustificationOrCommit::Commit((round_number, commit)) => {
				let mut justification_required =
					// justification is always required when block that enacts new authorities
					// set is finalized
					status.new_set_block.is_some() ||
					// justification is required when consensus changes are finalized
					finalizes_consensus_changes;

				// justification is required every N blocks to be able to prove blocks
				// finalization to remote nodes
				if !justification_required {
					if let Some(justification_period) = justification_period {
						let last_finalized_number = client.info()?.chain.finalized_number;
						justification_required =
							(!last_finalized_number.is_zero() || number - last_finalized_number == justification_period) &&
							(last_finalized_number / justification_period != number / justification_period);
					}
				}

				if justification_required {
					let justification = GrandpaJustification::from_commit(
						client,
						round_number,
						commit,
					)?;

					Some(justification.encode())
				} else {
					None
				}
			},
		};

		debug!(target: "afg", "Finalizing blocks up to ({:?}, {})", number, hash);

		// ideally some handle to a synchronization oracle would be used
		// to avoid unconditionally notifying.
		client.finalize_block(BlockId::Hash(hash), justification, true).map_err(|e| {
			warn!(target: "finality", "Error applying finality to block {:?}: {:?}", (hash, number), e);
			e
		})?;

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
	};

	match aux(&authority_set) {
		Err(ExitOrError::Error(err)) => {
			debug!(target: "afg", "Reverting authority set and/or consensus changes after block finalization error: {:?}", err);

			let mut revert_aux = Vec::new();

			if status.changed {
				revert_aux.push((AUTHORITY_SET_KEY, old_authority_set.encode()));
				if let Some(old_last_completed) = old_last_completed {
					revert_aux.push((LAST_COMPLETED_KEY, old_last_completed));
				}

				*authority_set = old_authority_set.clone();
			}

			if let Some(old_consensus_changes) = old_consensus_changes {
				revert_aux.push((CONSENSUS_CHANGES_KEY, old_consensus_changes.encode()));

				*consensus_changes = old_consensus_changes;
			}

			let write_result = Backend::insert_aux(
				&**client.backend(),
				revert_aux.iter().map(|(k, v)| (*k, &**v)).collect::<Vec<_>>().iter(),
				&[],
			);

			if let Err(e) = write_result {
				warn!(target: "finality", "Failed to revert consensus changes to disk. Bailing.");
				warn!(target: "finality", "Node is in a potentially inconsistent state.");

				return Err(e.into());
			}

			Err(ExitOrError::Error(err))
		},
		res => res,
	}
}

/// A block-import handler for GRANDPA.
///
/// This scans each imported block for signals of changing authority set.
/// If the block being imported enacts an authority set change then:
/// - If the current authority set is still live: we import the block
/// - Otherwise, the block must include a valid justification.
///
/// When using GRANDPA, the block import worker should be using this block import
/// object.
pub struct GrandpaBlockImport<B, E, Block: BlockT<Hash=H256>, RA, PRA> {
	inner: Arc<Client<B, E, Block, RA>>,
	authority_set: SharedAuthoritySet<Block::Hash, NumberFor<Block>>,
	authority_set_change: mpsc::UnboundedSender<NewAuthoritySet<Block::Hash, NumberFor<Block>>>,
	consensus_changes: SharedConsensusChanges<Block::Hash, NumberFor<Block>>,
	api: Arc<PRA>,
}

impl<B, E, Block: BlockT<Hash=H256>, RA, PRA> JustificationImport<Block>
	for GrandpaBlockImport<B, E, Block, RA, PRA> where
		NumberFor<Block>: grandpa::BlockNumberOps,
		B: Backend<Block, Blake2Hasher> + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		DigestFor<Block>: Encode,
		DigestItemFor<Block>: DigestItem<AuthorityId=Ed25519AuthorityId>,
		RA: Send + Sync,
		PRA: ProvideRuntimeApi,
		PRA::Api: GrandpaApi<Block>,
{
	type Error = ConsensusError;

	fn on_start(&self, link: &::consensus_common::import_queue::Link<Block>) {
		let chain_info = match self.inner.info() {
			Ok(info) => info.chain,
			_ => return,
		};

		// request justifications for all pending changes for which change blocks have already been imported
		for pending_change in self.authority_set.inner().read().pending_changes() {
			if pending_change.effective_number() > chain_info.finalized_number &&
				pending_change.effective_number() <= chain_info.best_number
			{
				let effective_block_hash = self.inner.best_containing(
					pending_change.canon_hash,
					Some(pending_change.effective_number()),
				);

				if let Ok(Some(hash)) = effective_block_hash {
					if let Ok(Some(header)) = self.inner.header(&BlockId::Hash(hash)) {
						if *header.number() == pending_change.effective_number() {
							link.request_justification(&header.hash(), *header.number());
						}
					}
				}
			}
		}
	}

	fn import_justification(
		&self,
		hash: Block::Hash,
		number: NumberFor<Block>,
		justification: Justification,
	) -> Result<(), Self::Error> {
		self.import_justification(hash, number, justification, false)
	}
}

impl<B, E, Block: BlockT<Hash=H256>, RA, PRA> BlockImport<Block>
	for GrandpaBlockImport<B, E, Block, RA, PRA> where
		NumberFor<Block>: grandpa::BlockNumberOps,
		B: Backend<Block, Blake2Hasher> + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		DigestFor<Block>: Encode,
		DigestItemFor<Block>: DigestItem<AuthorityId=Ed25519AuthorityId>,
		RA: Send + Sync,
		PRA: ProvideRuntimeApi,
		PRA::Api: GrandpaApi<Block>,
{
	type Error = ConsensusError;

	fn import_block(&self, mut block: ImportBlock<Block>, new_authorities: Option<Vec<Ed25519AuthorityId>>)
		-> Result<ImportResult, Self::Error>
	{
		use authorities::PendingChange;

		let hash = block.post_header().hash();
		let number = block.header.number().clone();

		let maybe_change = self.api.runtime_api().grandpa_pending_change(
			&BlockId::hash(*block.header.parent_hash()),
			&block.header.digest().clone(),
		);

		let maybe_change = match maybe_change {
			Err(e) => return Err(ConsensusErrorKind::ClientImport(e.to_string()).into()),
			Ok(maybe) => maybe,
		};

		// when we update the authorities, we need to hold the lock
		// until the block is written to prevent a race if we need to restore
		// the old authority set on error.
		let just_in_case = if let Some(change) = maybe_change {
			let parent_hash = *block.header.parent_hash();

			let mut authorities = self.authority_set.inner().write();
			let old_set = authorities.clone();

			let is_equal_or_descendent_of = |base: &Block::Hash| -> Result<(), ConsensusError> {
				let error = || {
					Err(ConsensusErrorKind::ClientImport("Incorrect base hash".to_string()).into())
				};

				if *base == hash { return error(); }
				if *base == parent_hash { return error(); }

				let tree_route = ::client::blockchain::tree_route(
					self.inner.backend().blockchain(),
					BlockId::Hash(parent_hash),
					BlockId::Hash(*base),
				);

				let tree_route = match tree_route {
					Err(e) => return Err(ConsensusErrorKind::ClientImport(e.to_string()).into()),
					Ok(route) => route,
				};

				if tree_route.common_block().hash == *base {
					return error();
				}

				Ok(())
			};

			authorities.add_pending_change(
				PendingChange {
					next_authorities: change.next_authorities,
					finalization_depth: change.delay,
					canon_height: number,
					canon_hash: hash,
				},
				is_equal_or_descendent_of,
			)?;

			block.auxiliary.push((AUTHORITY_SET_KEY.to_vec(), Some(authorities.encode())));
			Some((old_set, authorities))
		} else {
			None
		};

		// we don't want to finalize on `inner.import_block`
		let justification = block.justification.take();
		let enacts_consensus_change = new_authorities.is_some();
		let import_result = self.inner.import_block(block, new_authorities);

		let import_result = {
			// we scope this so that `just_in_case` is dropped eagerly and releases the authorities lock
			let revert_authorities = || if let Some((old_set, mut authorities)) = just_in_case {
				*authorities = old_set;
			};

			match import_result {
				Ok(ImportResult::Queued) => ImportResult::Queued,
				Ok(r) => {
					debug!(target: "afg", "Restoring old authority set after block import result: {:?}", r);
					revert_authorities();
					return Ok(r);
				},
				Err(e) => {
					debug!(target: "afg", "Restoring old authority set after block import error: {:?}", e);
					revert_authorities();
					return Err(ConsensusErrorKind::ClientImport(e.to_string()).into());
				},
			}
		};

		let enacts_change = self.authority_set.inner().read().enacts_change(number, |canon_number| {
			canonical_at_height(&self.inner, (hash, number), canon_number)
		}).map_err(|e| ConsensusError::from(ConsensusErrorKind::ClientImport(e.to_string())))?;

		if !enacts_change && !enacts_consensus_change {
			return Ok(import_result);
		}

		match justification {
			Some(justification) => {
				self.import_justification(hash, number, justification, enacts_change)?;
			},
			None => {
				if enacts_change {
					trace!(
						target: "finality",
						"Imported unjustified block #{} that enacts authority set change, waiting for finality for enactment.",
						number,
					);
				}

				// we have imported block with consensus data changes, but without justification
				// => remember to create justification when next block will be finalized
				if enacts_consensus_change {
					self.consensus_changes.lock().note_change((number, hash));
				}

				return Ok(ImportResult::NeedsJustification);
			}
		}

		Ok(import_result)
	}
}

impl<B, E, Block: BlockT<Hash=H256>, RA, PRA>
	GrandpaBlockImport<B, E, Block, RA, PRA> where
		NumberFor<Block>: grandpa::BlockNumberOps,
		B: Backend<Block, Blake2Hasher> + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		RA: Send + Sync,
{

	/// Import a block justification and finalize the block.
	///
	/// If `enacts_change` is set to true, then finalizing this block *must*
	/// enact an authority set change, the function will panic otherwise.
	fn import_justification(
		&self,
		hash: Block::Hash,
		number: NumberFor<Block>,
		justification: Justification,
		enacts_change: bool,
	) -> Result<(), ConsensusError> {
		let justification = GrandpaJustification::decode_and_verify(
			justification,
			self.authority_set.set_id(),
			&self.authority_set.current_authorities(),
		);

		let justification = match justification {
			Err(e) => return Err(ConsensusErrorKind::ClientImport(e.to_string()).into()),
			Ok(justification) => justification,
		};

		let result = finalize_block(
			&*self.inner,
			&self.authority_set,
			&self.consensus_changes,
			None,
			hash,
			number,
			justification.into(),
		);

		match result {
			Err(ExitOrError::AuthoritiesChanged(new)) => {
				info!(target: "finality", "Imported justification for block #{} that enacts authority set change, signalling voter.", number);
				if let Err(e) = self.authority_set_change.unbounded_send(new) {
					return Err(ConsensusErrorKind::ClientImport(e.to_string()).into());
				}
			},
			Err(ExitOrError::Error(e)) => {
				return Err(match e {
					Error::Grandpa(error) => ConsensusErrorKind::ClientImport(error.to_string()),
					Error::Network(error) => ConsensusErrorKind::ClientImport(error),
					Error::Blockchain(error) => ConsensusErrorKind::ClientImport(error),
					Error::Client(error) => ConsensusErrorKind::ClientImport(error.to_string()),
					Error::Timer(error) => ConsensusErrorKind::ClientImport(error.to_string()),
				}.into());
			},
			Ok(_) => {
				assert!(!enacts_change, "returns Ok when no authority set change should be enacted; qed;");
			},
		}

		Ok(())
	}
}

/// Using the given base get the block at the given height on this chain. The
/// target block must be an ancestor of base, therefore `height <= base.height`.
fn canonical_at_height<B, E, Block: BlockT<Hash=H256>, RA>(
	client: &Client<B, E, Block, RA>,
	base: (Block::Hash, NumberFor<Block>),
	height: NumberFor<Block>,
) -> Result<Option<Block::Hash>, ClientError> where
	B: Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync,
{
	use runtime_primitives::traits::{One, Zero};

	if height > base.1 {
		return Ok(None);
	}

	if height == base.1 {
		return Ok(Some(base.0));
	}

	let mut current = match client.header(&BlockId::Hash(base.0))? {
		Some(header) => header,
		_ => return Ok(None),
	};

	let mut steps = base.1 - height;

	while steps > NumberFor::<Block>::zero() {
		current = match client.header(&BlockId::Hash(*current.parent_hash()))? {
			Some(header) => header,
			_ => return Ok(None),
		};

		steps -= NumberFor::<Block>::one();
	}

	Ok(Some(current.hash()))
}

/// Half of a link between a block-import worker and a the background voter.
// This should remain non-clone.
pub struct LinkHalf<B, E, Block: BlockT<Hash=H256>, RA> {
	client: Arc<Client<B, E, Block, RA>>,
	authority_set: SharedAuthoritySet<Block::Hash, NumberFor<Block>>,
	authority_set_change: mpsc::UnboundedReceiver<NewAuthoritySet<Block::Hash, NumberFor<Block>>>,
	consensus_changes: SharedConsensusChanges<Block::Hash, NumberFor<Block>>,
}

struct AncestryChain<Block: BlockT> {
	ancestry: HashMap<Block::Hash, Block::Header>,
}

impl<Block: BlockT> AncestryChain<Block> {
	fn new(ancestry: &[Block::Header]) -> AncestryChain<Block> {
		let ancestry: HashMap<_, _> = ancestry
			.iter()
			.cloned()
			.map(|h: Block::Header| (h.hash(), h))
			.collect();

		AncestryChain { ancestry }
	}
}

impl<Block: BlockT> grandpa::Chain<Block::Hash, NumberFor<Block>> for AncestryChain<Block> where
	NumberFor<Block>: grandpa::BlockNumberOps
{
	fn ancestry(&self, base: Block::Hash, block: Block::Hash) -> Result<Vec<Block::Hash>, GrandpaError> {
		let mut route = Vec::new();
		let mut current_hash = block;
		loop {
			if current_hash == base { break; }
			match self.ancestry.get(&current_hash) {
				Some(current_header) => {
					current_hash = *current_header.parent_hash();
					route.push(current_hash);
				},
				_ => return Err(GrandpaError::NotDescendent),
			}
		}
		route.pop(); // remove the base

		Ok(route)
	}

	fn best_chain_containing(&self, _block: Block::Hash) -> Option<(Block::Hash, NumberFor<Block>)> {
		None
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
	let authority_set = match Backend::get_aux(&**client.backend(), AUTHORITY_SET_KEY)? {
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
			Backend::insert_aux(&**client.backend(), &[(AUTHORITY_SET_KEY, &encoded[..])], &[])?;

			authority_set
		}
		Some(raw) => ::authorities::AuthoritySet::decode(&mut &raw[..])
			.ok_or_else(|| ::client::error::ErrorKind::Backend(
				format!("GRANDPA authority set kept in invalid format")
			))?
			.into(),
	};

	let consensus_changes = Backend::get_aux(&**client.backend(), CONSENSUS_CHANGES_KEY)?;
	let consensus_changes = Arc::new(parking_lot::Mutex::new(match consensus_changes {
		Some(raw) => ConsensusChanges::decode(&mut &raw[..])
			.ok_or_else(|| ::client::error::ErrorKind::Backend(
				format!("GRANDPA consensus changes kept in invalid format")
			))?,
		None => ConsensusChanges::empty(),
	}));

	let (authority_set_change_tx, authority_set_change_rx) = mpsc::unbounded();

	Ok((
		GrandpaBlockImport {
			inner: client.clone(),
			authority_set: authority_set.clone(),
			authority_set_change: authority_set_change_tx,
			consensus_changes: consensus_changes.clone(),
			api
		},
		LinkHalf {
			client,
			authority_set,
			authority_set_change: authority_set_change_rx,
			consensus_changes,
		},
	))
}

fn committer_communication<Block: BlockT<Hash=H256>, B, E, N, RA>(
	local_key: Option<Arc<ed25519::Pair>>,
	set_id: u64,
	voters: &Arc<HashMap<Ed25519AuthorityId, u64>>,
	client: &Arc<Client<B, E, Block, RA>>,
	network: &N,
) -> (
	impl Stream<
		Item = (u64, ::grandpa::CompactCommit<H256, NumberFor<Block>, ed25519::Signature, Ed25519AuthorityId>),
		Error = ExitOrError<H256, NumberFor<Block>>,
	>,
	impl Sink<
		SinkItem = (u64, ::grandpa::Commit<H256, NumberFor<Block>, ed25519::Signature, Ed25519AuthorityId>),
		SinkError = ExitOrError<H256, NumberFor<Block>>,
	>,
) where
	B: Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync,
	N: Network,
	RA: Send + Sync,
	NumberFor<Block>: BlockNumberOps,
	DigestItemFor<Block>: DigestItem<AuthorityId=Ed25519AuthorityId>,
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

	let is_voter = local_key
		.map(|pair| voters.contains_key(&pair.public().into()))
		.unwrap_or(false);

	let commit_out = ::communication::CommitsOut::<Block, _>::new(
		network.clone(),
		set_id,
		is_voter,
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
	on_exit: impl Future<Item=(),Error=()> + Send + 'static,
) -> ::client::error::Result<impl Future<Item=(),Error=()> + Send + 'static> where
	Block::Hash: Ord,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
	N: Network + Send + Sync + 'static,
	N::In: Send + 'static,
	NumberFor<Block>: BlockNumberOps,
	DigestFor<Block>: Encode,
	DigestItemFor<Block>: DigestItem<AuthorityId=Ed25519AuthorityId>,
	RA: Send + Sync + 'static,
{
	use futures::future::{self, Loop as FutureLoop};
	use runtime_primitives::traits::Zero;

	let LinkHalf {
		client,
		authority_set,
		authority_set_change,
		consensus_changes,
	} = link;

	let chain_info = client.info()?;
	let genesis_hash = chain_info.chain.genesis_hash;

	// we shadow network with the wrapping/rebroadcasting network to avoid
	// accidental reuse.
	let (broadcast_worker, network) = communication::rebroadcasting_network(network);

	let (last_round_number, last_state) = match Backend::get_aux(&**client.backend(), LAST_COMPLETED_KEY)? {
		None => (0, RoundState::genesis((genesis_hash, <NumberFor<Block>>::zero()))),
		Some(raw) => LastCompleted::decode(&mut &raw[..])
			.ok_or_else(|| ::client::error::ErrorKind::Backend(
				format!("Last GRANDPA round state kept in invalid format")
			))?
	};

	let voters = authority_set.current_authorities();

	let initial_environment = Arc::new(Environment {
		inner: client.clone(),
		config: config.clone(),
		voters: Arc::new(voters),
		network: network.clone(),
		set_id: authority_set.set_id(),
		authority_set: authority_set.clone(),
		consensus_changes: consensus_changes.clone(),
	});

	let initial_state = (initial_environment, last_round_number, last_state, authority_set_change.into_future());
	let voter_work = future::loop_fn(initial_state, move |params| {
		let (env, last_round_number, last_state, authority_set_change) = params;
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
			config.local_key.clone(),
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
		let consensus_changes = consensus_changes.clone();

		let trigger_authority_set_change = |new: NewAuthoritySet<_, _>, authority_set_change| {
			let env = Arc::new(Environment {
				inner: client,
				config,
				voters: Arc::new(new.authorities.into_iter().collect()),
				set_id: new.set_id,
				network,
				authority_set,
				consensus_changes,
			});

			// start the new authority set using the block where the
			// set changed (not where the signal happened!) as the base.
			Ok(FutureLoop::Continue((
				env,
				0, // always start at round 0 when changing sets.
				RoundState::genesis((new.canon_hash, new.canon_number)),
				authority_set_change,
			)))
		};

		future::Either::A(voter.select2(authority_set_change).then(move |res| match res {
			Ok(future::Either::A(((), _))) => {
				// voters don't conclude naturally; this could reasonably be an error.
				Ok(FutureLoop::Break(()))
			},
			Err(future::Either::B(_)) => {
				// the `authority_set_change` stream should not fail.
				Ok(FutureLoop::Break(()))
			},
			Ok(future::Either::B(((None, _), _))) => {
				// the `authority_set_change` stream should never conclude since it's never closed.
				Ok(FutureLoop::Break(()))
			},
			Err(future::Either::A((ExitOrError::Error(e), _))) => {
				// return inner voter error
				Err(e)
			}
			Ok(future::Either::B(((Some(new), authority_set_change), _))) => {
				// authority set change triggered externally through the channel
				trigger_authority_set_change(new, authority_set_change.into_future())
			}
			Err(future::Either::A((ExitOrError::AuthoritiesChanged(new), authority_set_change))) => {
				// authority set change triggered internally by finalizing a change block
				trigger_authority_set_change(new, authority_set_change)
			},
		}))
	});

	let voter_work = voter_work
		.join(broadcast_worker)
		.map(|((), ())| ())
		.map_err(|e| warn!("GRANDPA Voter failed: {:?}", e));

	Ok(voter_work.select(on_exit).then(|_| Ok(())))
}
