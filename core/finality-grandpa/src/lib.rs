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
use futures::sync::{self, mpsc, oneshot};
use client::{
	BlockchainEvents, CallExecutor, Client, backend::Backend,
	error::Error as ClientError,
};
use client::blockchain::HeaderBackend;
use codec::{Encode, Decode};
use runtime_primitives::traits::{
	NumberFor, Block as BlockT, Header as HeaderT, DigestFor, ProvideRuntimeApi, Hash as HashT,
	DigestItemFor, DigestItem,
};
use fg_primitives::GrandpaApi;
use runtime_primitives::generic::BlockId;
use substrate_primitives::{ed25519, H256, Ed25519AuthorityId, Blake2Hasher};

use grandpa::Error as GrandpaError;
use grandpa::{voter, round::State as RoundState, BlockNumberOps, VoterSet};

use network::Service as NetworkService;
use std::sync::Arc;
use std::time::Duration;

pub use fg_primitives::ScheduledChange;

mod authorities;
mod communication;
mod consensus_changes;
mod environment;
mod finality_proof;
mod import;
mod justification;
mod until_imported;

#[cfg(feature="service-integration")]
mod service_integration;
#[cfg(feature="service-integration")]
pub use service_integration::{LinkHalfForService, BlockImportForService};

use authorities::SharedAuthoritySet;
use consensus_changes::{ConsensusChanges, SharedConsensusChanges};
use environment::{Environment, ExitOrError, NewAuthoritySet};
pub use finality_proof::{prove_finality, check_finality_proof};
use import::GrandpaBlockImport;
use until_imported::UntilCommitBlocksImported;

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

/// A stream used by NetworkBridge in its implementation of Network.
pub struct NetworkStream {
	inner: Option<mpsc::UnboundedReceiver<Vec<u8>>>,
	outer: oneshot::Receiver<mpsc::UnboundedReceiver<Vec<u8>>>
}

impl Stream for NetworkStream {
	type Item = Vec<u8>;
	type Error = ();

	fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
		if let Some(ref mut inner) = self.inner {
			return inner.poll();
		}
		match self.outer.poll() {
			Ok(futures::Async::Ready(mut inner)) => {
				let poll_result = inner.poll();
				self.inner = Some(inner);
				poll_result
			},
			Ok(futures::Async::NotReady) => Ok(futures::Async::NotReady),
			Err(_) => Err(())
		}
	}
}

/// A handle to the network. This is generally implemented by providing some
/// handle to a gossip service or similar.
///
/// Intended to be a lightweight handle such as an `Arc`.
pub trait Network<Block: BlockT>: Clone {
	/// A stream of input messages for a topic.
	type In: Stream<Item=Vec<u8>,Error=()>;

	/// Get a stream of messages for a specific round. This stream should
	/// never logically conclude.
	fn messages_for(&self, round: u64, set_id: u64) -> Self::In;

	/// Send a message at a specific round out.
	fn send_message(&self, round: u64, set_id: u64, message: Vec<u8>);

	/// Clean up messages for a round.
	fn drop_round_messages(&self, round: u64, set_id: u64);

	/// Clean up messages for a given authority set id (e.g. commit messages).
	fn drop_set_messages(&self, set_id: u64);

	/// Get a stream of commit messages for a specific set-id. This stream
	/// should never logically conclude.
	fn commit_messages(&self, set_id: u64) -> Self::In;

	/// Send message over the commit channel.
	fn send_commit(&self, round: u64, set_id: u64, message: Vec<u8>);

	/// Inform peers that a block with given hash should be downloaded.
	fn announce(&self, round: u64, set_id: u64, block: Block::Hash);
}

///  Bridge between NetworkService, gossiping consensus messages and Grandpa
pub struct NetworkBridge<B: BlockT, S: network::specialization::NetworkSpecialization<B>> {
	service: Arc<NetworkService<B, S>>
}

impl<B: BlockT, S: network::specialization::NetworkSpecialization<B>> NetworkBridge<B, S> {
	/// Create a new NetworkBridge to the given NetworkService
	pub fn new(service: Arc<NetworkService<B, S>>) -> Self {
		NetworkBridge { service }
	}
}

impl<B: BlockT, S: network::specialization::NetworkSpecialization<B>,> Clone for NetworkBridge<B, S> {
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

impl<B: BlockT, S: network::specialization::NetworkSpecialization<B>,> Network<B> for NetworkBridge<B, S> {
	type In = NetworkStream;
	fn messages_for(&self, round: u64, set_id: u64) -> Self::In {
		let (tx, rx) = sync::oneshot::channel();
		self.service.with_gossip(move |gossip, _| {
			let inner_rx = gossip.messages_for(message_topic::<B>(round, set_id));
			let _ = tx.send(inner_rx);
		});
		NetworkStream { outer: rx, inner: None }
	}

	fn send_message(&self, round: u64, set_id: u64, message: Vec<u8>) {
		let topic = message_topic::<B>(round, set_id);
		self.service.gossip_consensus_message(topic, message, false);
	}

	fn drop_round_messages(&self, round: u64, set_id: u64) {
		let topic = message_topic::<B>(round, set_id);
		self.service.with_gossip(move |gossip, _| gossip.collect_garbage_for_topic(topic));
	}

	fn drop_set_messages(&self, set_id: u64) {
		let topic = commit_topic::<B>(set_id);
		self.service.with_gossip(move |gossip, _| gossip.collect_garbage_for_topic(topic));
	}

	fn commit_messages(&self, set_id: u64) -> Self::In {
		let (tx, rx) = sync::oneshot::channel();
		self.service.with_gossip(move |gossip, _| {
			let inner_rx = gossip.messages_for(commit_topic::<B>(set_id));
			let _ = tx.send(inner_rx);
		});
		NetworkStream { outer: rx, inner: None }
	}

	fn send_commit(&self, _round: u64, set_id: u64, message: Vec<u8>) {
		let topic = commit_topic::<B>(set_id);
		self.service.gossip_consensus_message(topic, message, false);
	}

	fn announce(&self, round: u64, _set_id: u64, block: B::Hash) {
		debug!(target: "afg", "Announcing block {} to peers which we voted on in round {}", block, round);
		self.service.announce_block(block)
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

/// Half of a link between a block-import worker and a the background voter.
// This should remain non-clone.
pub struct LinkHalf<B, E, Block: BlockT<Hash=H256>, RA> {
	client: Arc<Client<B, E, Block, RA>>,
	authority_set: SharedAuthoritySet<Block::Hash, NumberFor<Block>>,
	authority_set_change: mpsc::UnboundedReceiver<NewAuthoritySet<Block::Hash, NumberFor<Block>>>,
	consensus_changes: SharedConsensusChanges<Block::Hash, NumberFor<Block>>,
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
		GrandpaBlockImport::new(
			client.clone(),
			authority_set.clone(),
			authority_set_change_tx,
			consensus_changes.clone(),
			api,
		),
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
	voters: &Arc<VoterSet<Ed25519AuthorityId>>,
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
	N: Network<Block>,
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
	N: Network<Block> + Send + Sync + 'static,
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
