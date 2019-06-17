// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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
//! Instead, we keep track of a list of all signals we've seen so far (across
//! all forks), sorted ascending by the block number they would be applied at.
//! We never vote on chains with number higher than the earliest handoff block
//! number (this is num(signal) + N). When finalizing a block, we either apply
//! or prune any signaled changes based on whether the signaling block is
//! included in the newly-finalized chain.

use futures::prelude::*;
use log::{debug, info, warn};
use futures::sync::mpsc;
use client::{BlockchainEvents, CallExecutor, Client, backend::Backend, error::Error as ClientError};
use client::blockchain::HeaderBackend;
use parity_codec::Encode;
use runtime_primitives::traits::{
	NumberFor, Block as BlockT, DigestFor, ProvideRuntimeApi,
};
use fg_primitives::GrandpaApi;
use inherents::InherentDataProviders;
use runtime_primitives::generic::BlockId;
use consensus_common::SelectChain;
use substrate_primitives::{ed25519, H256, Pair, Blake2Hasher};
use substrate_telemetry::{telemetry, CONSENSUS_INFO, CONSENSUS_DEBUG, CONSENSUS_WARN};
use serde_json;

use srml_finality_tracker;

use grandpa::Error as GrandpaError;
use grandpa::{voter, round::State as RoundState, BlockNumberOps, voter_set::VoterSet};

use std::fmt;
use std::sync::Arc;
use std::time::Duration;

mod authorities;
mod aux_schema;
mod communication;
mod consensus_changes;
mod environment;
mod finality_proof;
mod import;
mod justification;
mod light_import;
mod observer;
mod until_imported;

#[cfg(feature="service-integration")]
mod service_integration;
#[cfg(feature="service-integration")]
pub use service_integration::{LinkHalfForService, BlockImportForService, BlockImportForLightService};
pub use communication::Network;
pub use finality_proof::FinalityProofProvider;
pub use light_import::light_block_import;
pub use observer::run_grandpa_observer;

use aux_schema::PersistentData;
use environment::{CompletedRound, CompletedRounds, Environment, HasVoted, SharedVoterSetState, VoterSetState};
use import::GrandpaBlockImport;
use until_imported::UntilCommitBlocksImported;
use communication::NetworkBridge;
use service::TelemetryOnConnect;
use fg_primitives::AuthoritySignature;

// Re-export these two because it's just so damn convenient.
pub use fg_primitives::{AuthorityId, ScheduledChange};

#[cfg(test)]
mod tests;

/// A GRANDPA message for a substrate chain.
pub type Message<Block> = grandpa::Message<<Block as BlockT>::Hash, NumberFor<Block>>;
/// A signed message.
pub type SignedMessage<Block> = grandpa::SignedMessage<
	<Block as BlockT>::Hash,
	NumberFor<Block>,
	AuthoritySignature,
	AuthorityId,
>;

/// A primary propose message for this chain's block type.
pub type PrimaryPropose<Block> = grandpa::PrimaryPropose<<Block as BlockT>::Hash, NumberFor<Block>>;
/// A prevote message for this chain's block type.
pub type Prevote<Block> = grandpa::Prevote<<Block as BlockT>::Hash, NumberFor<Block>>;
/// A precommit message for this chain's block type.
pub type Precommit<Block> = grandpa::Precommit<<Block as BlockT>::Hash, NumberFor<Block>>;
/// A commit message for this chain's block type.
pub type Commit<Block> = grandpa::Commit<
	<Block as BlockT>::Hash,
	NumberFor<Block>,
	AuthoritySignature,
	AuthorityId
>;
/// A compact commit message for this chain's block type.
pub type CompactCommit<Block> = grandpa::CompactCommit<
	<Block as BlockT>::Hash,
	NumberFor<Block>,
	AuthoritySignature,
	AuthorityId
>;

/// Configuration for the GRANDPA service.
#[derive(Clone)]
pub struct Config {
	/// The expected duration for a message to be gossiped across the network.
	pub gossip_duration: Duration,
	/// Justification generation period (in blocks). GRANDPA will try to generate justifications
	/// at least every justification_period blocks. There are some other events which might cause
	/// justification generation.
	pub justification_period: u32,
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
	/// An invariant has been violated (e.g. not finalizing pending change blocks in-order)
	Safety(String),
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

/// A new authority set along with the canonical block it changed at.
#[derive(Debug)]
pub(crate) struct NewAuthoritySet<H, N> {
	pub(crate) canon_number: N,
	pub(crate) canon_hash: H,
	pub(crate) set_id: u64,
	pub(crate) authorities: Vec<(AuthorityId, u64)>,
}

/// Commands issued to the voter.
#[derive(Debug)]
pub(crate) enum VoterCommand<H, N> {
	/// Pause the voter for given reason.
	Pause(String),
	/// New authorities.
	ChangeAuthorities(NewAuthoritySet<H, N>)
}

impl<H, N> fmt::Display for VoterCommand<H, N> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			VoterCommand::Pause(ref reason) => write!(f, "Pausing voter: {}", reason),
			VoterCommand::ChangeAuthorities(_) => write!(f, "Changing authorities"),
		}
	}
}

/// Signals either an early exit of a voter or an error.
#[derive(Debug)]
pub(crate) enum CommandOrError<H, N> {
	/// An error occurred.
	Error(Error),
	/// A command to the voter.
	VoterCommand(VoterCommand<H, N>),
}

impl<H, N> From<Error> for CommandOrError<H, N> {
	fn from(e: Error) -> Self {
		CommandOrError::Error(e)
	}
}

impl<H, N> From<ClientError> for CommandOrError<H, N> {
	fn from(e: ClientError) -> Self {
		CommandOrError::Error(Error::Client(e))
	}
}

impl<H, N> From<grandpa::Error> for CommandOrError<H, N> {
	fn from(e: grandpa::Error) -> Self {
		CommandOrError::Error(Error::from(e))
	}
}

impl<H, N> From<VoterCommand<H, N>> for CommandOrError<H, N> {
	fn from(e: VoterCommand<H, N>) -> Self {
		CommandOrError::VoterCommand(e)
	}
}

impl<H: fmt::Debug, N: fmt::Debug> ::std::error::Error for CommandOrError<H, N> { }

impl<H, N> fmt::Display for CommandOrError<H, N> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			CommandOrError::Error(ref e) => write!(f, "{:?}", e),
			CommandOrError::VoterCommand(ref cmd) => write!(f, "{}", cmd),
		}
	}
}

pub struct LinkHalf<B, E, Block: BlockT<Hash=H256>, RA, SC> {
	client: Arc<Client<B, E, Block, RA>>,
	select_chain: SC,
	persistent_data: PersistentData<Block>,
	voter_commands_rx: mpsc::UnboundedReceiver<VoterCommand<Block::Hash, NumberFor<Block>>>,
}

/// Make block importer and link half necessary to tie the background voter
/// to it.
pub fn block_import<B, E, Block: BlockT<Hash=H256>, RA, PRA, SC>(
	client: Arc<Client<B, E, Block, RA>>,
	api: Arc<PRA>,
	select_chain: SC,
) -> Result<(
		GrandpaBlockImport<B, E, Block, RA, PRA, SC>,
		LinkHalf<B, E, Block, RA, SC>
	), ClientError>
where
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
	RA: Send + Sync,
	PRA: ProvideRuntimeApi,
	PRA::Api: GrandpaApi<Block>,
	SC: SelectChain<Block>,
{
	use runtime_primitives::traits::Zero;

	let chain_info = client.info();
	let genesis_hash = chain_info.chain.genesis_hash;

	let persistent_data = aux_schema::load_persistent(
		#[allow(deprecated)]
		&**client.backend(),
		genesis_hash,
		<NumberFor<Block>>::zero(),
		|| {
			let genesis_authorities = api.runtime_api()
				.grandpa_authorities(&BlockId::number(Zero::zero()))?;
			telemetry!(CONSENSUS_DEBUG; "afg.loading_authorities";
				"authorities_len" => ?genesis_authorities.len()
			);
			Ok(genesis_authorities)
		}
	)?;

	let (voter_commands_tx, voter_commands_rx) = mpsc::unbounded();

	Ok((
		GrandpaBlockImport::new(
			client.clone(),
			select_chain.clone(),
			persistent_data.authority_set.clone(),
			voter_commands_tx,
			persistent_data.consensus_changes.clone(),
			api,
		),
		LinkHalf {
			client,
			select_chain,
			persistent_data,
			voter_commands_rx,
		},
	))
}

fn global_communication<Block: BlockT<Hash=H256>, B, E, N, RA>(
	local_key: Option<&Arc<ed25519::Pair>>,
	set_id: u64,
	voters: &Arc<VoterSet<AuthorityId>>,
	client: &Arc<Client<B, E, Block, RA>>,
	network: &NetworkBridge<Block, N>,
) -> (
	impl Stream<
		Item = voter::CommunicationIn<H256, NumberFor<Block>, AuthoritySignature, AuthorityId>,
		Error = CommandOrError<H256, NumberFor<Block>>,
	>,
	impl Sink<
		SinkItem = voter::CommunicationOut<H256, NumberFor<Block>, AuthoritySignature, AuthorityId>,
		SinkError = CommandOrError<H256, NumberFor<Block>>,
	>,
) where
	B: Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync,
	N: Network<Block>,
	RA: Send + Sync,
	NumberFor<Block>: BlockNumberOps,
{

	let is_voter = local_key
		.map(|pair| voters.contains_key(&pair.public().into()))
		.unwrap_or(false);

	// verification stream
	let (commit_in, commit_out) = network.global_communication(
		communication::SetId(set_id),
		voters.clone(),
		is_voter,
	);

	// block commit messages until relevant blocks are imported.
	let commit_in = UntilCommitBlocksImported::new(
		client.import_notification_stream(),
		client.clone(),
		commit_in,
	);

	let commits_in = commit_in.map_err(CommandOrError::from);
	let commits_out = commit_out.sink_map_err(CommandOrError::from);

	let global_in = commits_in.map(|(round, commit, mut callback)| {
		let callback = voter::Callback::Work(Box::new(move |outcome| match outcome {
			voter::CommitProcessingOutcome::Good(_) =>
				callback(communication::CommitProcessingOutcome::Good),
			voter::CommitProcessingOutcome::Bad(_) =>
				callback(communication::CommitProcessingOutcome::Bad),
		}));
		voter::CommunicationIn::Commit(round, commit, callback)
	});

	// NOTE: eventually this will also handle catch-up requests
	let global_out = commits_out.with(|global| match global {
		voter::CommunicationOut::Commit(round, commit) => Ok((round, commit)),
		_ => unimplemented!(),
	});

	(global_in, global_out)
}

/// Register the finality tracker inherent data provider (which is used by
/// GRANDPA), if not registered already.
fn register_finality_tracker_inherent_data_provider<B, E, Block: BlockT<Hash=H256>, RA>(
	client: Arc<Client<B, E, Block, RA>>,
	inherent_data_providers: &InherentDataProviders,
) -> Result<(), consensus_common::Error> where
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
	RA: Send + Sync + 'static,
{
	if !inherent_data_providers.has_provider(&srml_finality_tracker::INHERENT_IDENTIFIER) {
		inherent_data_providers
			.register_provider(srml_finality_tracker::InherentDataProvider::new(move || {
				#[allow(deprecated)]
				{
					let info = client.backend().blockchain().info();
					telemetry!(CONSENSUS_INFO; "afg.finalized";
						"finalized_number" => ?info.finalized_number,
						"finalized_hash" => ?info.finalized_hash,
					);
					Ok(info.finalized_number)
				}
			}))
			.map_err(|err| consensus_common::Error::InherentData(err.into()))
	} else {
		Ok(())
	}
}

/// Parameters used to run Grandpa.
pub struct GrandpaParams<'a, B, E, Block: BlockT<Hash=H256>, N, RA, SC, X> {
	/// Configuration for the GRANDPA service.
	pub config: Config,
	/// A link to the block import worker.
	pub link: LinkHalf<B, E, Block, RA, SC>,
	/// The Network instance.
	pub network: N,
	/// The inherent data providers.
	pub inherent_data_providers: InherentDataProviders,
	/// Handle to a future that will resolve on exit.
	pub on_exit: X,
	/// If supplied, can be used to hook on telemetry connection established events.
	pub telemetry_on_connect: Option<TelemetryOnConnect<'a>>,
}

/// Run a GRANDPA voter as a task. Provide configuration and a link to a
/// block import worker that has already been instantiated with `block_import`.
pub fn run_grandpa_voter<B, E, Block: BlockT<Hash=H256>, N, RA, SC, X>(
	grandpa_params: GrandpaParams<B, E, Block, N, RA, SC, X>,
) -> ::client::error::Result<impl Future<Item=(),Error=()> + Send + 'static> where
	Block::Hash: Ord,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
	N: Network<Block> + Send + Sync + 'static,
	N::In: Send + 'static,
	SC: SelectChain<Block> + 'static,
	NumberFor<Block>: BlockNumberOps,
	DigestFor<Block>: Encode,
	RA: Send + Sync + 'static,
	X: Future<Item=(),Error=()> + Clone + Send + 'static,
{
	let GrandpaParams {
		config,
		link,
		network,
		inherent_data_providers,
		on_exit,
		telemetry_on_connect,
	} = grandpa_params;

	use futures::future::{self, Loop as FutureLoop};

	let LinkHalf {
		client,
		select_chain,
		persistent_data,
		voter_commands_rx,
	} = link;

	let PersistentData { authority_set, set_state, consensus_changes } = persistent_data;

	let (network, network_startup) = NetworkBridge::new(
		network,
		config.clone(),
		Some(&set_state.read()),
		on_exit.clone(),
	);

	register_finality_tracker_inherent_data_provider(client.clone(), &inherent_data_providers)?;

	if let Some(telemetry_on_connect) = telemetry_on_connect {
		let authorities = authority_set.clone();
		let events = telemetry_on_connect.telemetry_connection_sinks
			.for_each(move |_| {
				telemetry!(CONSENSUS_INFO; "afg.authority_set";
					 "authority_set_id" => ?authorities.set_id(),
					 "authorities" => {
						let curr = authorities.current_authorities();
						let voters = curr.voters();
						let authorities: Vec<String> =
							voters.iter().map(|(id, _)| id.to_string()).collect();
						serde_json::to_string(&authorities)
							.expect("authorities is always at least an empty vector; elements are always of type string")
					 }
				);
				Ok(())
			})
			.then(|_| Ok(()));
		let events = events.select(telemetry_on_connect.on_exit).then(|_| Ok(()));
		telemetry_on_connect.executor.spawn(events);
	}

	let voters = authority_set.current_authorities();
	let initial_environment = Arc::new(Environment {
		inner: client.clone(),
		config: config.clone(),
		select_chain: select_chain.clone(),
		voters: Arc::new(voters),
		network: network.clone(),
		set_id: authority_set.set_id(),
		authority_set: authority_set.clone(),
		consensus_changes: consensus_changes.clone(),
		voter_set_state: set_state.clone(),
	});

	initial_environment.update_voter_set_state(|voter_set_state| {
		match voter_set_state {
			VoterSetState::Live { current_round: HasVoted::Yes(id, _), completed_rounds } => {
				let local_id = config.local_key.clone().map(|pair| pair.public());
				let has_voted = match local_id {
					Some(local_id) => if *id == local_id {
						// keep the previous votes
						return Ok(None);
					} else {
						HasVoted::No
					},
					_ => HasVoted::No,
				};

				// NOTE: only updated on disk when the voter first
				// proposes/prevotes/precommits or completes a round.
				Ok(Some(VoterSetState::Live {
					current_round: has_voted,
					completed_rounds: completed_rounds.clone(),
				}))
			},
			_ => Ok(None),
		}
	}).expect("operation inside closure cannot fail; qed");

	let initial_state = (initial_environment, voter_commands_rx.into_future());
	let voter_work = future::loop_fn(initial_state, move |params| {
		let (env, voter_commands_rx) = params;
		debug!(target: "afg", "{}: Starting new voter with set ID {}", config.name(), env.set_id);
		telemetry!(CONSENSUS_DEBUG; "afg.starting_new_voter";
			"name" => ?config.name(), "set_id" => ?env.set_id
		);

		let mut maybe_voter = match &*env.voter_set_state.read() {
			VoterSetState::Live { completed_rounds, .. } => {
				let chain_info = client.info();

				let last_finalized = (
					chain_info.chain.finalized_hash,
					chain_info.chain.finalized_number,
				);

				let global_comms = global_communication(
					config.local_key.as_ref(),
					env.set_id,
					&env.voters,
					&client,
					&network,
				);

				let voters = (*env.voters).clone();

				let last_completed_round = completed_rounds.last();

				Some(voter::Voter::new(
					env.clone(),
					voters,
					global_comms,
					last_completed_round.number,
					last_completed_round.state.clone(),
					last_finalized,
				))
			},
			VoterSetState::Paused { .. } => None,
		};

		// needs to be combined with another future otherwise it can deadlock.
		let poll_voter = future::poll_fn(move || match maybe_voter {
			Some(ref mut voter) => voter.poll(),
			None => Ok(Async::NotReady),
		});

		let client = client.clone();
		let config = config.clone();
		let network = network.clone();
		let select_chain = select_chain.clone();
		let authority_set = authority_set.clone();
		let consensus_changes = consensus_changes.clone();

		let handle_voter_command = move |command: VoterCommand<_, _>, voter_commands_rx| {
			match command {
				VoterCommand::ChangeAuthorities(new) => {
					let voters: Vec<String> = new.authorities.iter().map(move |(a, _)| {
						format!("{}", a)
					}).collect();
					telemetry!(CONSENSUS_INFO; "afg.voter_command_change_authorities";
						"number" => ?new.canon_number,
						"hash" => ?new.canon_hash,
						"voters" => ?voters,
						"set_id" => ?new.set_id,
					);

					// start the new authority set using the block where the
					// set changed (not where the signal happened!) as the base.
					let genesis_state = RoundState::genesis((new.canon_hash, new.canon_number));

					let set_state = VoterSetState::Live {
						// always start at round 0 when changing sets.
						completed_rounds: CompletedRounds::new(
							CompletedRound {
								number: 0,
								state: genesis_state,
								base: (new.canon_hash, new.canon_number),
								votes: Vec::new(),
							},
							new.set_id,
							&*authority_set.inner().read(),
						),
						current_round: HasVoted::No,
					};

					#[allow(deprecated)]
					aux_schema::write_voter_set_state(&**client.backend(), &set_state)?;

					let set_state: SharedVoterSetState<_> = set_state.into();

					let env = Arc::new(Environment {
						inner: client,
						select_chain,
						config,
						voters: Arc::new(new.authorities.into_iter().collect()),
						set_id: new.set_id,
						network,
						authority_set,
						consensus_changes,
						voter_set_state: set_state,
					});

					Ok(FutureLoop::Continue((env, voter_commands_rx)))
				}
				VoterCommand::Pause(reason) => {
					info!(target: "afg", "Pausing old validator set: {}", reason);

					// not racing because old voter is shut down.
					env.update_voter_set_state(|voter_set_state| {
						let completed_rounds = voter_set_state.completed_rounds();
						let set_state = VoterSetState::Paused { completed_rounds };

						#[allow(deprecated)]
						aux_schema::write_voter_set_state(&**client.backend(), &set_state)?;
						Ok(Some(set_state))
					})?;

					Ok(FutureLoop::Continue((env, voter_commands_rx)))
				},
			}
		};

		poll_voter.select2(voter_commands_rx).then(move |res| match res {
			Ok(future::Either::A(((), _))) => {
				// voters don't conclude naturally; this could reasonably be an error.
				Ok(FutureLoop::Break(()))
			},
			Err(future::Either::B(_)) => {
				// the `voter_commands_rx` stream should not fail.
				Ok(FutureLoop::Break(()))
			},
			Ok(future::Either::B(((None, _), _))) => {
				// the `voter_commands_rx` stream should never conclude since it's never closed.
				Ok(FutureLoop::Break(()))
			},
			Err(future::Either::A((CommandOrError::Error(e), _))) => {
				// return inner voter error
				Err(e)
			}
			Ok(future::Either::B(((Some(command), voter_commands_rx), _))) => {
				// some command issued externally.
				handle_voter_command(command, voter_commands_rx.into_future())
			}
			Err(future::Either::A((CommandOrError::VoterCommand(command), voter_commands_rx))) => {
				// some command issued internally.
				handle_voter_command(command, voter_commands_rx)
			},
		})
	});

	let voter_work = voter_work
		.map(|_| ())
		.map_err(|e| {
			warn!("GRANDPA Voter failed: {:?}", e);
			telemetry!(CONSENSUS_WARN; "afg.voter_failed"; "e" => ?e);
		});

	let voter_work = network_startup.and_then(move |()| voter_work);

	Ok(voter_work.select(on_exit).then(|_| Ok(())))
}

#[deprecated(since = "1.1", note = "Please switch to run_grandpa_voter.")]
pub fn run_grandpa<B, E, Block: BlockT<Hash=H256>, N, RA, SC, X>(
	grandpa_params: GrandpaParams<B, E, Block, N, RA, SC, X>,
) -> ::client::error::Result<impl Future<Item=(),Error=()> + Send + 'static> where
	Block::Hash: Ord,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
	N: Network<Block> + Send + Sync + 'static,
	N::In: Send + 'static,
	SC: SelectChain<Block> + 'static,
	NumberFor<Block>: BlockNumberOps,
	DigestFor<Block>: Encode,
	RA: Send + Sync + 'static,
	X: Future<Item=(),Error=()> + Clone + Send + 'static,
{
	run_grandpa_voter(grandpa_params)
}
