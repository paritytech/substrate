// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Integration of the GRANDPA finality gadget into substrate.
//!
//! This crate is unstable and the API and usage may change.
//!
//! This crate provides a long-running future that produces finality notifications.
//!
//! # Usage
//!
//! First, create a block-import wrapper with the `block_import` function. The
//! GRANDPA worker needs to be linked together with this block import object, so
//! a `LinkHalf` is returned as well. All blocks imported (from network or
//! consensus or otherwise) must pass through this wrapper, otherwise consensus
//! is likely to break in unexpected ways.
//!
//! Next, use the `LinkHalf` and a local configuration to `run_grandpa_voter`.
//! This requires a `Network` implementation. The returned future should be
//! driven to completion and will finalize blocks in the background.
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

#![warn(missing_docs)]

use futures::{prelude::*, StreamExt};
use log::{debug, error, info};
use parity_scale_codec::Decode;
use parking_lot::RwLock;
use prometheus_endpoint::{PrometheusError, Registry};
use sc_client_api::{
	backend::{AuxStore, Backend},
	utils::is_descendent_of,
	BlockchainEvents, CallExecutor, ExecutionStrategy, ExecutorProvider, Finalizer, LockImportRun,
	StorageProvider, TransactionFor,
};
use sc_consensus::BlockImport;
use sc_network::types::ProtocolName;
use sc_telemetry::{telemetry, TelemetryHandle, CONSENSUS_DEBUG, CONSENSUS_INFO};
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver};
use sp_api::ProvideRuntimeApi;
use sp_application_crypto::AppCrypto;
use sp_blockchain::{Error as ClientError, HeaderBackend, HeaderMetadata, Result as ClientResult};
use sp_consensus::SelectChain;
use sp_consensus_grandpa::{
	AuthorityList, AuthoritySignature, SetId, CLIENT_LOG_TARGET as LOG_TARGET,
};
use sp_core::{crypto::ByteArray, traits::CallContext};
use sp_keystore::KeystorePtr;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, NumberFor, Zero},
};

pub use finality_grandpa::BlockNumberOps;
use finality_grandpa::{voter, voter_set::VoterSet, Error as GrandpaError};

use std::{
	fmt, io,
	pin::Pin,
	sync::Arc,
	task::{Context, Poll},
	time::Duration,
};

// utility logging macro that takes as first argument a conditional to
// decide whether to log under debug or info level (useful to restrict
// logging under initial sync).
macro_rules! grandpa_log {
	($condition:expr, $($msg: expr),+ $(,)?) => {
		{
			let log_level = if $condition {
				log::Level::Debug
			} else {
				log::Level::Info
			};

			log::log!(target: LOG_TARGET, log_level, $($msg),+);
		}
	};
}

mod authorities;
mod aux_schema;
mod communication;
mod environment;
mod finality_proof;
mod import;
mod justification;
mod notification;
mod observer;
mod until_imported;
mod voting_rule;
pub mod warp_proof;

pub use authorities::{AuthoritySet, AuthoritySetChanges, SharedAuthoritySet};
pub use aux_schema::best_justification;
pub use communication::grandpa_protocol_name::standard_name as protocol_standard_name;
pub use finality_grandpa::voter::report;
pub use finality_proof::{FinalityProof, FinalityProofError, FinalityProofProvider};
pub use import::{find_forced_change, find_scheduled_change, GrandpaBlockImport};
pub use justification::GrandpaJustification;
pub use notification::{GrandpaJustificationSender, GrandpaJustificationStream};
pub use observer::run_grandpa_observer;
pub use voting_rule::{
	BeforeBestBlockBy, ThreeQuartersOfTheUnfinalizedChain, VotingRule, VotingRuleResult,
	VotingRulesBuilder,
};

use aux_schema::PersistentData;
use communication::{Network as NetworkT, NetworkBridge, Syncing as SyncingT};
use environment::{Environment, VoterSetState};
use until_imported::UntilGlobalMessageBlocksImported;

// Re-export these two because it's just so damn convenient.
pub use sp_consensus_grandpa::{
	AuthorityId, AuthorityPair, CatchUp, Commit, CompactCommit, GrandpaApi, Message, Precommit,
	Prevote, PrimaryPropose, ScheduledChange, SignedMessage,
};
use std::marker::PhantomData;

#[cfg(test)]
mod tests;

/// A global communication input stream for commits and catch up messages. Not
/// exposed publicly, used internally to simplify types in the communication
/// layer.
type CommunicationIn<Block> = voter::CommunicationIn<
	<Block as BlockT>::Hash,
	NumberFor<Block>,
	AuthoritySignature,
	AuthorityId,
>;
/// Global communication input stream for commits and catch up messages, with
/// the hash type not being derived from the block, useful for forcing the hash
/// to some type (e.g. `H256`) when the compiler can't do the inference.
type CommunicationInH<Block, H> =
	voter::CommunicationIn<H, NumberFor<Block>, AuthoritySignature, AuthorityId>;

/// Global communication sink for commits with the hash type not being derived
/// from the block, useful for forcing the hash to some type (e.g. `H256`) when
/// the compiler can't do the inference.
type CommunicationOutH<Block, H> =
	voter::CommunicationOut<H, NumberFor<Block>, AuthoritySignature, AuthorityId>;

/// Shared voter state for querying.
pub struct SharedVoterState {
	inner: Arc<RwLock<Option<Box<dyn voter::VoterState<AuthorityId> + Sync + Send>>>>,
}

impl SharedVoterState {
	/// Create a new empty `SharedVoterState` instance.
	pub fn empty() -> Self {
		Self { inner: Arc::new(RwLock::new(None)) }
	}

	fn reset(
		&self,
		voter_state: Box<dyn voter::VoterState<AuthorityId> + Sync + Send>,
	) -> Option<()> {
		let mut shared_voter_state = self.inner.try_write_for(Duration::from_secs(1))?;

		*shared_voter_state = Some(voter_state);
		Some(())
	}

	/// Get the inner `VoterState` instance.
	pub fn voter_state(&self) -> Option<report::VoterState<AuthorityId>> {
		self.inner.read().as_ref().map(|vs| vs.get())
	}
}

impl Clone for SharedVoterState {
	fn clone(&self) -> Self {
		SharedVoterState { inner: self.inner.clone() }
	}
}

/// Configuration for the GRANDPA service
#[derive(Clone)]
pub struct Config {
	/// The expected duration for a message to be gossiped across the network.
	pub gossip_duration: Duration,
	/// Justification generation period (in blocks). GRANDPA will try to generate justifications
	/// at least every justification_period blocks. There are some other events which might cause
	/// justification generation.
	pub justification_period: u32,
	/// Whether the GRANDPA observer protocol is live on the network and thereby
	/// a full-node not running as a validator is running the GRANDPA observer
	/// protocol (we will only issue catch-up requests to authorities when the
	/// observer protocol is enabled).
	pub observer_enabled: bool,
	/// The role of the local node (i.e. authority, full-node or light).
	pub local_role: sc_network::config::Role,
	/// Some local identifier of the voter.
	pub name: Option<String>,
	/// The keystore that manages the keys of this node.
	pub keystore: Option<KeystorePtr>,
	/// TelemetryHandle instance.
	pub telemetry: Option<TelemetryHandle>,
	/// Chain specific GRANDPA protocol name. See [`crate::protocol_standard_name`].
	pub protocol_name: ProtocolName,
}

impl Config {
	fn name(&self) -> &str {
		self.name.as_deref().unwrap_or("<unknown>")
	}
}

/// Errors that can occur while voting in GRANDPA.
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// An error within grandpa.
	#[error("grandpa error: {0}")]
	Grandpa(#[from] GrandpaError),

	/// A network error.
	#[error("network error: {0}")]
	Network(String),

	/// A blockchain error.
	#[error("blockchain error: {0}")]
	Blockchain(String),

	/// Could not complete a round on disk.
	#[error("could not complete a round on disk: {0}")]
	Client(#[from] ClientError),

	/// Could not sign outgoing message
	#[error("could not sign outgoing message: {0}")]
	Signing(String),

	/// An invariant has been violated (e.g. not finalizing pending change blocks in-order)
	#[error("safety invariant has been violated: {0}")]
	Safety(String),

	/// A timer failed to fire.
	#[error("a timer failed to fire: {0}")]
	Timer(io::Error),

	/// A runtime api request failed.
	#[error("runtime API request failed: {0}")]
	RuntimeApi(sp_api::ApiError),
}

/// Something which can determine if a block is known.
pub(crate) trait BlockStatus<Block: BlockT> {
	/// Return `Ok(Some(number))` or `Ok(None)` depending on whether the block
	/// is definitely known and has been imported.
	/// If an unexpected error occurs, return that.
	fn block_number(&self, hash: Block::Hash) -> Result<Option<NumberFor<Block>>, Error>;
}

impl<Block: BlockT, Client> BlockStatus<Block> for Arc<Client>
where
	Client: HeaderBackend<Block>,
	NumberFor<Block>: BlockNumberOps,
{
	fn block_number(&self, hash: Block::Hash) -> Result<Option<NumberFor<Block>>, Error> {
		self.block_number_from_id(&BlockId::Hash(hash))
			.map_err(|e| Error::Blockchain(e.to_string()))
	}
}

/// A trait that includes all the client functionalities grandpa requires.
/// Ideally this would be a trait alias, we're not there yet.
/// tracking issue <https://github.com/rust-lang/rust/issues/41517>
pub trait ClientForGrandpa<Block, BE>:
	LockImportRun<Block, BE>
	+ Finalizer<Block, BE>
	+ AuxStore
	+ HeaderMetadata<Block, Error = sp_blockchain::Error>
	+ HeaderBackend<Block>
	+ BlockchainEvents<Block>
	+ ProvideRuntimeApi<Block>
	+ ExecutorProvider<Block>
	+ BlockImport<Block, Transaction = TransactionFor<BE, Block>, Error = sp_consensus::Error>
	+ StorageProvider<Block, BE>
where
	BE: Backend<Block>,
	Block: BlockT,
{
}

impl<Block, BE, T> ClientForGrandpa<Block, BE> for T
where
	BE: Backend<Block>,
	Block: BlockT,
	T: LockImportRun<Block, BE>
		+ Finalizer<Block, BE>
		+ AuxStore
		+ HeaderMetadata<Block, Error = sp_blockchain::Error>
		+ HeaderBackend<Block>
		+ BlockchainEvents<Block>
		+ ProvideRuntimeApi<Block>
		+ ExecutorProvider<Block>
		+ BlockImport<Block, Transaction = TransactionFor<BE, Block>, Error = sp_consensus::Error>
		+ StorageProvider<Block, BE>,
{
}

/// Something that one can ask to do a block sync request.
pub(crate) trait BlockSyncRequester<Block: BlockT> {
	/// Notifies the sync service to try and sync the given block from the given
	/// peers.
	///
	/// If the given vector of peers is empty then the underlying implementation
	/// should make a best effort to fetch the block from any peers it is
	/// connected to (NOTE: this assumption will change in the future #3629).
	fn set_sync_fork_request(
		&self,
		peers: Vec<sc_network::PeerId>,
		hash: Block::Hash,
		number: NumberFor<Block>,
	);
}

impl<Block, Network, Syncing> BlockSyncRequester<Block> for NetworkBridge<Block, Network, Syncing>
where
	Block: BlockT,
	Network: NetworkT<Block>,
	Syncing: SyncingT<Block>,
{
	fn set_sync_fork_request(
		&self,
		peers: Vec<sc_network::PeerId>,
		hash: Block::Hash,
		number: NumberFor<Block>,
	) {
		NetworkBridge::set_sync_fork_request(self, peers, hash, number)
	}
}

/// A new authority set along with the canonical block it changed at.
#[derive(Debug)]
pub(crate) struct NewAuthoritySet<H, N> {
	pub(crate) canon_number: N,
	pub(crate) canon_hash: H,
	pub(crate) set_id: SetId,
	pub(crate) authorities: AuthorityList,
}

/// Commands issued to the voter.
#[derive(Debug)]
pub(crate) enum VoterCommand<H, N> {
	/// Pause the voter for given reason.
	Pause(String),
	/// New authorities.
	ChangeAuthorities(NewAuthoritySet<H, N>),
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

impl<H, N> From<finality_grandpa::Error> for CommandOrError<H, N> {
	fn from(e: finality_grandpa::Error) -> Self {
		CommandOrError::Error(Error::from(e))
	}
}

impl<H, N> From<VoterCommand<H, N>> for CommandOrError<H, N> {
	fn from(e: VoterCommand<H, N>) -> Self {
		CommandOrError::VoterCommand(e)
	}
}

impl<H: fmt::Debug, N: fmt::Debug> ::std::error::Error for CommandOrError<H, N> {}

impl<H, N> fmt::Display for CommandOrError<H, N> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			CommandOrError::Error(ref e) => write!(f, "{}", e),
			CommandOrError::VoterCommand(ref cmd) => write!(f, "{}", cmd),
		}
	}
}

/// Link between the block importer and the background voter.
pub struct LinkHalf<Block: BlockT, C, SC> {
	client: Arc<C>,
	select_chain: SC,
	persistent_data: PersistentData<Block>,
	voter_commands_rx: TracingUnboundedReceiver<VoterCommand<Block::Hash, NumberFor<Block>>>,
	justification_sender: GrandpaJustificationSender<Block>,
	justification_stream: GrandpaJustificationStream<Block>,
	telemetry: Option<TelemetryHandle>,
}

impl<Block: BlockT, C, SC> LinkHalf<Block, C, SC> {
	/// Get the shared authority set.
	pub fn shared_authority_set(&self) -> &SharedAuthoritySet<Block::Hash, NumberFor<Block>> {
		&self.persistent_data.authority_set
	}

	/// Get the receiving end of justification notifications.
	pub fn justification_stream(&self) -> GrandpaJustificationStream<Block> {
		self.justification_stream.clone()
	}
}

/// Provider for the Grandpa authority set configured on the genesis block.
pub trait GenesisAuthoritySetProvider<Block: BlockT> {
	/// Get the authority set at the genesis block.
	fn get(&self) -> Result<AuthorityList, ClientError>;
}

impl<Block: BlockT, E, Client> GenesisAuthoritySetProvider<Block> for Arc<Client>
where
	E: CallExecutor<Block>,
	Client: ExecutorProvider<Block, Executor = E> + HeaderBackend<Block>,
{
	fn get(&self) -> Result<AuthorityList, ClientError> {
		// This implementation uses the Grandpa runtime API instead of reading directly from the
		// `GRANDPA_AUTHORITIES_KEY` as the data may have been migrated since the genesis block of
		// the chain, whereas the runtime API is backwards compatible.
		self.executor()
			.call(
				self.expect_block_hash_from_id(&BlockId::Number(Zero::zero()))?,
				"GrandpaApi_grandpa_authorities",
				&[],
				ExecutionStrategy::NativeElseWasm,
				CallContext::Offchain,
			)
			.and_then(|call_result| {
				Decode::decode(&mut &call_result[..]).map_err(|err| {
					ClientError::CallResultDecode(
						"failed to decode GRANDPA authorities set proof",
						err,
					)
				})
			})
	}
}

/// Make block importer and link half necessary to tie the background voter
/// to it.
pub fn block_import<BE, Block: BlockT, Client, SC>(
	client: Arc<Client>,
	genesis_authorities_provider: &dyn GenesisAuthoritySetProvider<Block>,
	select_chain: SC,
	telemetry: Option<TelemetryHandle>,
) -> Result<(GrandpaBlockImport<BE, Block, Client, SC>, LinkHalf<Block, Client, SC>), ClientError>
where
	SC: SelectChain<Block>,
	BE: Backend<Block> + 'static,
	Client: ClientForGrandpa<Block, BE> + 'static,
{
	block_import_with_authority_set_hard_forks(
		client,
		genesis_authorities_provider,
		select_chain,
		Default::default(),
		telemetry,
	)
}

/// A descriptor for an authority set hard fork. These are authority set changes
/// that are not signalled by the runtime and instead are defined off-chain
/// (hence the hard fork).
pub struct AuthoritySetHardFork<Block: BlockT> {
	/// The new authority set id.
	pub set_id: SetId,
	/// The block hash and number at which the hard fork should be applied.
	pub block: (Block::Hash, NumberFor<Block>),
	/// The authorities in the new set.
	pub authorities: AuthorityList,
	/// The latest block number that was finalized before this authority set
	/// hard fork. When defined, the authority set change will be forced, i.e.
	/// the node won't wait for the block above to be finalized before enacting
	/// the change, and the given finalized number will be used as a base for
	/// voting.
	pub last_finalized: Option<NumberFor<Block>>,
}

/// Make block importer and link half necessary to tie the background voter to
/// it. A vector of authority set hard forks can be passed, any authority set
/// change signaled at the given block (either already signalled or in a further
/// block when importing it) will be replaced by a standard change with the
/// given static authorities.
pub fn block_import_with_authority_set_hard_forks<BE, Block: BlockT, Client, SC>(
	client: Arc<Client>,
	genesis_authorities_provider: &dyn GenesisAuthoritySetProvider<Block>,
	select_chain: SC,
	authority_set_hard_forks: Vec<AuthoritySetHardFork<Block>>,
	telemetry: Option<TelemetryHandle>,
) -> Result<(GrandpaBlockImport<BE, Block, Client, SC>, LinkHalf<Block, Client, SC>), ClientError>
where
	SC: SelectChain<Block>,
	BE: Backend<Block> + 'static,
	Client: ClientForGrandpa<Block, BE> + 'static,
{
	let chain_info = client.info();
	let genesis_hash = chain_info.genesis_hash;

	let persistent_data =
		aux_schema::load_persistent(&*client, genesis_hash, <NumberFor<Block>>::zero(), {
			let telemetry = telemetry.clone();
			move || {
				let authorities = genesis_authorities_provider.get()?;
				telemetry!(
					telemetry;
					CONSENSUS_DEBUG;
					"afg.loading_authorities";
					"authorities_len" => ?authorities.len()
				);
				Ok(authorities)
			}
		})?;

	let (voter_commands_tx, voter_commands_rx) =
		tracing_unbounded("mpsc_grandpa_voter_command", 100_000);

	let (justification_sender, justification_stream) = GrandpaJustificationStream::channel();

	// create pending change objects with 0 delay for each authority set hard fork.
	let authority_set_hard_forks = authority_set_hard_forks
		.into_iter()
		.map(|fork| {
			let delay_kind = if let Some(last_finalized) = fork.last_finalized {
				authorities::DelayKind::Best { median_last_finalized: last_finalized }
			} else {
				authorities::DelayKind::Finalized
			};

			(
				fork.set_id,
				authorities::PendingChange {
					next_authorities: fork.authorities,
					delay: Zero::zero(),
					canon_hash: fork.block.0,
					canon_height: fork.block.1,
					delay_kind,
				},
			)
		})
		.collect();

	Ok((
		GrandpaBlockImport::new(
			client.clone(),
			select_chain.clone(),
			persistent_data.authority_set.clone(),
			voter_commands_tx,
			authority_set_hard_forks,
			justification_sender.clone(),
			telemetry.clone(),
		),
		LinkHalf {
			client,
			select_chain,
			persistent_data,
			voter_commands_rx,
			justification_sender,
			justification_stream,
			telemetry,
		},
	))
}

fn global_communication<BE, Block: BlockT, C, N, S>(
	set_id: SetId,
	voters: &Arc<VoterSet<AuthorityId>>,
	client: Arc<C>,
	network: &NetworkBridge<Block, N, S>,
	keystore: Option<&KeystorePtr>,
	metrics: Option<until_imported::Metrics>,
) -> (
	impl Stream<
		Item = Result<
			CommunicationInH<Block, Block::Hash>,
			CommandOrError<Block::Hash, NumberFor<Block>>,
		>,
	>,
	impl Sink<
		CommunicationOutH<Block, Block::Hash>,
		Error = CommandOrError<Block::Hash, NumberFor<Block>>,
	>,
)
where
	BE: Backend<Block> + 'static,
	C: ClientForGrandpa<Block, BE> + 'static,
	N: NetworkT<Block>,
	S: SyncingT<Block>,
	NumberFor<Block>: BlockNumberOps,
{
	let is_voter = local_authority_id(voters, keystore).is_some();

	// verification stream
	let (global_in, global_out) =
		network.global_communication(communication::SetId(set_id), voters.clone(), is_voter);

	// block commit and catch up messages until relevant blocks are imported.
	let global_in = UntilGlobalMessageBlocksImported::new(
		client.import_notification_stream(),
		network.clone(),
		client.clone(),
		global_in,
		"global",
		metrics,
	);

	let global_in = global_in.map_err(CommandOrError::from);
	let global_out = global_out.sink_map_err(CommandOrError::from);

	(global_in, global_out)
}

/// Parameters used to run Grandpa.
pub struct GrandpaParams<Block: BlockT, C, N, S, SC, VR> {
	/// Configuration for the GRANDPA service.
	pub config: Config,
	/// A link to the block import worker.
	pub link: LinkHalf<Block, C, SC>,
	/// The Network instance.
	///
	/// It is assumed that this network will feed us Grandpa notifications. When using the
	/// `sc_network` crate, it is assumed that the Grandpa notifications protocol has been passed
	/// to the configuration of the networking. See [`grandpa_peers_set_config`].
	pub network: N,
	/// Event stream for syncing-related events.
	pub sync: S,
	/// A voting rule used to potentially restrict target votes.
	pub voting_rule: VR,
	/// The prometheus metrics registry.
	pub prometheus_registry: Option<prometheus_endpoint::Registry>,
	/// The voter state is exposed at an RPC endpoint.
	pub shared_voter_state: SharedVoterState,
	/// TelemetryHandle instance.
	pub telemetry: Option<TelemetryHandle>,
}

/// Returns the configuration value to put in
/// [`sc_network::config::FullNetworkConfiguration`].
/// For standard protocol name see [`crate::protocol_standard_name`].
pub fn grandpa_peers_set_config(
	protocol_name: ProtocolName,
) -> sc_network::config::NonDefaultSetConfig {
	use communication::grandpa_protocol_name;
	sc_network::config::NonDefaultSetConfig {
		notifications_protocol: protocol_name,
		fallback_names: grandpa_protocol_name::LEGACY_NAMES.iter().map(|&n| n.into()).collect(),
		// Notifications reach ~256kiB in size at the time of writing on Kusama and Polkadot.
		max_notification_size: 1024 * 1024,
		handshake: None,
		set_config: sc_network::config::SetConfig {
			in_peers: 0,
			out_peers: 0,
			reserved_nodes: Vec::new(),
			non_reserved_mode: sc_network::config::NonReservedPeerMode::Deny,
		},
	}
}

/// Run a GRANDPA voter as a task. Provide configuration and a link to a
/// block import worker that has already been instantiated with `block_import`.
pub fn run_grandpa_voter<Block: BlockT, BE: 'static, C, N, S, SC, VR>(
	grandpa_params: GrandpaParams<Block, C, N, S, SC, VR>,
) -> sp_blockchain::Result<impl Future<Output = ()> + Send>
where
	Block::Hash: Ord,
	BE: Backend<Block> + 'static,
	N: NetworkT<Block> + Sync + 'static,
	S: SyncingT<Block> + Sync + 'static,
	SC: SelectChain<Block> + 'static,
	VR: VotingRule<Block, C> + Clone + 'static,
	NumberFor<Block>: BlockNumberOps,
	C: ClientForGrandpa<Block, BE> + 'static,
	C::Api: GrandpaApi<Block>,
{
	let GrandpaParams {
		mut config,
		link,
		network,
		sync,
		voting_rule,
		prometheus_registry,
		shared_voter_state,
		telemetry,
	} = grandpa_params;

	// NOTE: we have recently removed `run_grandpa_observer` from the public
	// API, I felt it is easier to just ignore this field rather than removing
	// it from the config temporarily. This should be removed after #5013 is
	// fixed and we re-add the observer to the public API.
	config.observer_enabled = false;

	let LinkHalf {
		client,
		select_chain,
		persistent_data,
		voter_commands_rx,
		justification_sender,
		justification_stream: _,
		telemetry: _,
	} = link;

	let network = NetworkBridge::new(
		network,
		sync,
		config.clone(),
		persistent_data.set_state.clone(),
		prometheus_registry.as_ref(),
		telemetry.clone(),
	);

	let conf = config.clone();
	let telemetry_task =
		if let Some(telemetry_on_connect) = telemetry.as_ref().map(|x| x.on_connect_stream()) {
			let authorities = persistent_data.authority_set.clone();
			let telemetry = telemetry.clone();
			let events = telemetry_on_connect.for_each(move |_| {
				let current_authorities = authorities.current_authorities();
				let set_id = authorities.set_id();
				let maybe_authority_id =
					local_authority_id(&current_authorities, conf.keystore.as_ref());

				let authorities =
					current_authorities.iter().map(|(id, _)| id.to_string()).collect::<Vec<_>>();

				let authorities = serde_json::to_string(&authorities).expect(
					"authorities is always at least an empty vector; \
					 elements are always of type string",
				);

				telemetry!(
					telemetry;
					CONSENSUS_INFO;
					"afg.authority_set";
					"authority_id" => maybe_authority_id.map_or("".into(), |s| s.to_string()),
					"authority_set_id" => ?set_id,
					"authorities" => authorities,
				);

				future::ready(())
			});
			future::Either::Left(events)
		} else {
			future::Either::Right(future::pending())
		};

	let voter_work = VoterWork::new(
		client,
		config,
		network,
		select_chain,
		voting_rule,
		persistent_data,
		voter_commands_rx,
		prometheus_registry,
		shared_voter_state,
		justification_sender,
		telemetry,
	);

	let voter_work = voter_work.map(|res| match res {
		Ok(()) => error!(
			target: LOG_TARGET,
			"GRANDPA voter future has concluded naturally, this should be unreachable."
		),
		Err(e) => error!(target: LOG_TARGET, "GRANDPA voter error: {}", e),
	});

	// Make sure that `telemetry_task` doesn't accidentally finish and kill grandpa.
	let telemetry_task = telemetry_task.then(|_| future::pending::<()>());

	Ok(future::select(voter_work, telemetry_task).map(drop))
}

struct Metrics {
	environment: environment::Metrics,
	until_imported: until_imported::Metrics,
}

impl Metrics {
	fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Metrics {
			environment: environment::Metrics::register(registry)?,
			until_imported: until_imported::Metrics::register(registry)?,
		})
	}
}

/// Future that powers the voter.
#[must_use]
struct VoterWork<B, Block: BlockT, C, N: NetworkT<Block>, S: SyncingT<Block>, SC, VR> {
	voter: Pin<
		Box<dyn Future<Output = Result<(), CommandOrError<Block::Hash, NumberFor<Block>>>> + Send>,
	>,
	shared_voter_state: SharedVoterState,
	env: Arc<Environment<B, Block, C, N, S, SC, VR>>,
	voter_commands_rx: TracingUnboundedReceiver<VoterCommand<Block::Hash, NumberFor<Block>>>,
	network: NetworkBridge<Block, N, S>,
	telemetry: Option<TelemetryHandle>,
	/// Prometheus metrics.
	metrics: Option<Metrics>,
}

impl<B, Block, C, N, S, SC, VR> VoterWork<B, Block, C, N, S, SC, VR>
where
	Block: BlockT,
	B: Backend<Block> + 'static,
	C: ClientForGrandpa<Block, B> + 'static,
	C::Api: GrandpaApi<Block>,
	N: NetworkT<Block> + Sync,
	S: SyncingT<Block> + Sync,
	NumberFor<Block>: BlockNumberOps,
	SC: SelectChain<Block> + 'static,
	VR: VotingRule<Block, C> + Clone + 'static,
{
	fn new(
		client: Arc<C>,
		config: Config,
		network: NetworkBridge<Block, N, S>,
		select_chain: SC,
		voting_rule: VR,
		persistent_data: PersistentData<Block>,
		voter_commands_rx: TracingUnboundedReceiver<VoterCommand<Block::Hash, NumberFor<Block>>>,
		prometheus_registry: Option<prometheus_endpoint::Registry>,
		shared_voter_state: SharedVoterState,
		justification_sender: GrandpaJustificationSender<Block>,
		telemetry: Option<TelemetryHandle>,
	) -> Self {
		let metrics = match prometheus_registry.as_ref().map(Metrics::register) {
			Some(Ok(metrics)) => Some(metrics),
			Some(Err(e)) => {
				debug!(target: LOG_TARGET, "Failed to register metrics: {:?}", e);
				None
			},
			None => None,
		};

		let voters = persistent_data.authority_set.current_authorities();
		let env = Arc::new(Environment {
			client,
			select_chain,
			voting_rule,
			voters: Arc::new(voters),
			config,
			network: network.clone(),
			set_id: persistent_data.authority_set.set_id(),
			authority_set: persistent_data.authority_set.clone(),
			voter_set_state: persistent_data.set_state,
			metrics: metrics.as_ref().map(|m| m.environment.clone()),
			justification_sender: Some(justification_sender),
			telemetry: telemetry.clone(),
			_phantom: PhantomData,
		});

		let mut work = VoterWork {
			// `voter` is set to a temporary value and replaced below when
			// calling `rebuild_voter`.
			voter: Box::pin(future::pending()),
			shared_voter_state,
			env,
			voter_commands_rx,
			network,
			telemetry,
			metrics,
		};
		work.rebuild_voter();
		work
	}

	/// Rebuilds the `self.voter` field using the current authority set
	/// state. This method should be called when we know that the authority set
	/// has changed (e.g. as signalled by a voter command).
	fn rebuild_voter(&mut self) {
		debug!(
			target: LOG_TARGET,
			"{}: Starting new voter with set ID {}",
			self.env.config.name(),
			self.env.set_id
		);

		let maybe_authority_id =
			local_authority_id(&self.env.voters, self.env.config.keystore.as_ref());
		let authority_id = maybe_authority_id.map_or("<unknown>".into(), |s| s.to_string());

		telemetry!(
			self.telemetry;
			CONSENSUS_DEBUG;
			"afg.starting_new_voter";
			"name" => ?self.env.config.name(),
			"set_id" => ?self.env.set_id,
			"authority_id" => authority_id,
		);

		let chain_info = self.env.client.info();

		let authorities = self.env.voters.iter().map(|(id, _)| id.to_string()).collect::<Vec<_>>();

		let authorities = serde_json::to_string(&authorities).expect(
			"authorities is always at least an empty vector; elements are always of type string; qed.",
		);

		telemetry!(
			self.telemetry;
			CONSENSUS_INFO;
			"afg.authority_set";
			"number" => ?chain_info.finalized_number,
			"hash" => ?chain_info.finalized_hash,
			"authority_id" => authority_id,
			"authority_set_id" => ?self.env.set_id,
			"authorities" => authorities,
		);

		match &*self.env.voter_set_state.read() {
			VoterSetState::Live { completed_rounds, .. } => {
				let last_finalized = (chain_info.finalized_hash, chain_info.finalized_number);

				let global_comms = global_communication(
					self.env.set_id,
					&self.env.voters,
					self.env.client.clone(),
					&self.env.network,
					self.env.config.keystore.as_ref(),
					self.metrics.as_ref().map(|m| m.until_imported.clone()),
				);

				let last_completed_round = completed_rounds.last();

				let voter = voter::Voter::new(
					self.env.clone(),
					(*self.env.voters).clone(),
					global_comms,
					last_completed_round.number,
					last_completed_round.votes.clone(),
					last_completed_round.base,
					last_finalized,
				);

				// Repoint shared_voter_state so that the RPC endpoint can query the state
				if self.shared_voter_state.reset(voter.voter_state()).is_none() {
					info!(
						target: LOG_TARGET,
						"Timed out trying to update shared GRANDPA voter state. \
						RPC endpoints may return stale data."
					);
				}

				self.voter = Box::pin(voter);
			},
			VoterSetState::Paused { .. } => self.voter = Box::pin(future::pending()),
		};
	}

	fn handle_voter_command(
		&mut self,
		command: VoterCommand<Block::Hash, NumberFor<Block>>,
	) -> Result<(), Error> {
		match command {
			VoterCommand::ChangeAuthorities(new) => {
				let voters: Vec<String> =
					new.authorities.iter().map(move |(a, _)| format!("{}", a)).collect();
				telemetry!(
					self.telemetry;
					CONSENSUS_INFO;
					"afg.voter_command_change_authorities";
					"number" => ?new.canon_number,
					"hash" => ?new.canon_hash,
					"voters" => ?voters,
					"set_id" => ?new.set_id,
				);

				self.env.update_voter_set_state(|_| {
					// start the new authority set using the block where the
					// set changed (not where the signal happened!) as the base.
					let set_state = VoterSetState::live(
						new.set_id,
						&*self.env.authority_set.inner(),
						(new.canon_hash, new.canon_number),
					);

					aux_schema::write_voter_set_state(&*self.env.client, &set_state)?;
					Ok(Some(set_state))
				})?;

				let voters = Arc::new(VoterSet::new(new.authorities.into_iter()).expect(
					"new authorities come from pending change; pending change comes from \
					 `AuthoritySet`; `AuthoritySet` validates authorities is non-empty and \
					 weights are non-zero; qed.",
				));

				self.env = Arc::new(Environment {
					voters,
					set_id: new.set_id,
					voter_set_state: self.env.voter_set_state.clone(),
					client: self.env.client.clone(),
					select_chain: self.env.select_chain.clone(),
					config: self.env.config.clone(),
					authority_set: self.env.authority_set.clone(),
					network: self.env.network.clone(),
					voting_rule: self.env.voting_rule.clone(),
					metrics: self.env.metrics.clone(),
					justification_sender: self.env.justification_sender.clone(),
					telemetry: self.telemetry.clone(),
					_phantom: PhantomData,
				});

				self.rebuild_voter();
				Ok(())
			},
			VoterCommand::Pause(reason) => {
				info!(target: LOG_TARGET, "Pausing old validator set: {}", reason);

				// not racing because old voter is shut down.
				self.env.update_voter_set_state(|voter_set_state| {
					let completed_rounds = voter_set_state.completed_rounds();
					let set_state = VoterSetState::Paused { completed_rounds };

					aux_schema::write_voter_set_state(&*self.env.client, &set_state)?;
					Ok(Some(set_state))
				})?;

				self.rebuild_voter();
				Ok(())
			},
		}
	}
}

impl<B, Block, C, N, S, SC, VR> Future for VoterWork<B, Block, C, N, S, SC, VR>
where
	Block: BlockT,
	B: Backend<Block> + 'static,
	N: NetworkT<Block> + Sync,
	S: SyncingT<Block> + Sync,
	NumberFor<Block>: BlockNumberOps,
	SC: SelectChain<Block> + 'static,
	C: ClientForGrandpa<Block, B> + 'static,
	C::Api: GrandpaApi<Block>,
	VR: VotingRule<Block, C> + Clone + 'static,
{
	type Output = Result<(), Error>;

	fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		match Future::poll(Pin::new(&mut self.voter), cx) {
			Poll::Pending => {},
			Poll::Ready(Ok(())) => {
				// voters don't conclude naturally
				return Poll::Ready(Err(Error::Safety(
					"consensus-grandpa inner voter has concluded.".into(),
				)))
			},
			Poll::Ready(Err(CommandOrError::Error(e))) => {
				// return inner observer error
				return Poll::Ready(Err(e))
			},
			Poll::Ready(Err(CommandOrError::VoterCommand(command))) => {
				// some command issued internally
				self.handle_voter_command(command)?;
				cx.waker().wake_by_ref();
			},
		}

		match Stream::poll_next(Pin::new(&mut self.voter_commands_rx), cx) {
			Poll::Pending => {},
			Poll::Ready(None) => {
				// the `voter_commands_rx` stream should never conclude since it's never closed.
				return Poll::Ready(Err(Error::Safety("`voter_commands_rx` was closed.".into())))
			},
			Poll::Ready(Some(command)) => {
				// some command issued externally
				self.handle_voter_command(command)?;
				cx.waker().wake_by_ref();
			},
		}

		Future::poll(Pin::new(&mut self.network), cx)
	}
}

/// Checks if this node has any available keys in the keystore for any authority id in the given
/// voter set.  Returns the authority id for which keys are available, or `None` if no keys are
/// available.
fn local_authority_id(
	voters: &VoterSet<AuthorityId>,
	keystore: Option<&KeystorePtr>,
) -> Option<AuthorityId> {
	keystore.and_then(|keystore| {
		voters
			.iter()
			.find(|(p, _)| keystore.has_keys(&[(p.to_raw_vec(), AuthorityId::ID)]))
			.map(|(p, _)| p.clone())
	})
}

/// Reverts protocol aux data to at most the last finalized block.
/// In particular, standard and forced authority set changes announced after the
/// revert point are removed.
pub fn revert<Block, Client>(client: Arc<Client>, blocks: NumberFor<Block>) -> ClientResult<()>
where
	Block: BlockT,
	Client: AuxStore + HeaderMetadata<Block, Error = ClientError> + HeaderBackend<Block>,
{
	let best_number = client.info().best_number;
	let finalized = client.info().finalized_number;

	let revertible = blocks.min(best_number - finalized);
	if revertible == Zero::zero() {
		return Ok(())
	}

	let number = best_number - revertible;
	let hash = client
		.block_hash_from_id(&BlockId::Number(number))?
		.ok_or(ClientError::Backend(format!(
			"Unexpected hash lookup failure for block number: {}",
			number
		)))?;

	let info = client.info();

	let persistent_data: PersistentData<Block> =
		aux_schema::load_persistent(&*client, info.genesis_hash, Zero::zero(), || {
			const MSG: &str = "Unexpected missing grandpa data during revert";
			Err(ClientError::Application(Box::from(MSG)))
		})?;

	let shared_authority_set = persistent_data.authority_set;
	let mut authority_set = shared_authority_set.inner();

	let is_descendent_of = is_descendent_of(&*client, None);
	authority_set.revert(hash, number, &is_descendent_of);

	// The following has the side effect to properly reset the current voter state.
	let (set_id, set_ref) = authority_set.current();
	let new_set = Some(NewAuthoritySet {
		canon_hash: info.finalized_hash,
		canon_number: info.finalized_number,
		set_id,
		authorities: set_ref.to_vec(),
	});
	aux_schema::update_authority_set::<Block, _, _>(&authority_set, new_set.as_ref(), |values| {
		client.insert_aux(values, None)
	})
}
