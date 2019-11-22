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

use futures::prelude::*;
use log::{debug, error, info};
use futures::sync::mpsc;
use client_api::{BlockchainEvents, CallExecutor, backend::Backend, ExecutionStrategy};
use sp_blockchain::{HeaderBackend, Error as ClientError};
use client::Client;
use codec::{Decode, Encode};
use sr_primitives::generic::BlockId;
use sr_primitives::traits::{NumberFor, Block as BlockT, DigestFor, Zero};
use keystore::KeyStorePtr;
use inherents::InherentDataProviders;
use consensus_common::SelectChain;
use primitives::{H256, Blake2Hasher, Pair};
use substrate_telemetry::{telemetry, CONSENSUS_INFO, CONSENSUS_DEBUG, CONSENSUS_WARN};
use serde_json;

use sp_finality_tracker;

use grandpa::Error as GrandpaError;
use grandpa::{voter, BlockNumberOps, voter_set::VoterSet};

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
mod voting_rule;

pub use communication::Network;
pub use finality_proof::FinalityProofProvider;
pub use justification::GrandpaJustification;
pub use light_import::light_block_import;
pub use observer::run_grandpa_observer;
pub use voting_rule::{
	BeforeBestBlock, ThreeQuartersOfTheUnfinalizedChain, VotingRule, VotingRulesBuilder
};

use aux_schema::PersistentData;
use environment::{Environment, VoterSetState};
use import::GrandpaBlockImport;
use until_imported::UntilGlobalMessageBlocksImported;
use communication::NetworkBridge;
use fg_primitives::{AuthorityList, AuthorityPair, AuthoritySignature, SetId};

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
/// A catch up message for this chain's block type.
pub type CatchUp<Block> = grandpa::CatchUp<
	<Block as BlockT>::Hash,
	NumberFor<Block>,
	AuthoritySignature,
	AuthorityId,
>;
/// A commit message for this chain's block type.
pub type Commit<Block> = grandpa::Commit<
	<Block as BlockT>::Hash,
	NumberFor<Block>,
	AuthoritySignature,
	AuthorityId,
>;
/// A compact commit message for this chain's block type.
pub type CompactCommit<Block> = grandpa::CompactCommit<
	<Block as BlockT>::Hash,
	NumberFor<Block>,
	AuthoritySignature,
	AuthorityId,
>;
/// A global communication input stream for commits and catch up messages. Not
/// exposed publicly, used internally to simplify types in the communication
/// layer.
type CommunicationIn<Block> = grandpa::voter::CommunicationIn<
	<Block as BlockT>::Hash,
	NumberFor<Block>,
	AuthoritySignature,
	AuthorityId,
>;

/// Global communication input stream for commits and catch up messages, with
/// the hash type not being derived from the block, useful for forcing the hash
/// to some type (e.g. `H256`) when the compiler can't do the inference.
type CommunicationInH<Block, H> = grandpa::voter::CommunicationIn<
	H,
	NumberFor<Block>,
	AuthoritySignature,
	AuthorityId,
>;

/// A global communication sink for commits. Not exposed publicly, used
/// internally to simplify types in the communication layer.
type CommunicationOut<Block> = grandpa::voter::CommunicationOut<
	<Block as BlockT>::Hash,
	NumberFor<Block>,
	AuthoritySignature,
	AuthorityId,
>;

/// Global communication sink for commits with the hash type not being derived
/// from the block, useful for forcing the hash to some type (e.g. `H256`) when
/// the compiler can't do the inference.
type CommunicationOutH<Block, H> = grandpa::voter::CommunicationOut<
	H,
	NumberFor<Block>,
	AuthoritySignature,
	AuthorityId,
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
	/// Whether the GRANDPA observer protocol is live on the network and thereby
	/// a full-node not running as a validator is running the GRANDPA observer
	/// protocol (we will only issue catch-up requests to authorities when the
	/// observer protocol is enabled).
	pub observer_enabled: bool,
	/// Whether the node is running as an authority (i.e. running the full GRANDPA protocol).
	pub is_authority: bool,
	/// Some local identifier of the voter.
	pub name: Option<String>,
	/// The keystore that manages the keys of this node.
	pub keystore: Option<keystore::KeyStorePtr>,
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
	Timer(tokio_timer::Error),
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
pub(crate) trait BlockStatus<Block: BlockT> {
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

/// Something that one can ask to do a block sync request.
pub(crate) trait BlockSyncRequester<Block: BlockT> {
	/// Notifies the sync service to try and sync the given block from the given
	/// peers.
	///
	/// If the given vector of peers is empty then the underlying implementation
	/// should make a best effort to fetch the block from any peers it is
	/// connected to (NOTE: this assumption will change in the future #3629).
	fn set_sync_fork_request(&self, peers: Vec<network::PeerId>, hash: Block::Hash, number: NumberFor<Block>);
}

impl<Block, N> BlockSyncRequester<Block> for NetworkBridge<Block, N> where
	Block: BlockT,
	N: communication::Network<Block>,
{
	fn set_sync_fork_request(&self, peers: Vec<network::PeerId>, hash: Block::Hash, number: NumberFor<Block>) {
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

/// Provider for the Grandpa authority set configured on the genesis block.
pub trait GenesisAuthoritySetProvider<Block: BlockT> {
	/// Get the authority set at the genesis block.
	fn get(&self) -> Result<AuthorityList, ClientError>;
}

impl<B, E, Block: BlockT<Hash=H256>, RA> GenesisAuthoritySetProvider<Block> for Client<B, E, Block, RA>
	where
		B: Backend<Block, Blake2Hasher> + Send + Sync + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		RA: Send + Sync,
{
	fn get(&self) -> Result<AuthorityList, ClientError> {
		// This implementation uses the Grandpa runtime API instead of reading directly from the
		// `GRANDPA_AUTHORITIES_KEY` as the data may have been migrated since the genesis block of
		// the chain, whereas the runtime API is backwards compatible.
		self.executor()
			.call(
				&BlockId::Number(Zero::zero()),
				"GrandpaApi_grandpa_authorities",
				&[],
				ExecutionStrategy::NativeElseWasm,
				None,
			)
			.and_then(|call_result| {
				Decode::decode(&mut &call_result[..])
					.map_err(|err| ClientError::CallResultDecode(
						"failed to decode GRANDPA authorities set proof".into(), err
					))
			})
	}
}

/// Make block importer and link half necessary to tie the background voter
/// to it.
pub fn block_import<B, E, Block: BlockT<Hash=H256>, RA, SC>(
	client: Arc<Client<B, E, Block, RA>>,
	genesis_authorities_provider: &dyn GenesisAuthoritySetProvider<Block>,
	select_chain: SC,
) -> Result<(
		GrandpaBlockImport<B, E, Block, RA, SC>,
		LinkHalf<B, E, Block, RA, SC>
	), ClientError>
where
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
	RA: Send + Sync,
	SC: SelectChain<Block>,
{
	let chain_info = client.info();
	let genesis_hash = chain_info.chain.genesis_hash;

	let persistent_data = aux_schema::load_persistent(
		&*client,
		genesis_hash,
		<NumberFor<Block>>::zero(),
		|| {
			let authorities = genesis_authorities_provider.get()?;
			telemetry!(CONSENSUS_DEBUG; "afg.loading_authorities";
				"authorities_len" => ?authorities.len()
			);
			Ok(authorities)
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
	set_id: SetId,
	voters: &Arc<VoterSet<AuthorityId>>,
	client: &Arc<Client<B, E, Block, RA>>,
	network: &NetworkBridge<Block, N>,
	keystore: &Option<KeyStorePtr>,
) -> (
	impl Stream<
		Item = CommunicationInH<Block, H256>,
		Error = CommandOrError<H256, NumberFor<Block>>,
	>,
	impl Sink<
		SinkItem = CommunicationOutH<Block, H256>,
		SinkError = CommandOrError<H256, NumberFor<Block>>,
	>,
) where
	B: Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync,
	N: Network<Block>,
	RA: Send + Sync,
	NumberFor<Block>: BlockNumberOps,
{
	let is_voter = is_voter(voters, keystore).is_some();

	// verification stream
	let (global_in, global_out) = network.global_communication(
		communication::SetId(set_id),
		voters.clone(),
		is_voter,
	);

	// block commit and catch up messages until relevant blocks are imported.
	let global_in = UntilGlobalMessageBlocksImported::new(
		client.import_notification_stream(),
		network.clone(),
		client.clone(),
		global_in,
		"global",
	);

	let global_in = global_in.map_err(CommandOrError::from);
	let global_out = global_out.sink_map_err(CommandOrError::from);

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
	if !inherent_data_providers.has_provider(&sp_finality_tracker::INHERENT_IDENTIFIER) {
		inherent_data_providers
			.register_provider(sp_finality_tracker::InherentDataProvider::new(move || {
				#[allow(deprecated)]
				{
					let info = client.info().chain;
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
pub struct GrandpaParams<B, E, Block: BlockT<Hash=H256>, N, RA, SC, VR, X> {
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
	pub telemetry_on_connect: Option<mpsc::UnboundedReceiver<()>>,
	/// A voting rule used to potentially restrict target votes.
	pub voting_rule: VR,
}

/// Run a GRANDPA voter as a task. Provide configuration and a link to a
/// block import worker that has already been instantiated with `block_import`.
pub fn run_grandpa_voter<B, E, Block: BlockT<Hash=H256>, N, RA, SC, VR, X>(
	grandpa_params: GrandpaParams<B, E, Block, N, RA, SC, VR, X>,
) -> sp_blockchain::Result<impl Future<Item=(),Error=()> + Send + 'static> where
	Block::Hash: Ord,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
	N: Network<Block> + Send + Sync + 'static,
	N::In: Send + 'static,
	SC: SelectChain<Block> + 'static,
	VR: VotingRule<Block, Client<B, E, Block, RA>> + Clone + 'static,
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
		voting_rule,
	} = grandpa_params;

	let LinkHalf {
		client,
		select_chain,
		persistent_data,
		voter_commands_rx,
	} = link;

	let (network, network_startup) = NetworkBridge::new(
		network,
		config.clone(),
		persistent_data.set_state.clone(),
		on_exit.clone(),
	);

	register_finality_tracker_inherent_data_provider(client.clone(), &inherent_data_providers)?;

	let conf = config.clone();
	let telemetry_task = if let Some(telemetry_on_connect) = telemetry_on_connect {
		let authorities = persistent_data.authority_set.clone();
		let events = telemetry_on_connect
			.for_each(move |_| {
				let curr = authorities.current_authorities();
				let mut auths = curr.voters().into_iter().map(|(p, _)| p);
				let maybe_authority_id = authority_id(&mut auths, &conf.keystore)
					.unwrap_or(Default::default());

				telemetry!(CONSENSUS_INFO; "afg.authority_set";
					"authority_id" => maybe_authority_id.to_string(),
					"authority_set_id" => ?authorities.set_id(),
					"authorities" => {
						let authorities: Vec<String> = curr.voters()
							.iter().map(|(id, _)| id.to_string()).collect();
						serde_json::to_string(&authorities)
							.expect("authorities is always at least an empty vector; elements are always of type string")
					}
				);
				Ok(())
			})
			.then(|_| -> Result<(), ()> { Ok(()) });
		futures::future::Either::A(events)
	} else {
		futures::future::Either::B(futures::future::empty())
	};

	let voter_work = VoterWork::new(
		client,
		config,
		network,
		select_chain,
		voting_rule,
		persistent_data,
		voter_commands_rx,
	);

	let voter_work = voter_work
		.map(|_| ())
		.map_err(|e| {
			error!("GRANDPA Voter failed: {:?}", e);
			telemetry!(CONSENSUS_WARN; "afg.voter_failed"; "e" => ?e);
		});

	let voter_work = network_startup.and_then(move |()| voter_work);

	// Make sure that `telemetry_task` doesn't accidentally finish and kill grandpa.
	let telemetry_task = telemetry_task
		.then(|_| futures::future::empty::<(), ()>());

	Ok(voter_work.select(on_exit).select2(telemetry_task).then(|_| Ok(())))
}

/// Future that powers the voter.
#[must_use]
struct VoterWork<B, E, Block: BlockT, N: Network<Block>, RA, SC, VR> {
	voter: Box<dyn Future<Item = (), Error = CommandOrError<Block::Hash, NumberFor<Block>>> + Send>,
	env: Arc<Environment<B, E, Block, N, RA, SC, VR>>,
	voter_commands_rx: mpsc::UnboundedReceiver<VoterCommand<Block::Hash, NumberFor<Block>>>,
}

impl<B, E, Block, N, RA, SC, VR> VoterWork<B, E, Block, N, RA, SC, VR>
where
	Block: BlockT<Hash=H256>,
	N: Network<Block> + Sync,
	N::In: Send + 'static,
	NumberFor<Block>: BlockNumberOps,
	RA: 'static + Send + Sync,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
	B: Backend<Block, Blake2Hasher> + 'static,
	SC: SelectChain<Block> + 'static,
	VR: VotingRule<Block, Client<B, E, Block, RA>> + Clone + 'static,
{
	fn new(
		client: Arc<Client<B, E, Block, RA>>,
		config: Config,
		network: NetworkBridge<Block, N>,
		select_chain: SC,
		voting_rule: VR,
		persistent_data: PersistentData<Block>,
		voter_commands_rx: mpsc::UnboundedReceiver<VoterCommand<Block::Hash, NumberFor<Block>>>,
	) -> Self {

		let voters = persistent_data.authority_set.current_authorities();
		let env = Arc::new(Environment {
			client,
			select_chain,
			voting_rule,
			voters: Arc::new(voters),
			config,
			network,
			set_id: persistent_data.authority_set.set_id(),
			authority_set: persistent_data.authority_set.clone(),
			consensus_changes: persistent_data.consensus_changes.clone(),
			voter_set_state: persistent_data.set_state.clone(),
		});

		let mut work = VoterWork {
			// `voter` is set to a temporary value and replaced below when
			// calling `rebuild_voter`.
			voter: Box::new(futures::empty()) as Box<_>,
			env,
			voter_commands_rx,
		};
		work.rebuild_voter();
		work
	}

	/// Rebuilds the `self.voter` field using the current authority set
	/// state. This method should be called when we know that the authority set
	/// has changed (e.g. as signalled by a voter command).
	fn rebuild_voter(&mut self) {
		debug!(target: "afg", "{}: Starting new voter with set ID {}", self.env.config.name(), self.env.set_id);

		let authority_id = is_voter(&self.env.voters, &self.env.config.keystore)
			.map(|ap| ap.public())
			.unwrap_or(Default::default());

		telemetry!(CONSENSUS_DEBUG; "afg.starting_new_voter";
			"name" => ?self.env.config.name(),
			"set_id" => ?self.env.set_id,
			"authority_id" => authority_id.to_string(),
		);

		let chain_info = self.env.client.info();
		telemetry!(CONSENSUS_INFO; "afg.authority_set";
			"number" => ?chain_info.chain.finalized_number,
			"hash" => ?chain_info.chain.finalized_hash,
			"authority_id" => authority_id.to_string(),
			"authority_set_id" => ?self.env.set_id,
			"authorities" => {
				let authorities: Vec<String> = self.env.voters.voters()
					.iter().map(|(id, _)| id.to_string()).collect();
				serde_json::to_string(&authorities)
					.expect("authorities is always at least an empty vector; elements are always of type string")
			},
		);

		match &*self.env.voter_set_state.read() {
			VoterSetState::Live { completed_rounds, .. } => {
				let last_finalized = (
					chain_info.chain.finalized_hash,
					chain_info.chain.finalized_number,
				);

				let global_comms = global_communication(
					self.env.set_id,
					&self.env.voters,
					&self.env.client,
					&self.env.network,
					&self.env.config.keystore,
				);

				let last_completed_round = completed_rounds.last();

				let voter = voter::Voter::new(
					self.env.clone(),
					(*self.env.voters).clone(),
					global_comms,
					last_completed_round.number,
					last_completed_round.votes.clone(),
					last_completed_round.base.clone(),
					last_finalized,
				);

				self.voter = Box::new(voter);
			},
			VoterSetState::Paused { .. } =>
				self.voter = Box::new(futures::empty()),
		};
	}

	fn handle_voter_command(
		&mut self,
		command: VoterCommand<Block::Hash, NumberFor<Block>>
	) -> Result<(), Error> {
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

				self.env.update_voter_set_state(|_| {
					// start the new authority set using the block where the
					// set changed (not where the signal happened!) as the base.
					let set_state = VoterSetState::live(
						new.set_id,
						&*self.env.authority_set.inner().read(),
						(new.canon_hash, new.canon_number),
					);

					aux_schema::write_voter_set_state(&*self.env.client, &set_state)?;
					Ok(Some(set_state))
				})?;

				self.env = Arc::new(Environment {
					voters: Arc::new(new.authorities.into_iter().collect()),
					set_id: new.set_id,
					voter_set_state: self.env.voter_set_state.clone(),
					// Fields below are simply transferred and not updated.
					client: self.env.client.clone(),
					select_chain: self.env.select_chain.clone(),
					config: self.env.config.clone(),
					authority_set: self.env.authority_set.clone(),
					consensus_changes: self.env.consensus_changes.clone(),
					network: self.env.network.clone(),
					voting_rule: self.env.voting_rule.clone(),
				});

				self.rebuild_voter();
				Ok(())
			}
			VoterCommand::Pause(reason) => {
				info!(target: "afg", "Pausing old validator set: {}", reason);

				// not racing because old voter is shut down.
				self.env.update_voter_set_state(|voter_set_state| {
					let completed_rounds = voter_set_state.completed_rounds();
					let set_state = VoterSetState::Paused { completed_rounds };

					aux_schema::write_voter_set_state(&*self.env.client, &set_state)?;
					Ok(Some(set_state))
				})?;

				self.rebuild_voter();
				Ok(())
			}
		}
	}
}

impl<B, E, Block, N, RA, SC, VR> Future for VoterWork<B, E, Block, N, RA, SC, VR>
where
	Block: BlockT<Hash=H256>,
	N: Network<Block> + Sync,
	N::In: Send + 'static,
	NumberFor<Block>: BlockNumberOps,
	RA: 'static + Send + Sync,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
	B: Backend<Block, Blake2Hasher> + 'static,
	SC: SelectChain<Block> + 'static,
	VR: VotingRule<Block, Client<B, E, Block, RA>> + Clone + 'static,
{
	type Item = ();
	type Error = Error;

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
		match self.voter.poll() {
			Ok(Async::NotReady) => {}
			Ok(Async::Ready(())) => {
				// voters don't conclude naturally
				return Err(Error::Safety("GRANDPA voter has concluded.".into()))
			}
			Err(CommandOrError::Error(e)) => {
				// return inner observer error
				return Err(e)
			}
			Err(CommandOrError::VoterCommand(command)) => {
				// some command issued internally
				self.handle_voter_command(command)?;
				futures::task::current().notify();
			}
		}

		match self.voter_commands_rx.poll() {
			Ok(Async::NotReady) => {}
			Err(_) => {
				// the `voter_commands_rx` stream should not fail.
				return Ok(Async::Ready(()))
			}
			Ok(Async::Ready(None)) => {
				// the `voter_commands_rx` stream should never conclude since it's never closed.
				return Ok(Async::Ready(()))
			}
			Ok(Async::Ready(Some(command))) => {
				// some command issued externally
				self.handle_voter_command(command)?;
				futures::task::current().notify();
			}
		}

		Ok(Async::NotReady)
	}
}

#[deprecated(since = "1.1.0", note = "Please switch to run_grandpa_voter.")]
pub fn run_grandpa<B, E, Block: BlockT<Hash=H256>, N, RA, SC, VR, X>(
	grandpa_params: GrandpaParams<B, E, Block, N, RA, SC, VR, X>,
) -> ::sp_blockchain::Result<impl Future<Item=(),Error=()> + Send + 'static> where
	Block::Hash: Ord,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
	N: Network<Block> + Send + Sync + 'static,
	N::In: Send + 'static,
	SC: SelectChain<Block> + 'static,
	NumberFor<Block>: BlockNumberOps,
	DigestFor<Block>: Encode,
	RA: Send + Sync + 'static,
	VR: VotingRule<Block, Client<B, E, Block, RA>> + Clone + 'static,
	X: Future<Item=(),Error=()> + Clone + Send + 'static,
{
	run_grandpa_voter(grandpa_params)
}

/// When GRANDPA is not initialized we still need to register the finality
/// tracker inherent provider which might be expected by the runtime for block
/// authoring. Additionally, we register a gossip message validator that
/// discards all GRANDPA messages (otherwise, we end up banning nodes that send
/// us a `Neighbor` message, since there is no registered gossip validator for
/// the engine id defined in the message.)
pub fn setup_disabled_grandpa<B, E, Block: BlockT<Hash=H256>, RA, N>(
	client: Arc<Client<B, E, Block, RA>>,
	inherent_data_providers: &InherentDataProviders,
	network: N,
) -> Result<(), consensus_common::Error> where
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
	RA: Send + Sync + 'static,
	N: Network<Block> + Send + Sync + 'static,
	N::In: Send + 'static,
{
	register_finality_tracker_inherent_data_provider(
		client,
		inherent_data_providers,
	)?;

	network.register_validator(Arc::new(network::consensus_gossip::DiscardAll));

	Ok(())
}

/// Checks if this node is a voter in the given voter set.
///
/// Returns the key pair of the node that is being used in the current voter set or `None`.
fn is_voter(
	voters: &Arc<VoterSet<AuthorityId>>,
	keystore: &Option<KeyStorePtr>,
) -> Option<AuthorityPair> {
	match keystore {
		Some(keystore) => voters.voters().iter()
			.find_map(|(p, _)| keystore.read().key_pair::<AuthorityPair>(&p).ok()),
		None => None,
	}
}

/// Returns the authority id of this node, if available.
fn authority_id<'a, I>(
	authorities: &mut I,
	keystore: &Option<KeyStorePtr>,
) -> Option<AuthorityId> where
	I: Iterator<Item = &'a AuthorityId>,
{
	match keystore {
		Some(keystore) => {
			authorities
				.find_map(|p| {
					keystore.read().key_pair::<AuthorityPair>(&p)
						.ok()
						.map(|ap| ap.public())
				})
		}
		None => None,
	}
}
