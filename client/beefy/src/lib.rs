// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

use core::fmt::Debug;
use codec::{Codec, Decode, Encode};

use crate::{
	communication::{
		notification::{
			BeefyBestBlockSender, BeefyBestBlockStream, BeefyVersionedFinalityProofSender,
			BeefyVersionedFinalityProofStream,
		},
		peers::KnownPeers,
		request_response::{
			outgoing_requests_engine::OnDemandJustificationsEngine, BeefyJustifsRequestHandler,
		},
	},
	import::BeefyBlockImport,
	keystore::BeefyKeystore,
	round::Rounds,
	worker::PersistedState,
};
use beefy_primitives::{
	ecdsa_crypto::AuthorityId, BeefyApi, MmrRootHash, PayloadProvider, ValidatorSet, BEEFY_ENGINE_ID,
	GENESIS_AUTHORITY_SET_ID,
};
use futures::{stream::Fuse, StreamExt};
use log::{debug, error, info};
use parking_lot::Mutex;
use prometheus::Registry;
use sc_client_api::{Backend, BlockBackend, BlockchainEvents, FinalityNotifications, Finalizer};
use sc_consensus::BlockImport;
use sc_network::ProtocolName;
use sc_network_common::service::NetworkRequest;
use sc_network_gossip::{GossipEngine, Network as GossipNetwork};
use sp_api::{HeaderT, NumberFor, ProvideRuntimeApi};
use sp_blockchain::{
	Backend as BlockchainBackend, Error as ClientError, HeaderBackend, Result as ClientResult,
};
use sp_consensus::{Error as ConsensusError, SyncOracle};
use sp_keystore::SyncCryptoStorePtr;
use sp_mmr_primitives::MmrApi;
use sp_runtime::{
	generic::BlockId,
	traits::{Block, One, Zero},
};
use std::{collections::VecDeque, marker::PhantomData, sync::Arc};

mod aux_schema;
mod error;
mod keystore;
mod metrics;
mod round;
mod worker;

pub mod communication;
pub mod import;
pub mod justification;

pub use communication::beefy_protocol_name::{
	gossip_protocol_name, justifications_protocol_name as justifs_protocol_name,
};

#[cfg(test)]
mod tests;

const LOG_TARGET: &str = "beefy";

/// A convenience BEEFY client trait that defines all the type bounds a BEEFY client
/// has to satisfy. Ideally that should actually be a trait alias. Unfortunately as
/// of today, Rust does not allow a type alias to be used as a trait bound. Tracking
/// issue is <https://github.com/rust-lang/rust/issues/41517>.
pub trait Client<B, BE>:
	BlockchainEvents<B> + HeaderBackend<B> + Finalizer<B, BE> + Send + Sync
where
	B: Block,
	BE: Backend<B>,
{
	// empty
}

impl<B, BE, T> Client<B, BE> for T
where
	B: Block,
	BE: Backend<B>,
	T: BlockchainEvents<B>
		+ HeaderBackend<B>
		+ Finalizer<B, BE>
		+ ProvideRuntimeApi<B>
		+ Send
		+ Sync,
{
	// empty
}

/// Links between the block importer, the background voter and the RPC layer,
/// to be used by the voter.
#[derive(Clone)]
pub struct BeefyVoterLinks<B: Block, TSignature: Encode + Decode + Debug + Clone + Sync + Send,> {
	// BlockImport -> Voter links
	/// Stream of BEEFY signed commitments from block import to voter.
	pub from_block_import_justif_stream: BeefyVersionedFinalityProofStream<B, TSignature>,

	// Voter -> RPC links
	/// Sends BEEFY signed commitments from voter to RPC.
	pub to_rpc_justif_sender: BeefyVersionedFinalityProofSender<B, TSignature>,
	/// Sends BEEFY best block hashes from voter to RPC.
	pub to_rpc_best_block_sender: BeefyBestBlockSender<B>,
}

/// Links used by the BEEFY RPC layer, from the BEEFY background voter.
#[derive(Clone)]
pub struct BeefyRPCLinks<B: Block, TSignature: Encode + Decode + Debug + Clone + Sync + Send> {
	/// Stream of signed commitments coming from the voter.
	pub from_voter_justif_stream: BeefyVersionedFinalityProofStream<B, TSignature>,
	/// Stream of BEEFY best block hashes coming from the voter.
	pub from_voter_best_beefy_stream: BeefyBestBlockStream<B>,
}

/// Make block importer and link half necessary to tie the background voter to it.
pub fn beefy_block_import_and_links<B, BE, RuntimeApi, I, AuthId, TSignature, BKS>(
	wrapped_block_import: I,
	backend: Arc<BE>,
	runtime: Arc<RuntimeApi>,	
) -> (BeefyBlockImport<B, BE, RuntimeApi, I, AuthId, TSignature, BKS>, BeefyVoterLinks<B, TSignature>, BeefyRPCLinks<B, TSignature>)
where
	B: Block,
	BE: Backend<B>,
	I: BlockImport<B, Error = ConsensusError, Transaction = sp_api::TransactionFor<RuntimeApi, B>>
		+ Send
		+ Sync,
	RuntimeApi: ProvideRuntimeApi<B> + Send + Sync,
	RuntimeApi::Api: BeefyApi<B, AuthId>,
        AuthId: Encode + Decode + Debug + Clone + Ord + Sync + Send,
	TSignature: Encode + Decode + Debug + Clone + Sync + Send,
	BKS: BeefyKeystore<AuthId, TSignature, Public = AuthId>,
{
	// Voter -> RPC links
	let (to_rpc_justif_sender, from_voter_justif_stream) =
		BeefyVersionedFinalityProofStream::<B, TSignature>::channel();
	let (to_rpc_best_block_sender, from_voter_best_beefy_stream) =
		BeefyBestBlockStream::<B>::channel();

	// BlockImport -> Voter links
	let (to_voter_justif_sender, from_block_import_justif_stream) =
		BeefyVersionedFinalityProofStream::<B, TSignature>::channel();

	// BlockImport
	let import =
		BeefyBlockImport::new(backend, runtime, wrapped_block_import, to_voter_justif_sender);
	let voter_links = BeefyVoterLinks {
		from_block_import_justif_stream,
		to_rpc_justif_sender,
		to_rpc_best_block_sender,
	};
	let rpc_links = BeefyRPCLinks { from_voter_best_beefy_stream, from_voter_justif_stream };

	(import, voter_links, rpc_links)
}

/// BEEFY gadget network parameters.
pub struct BeefyNetworkParams<B: Block, N> {
	/// Network implementing gossip, requests and sync-oracle.
	pub network: Arc<N>,
	/// Chain specific BEEFY gossip protocol name. See
	/// [`communication::beefy_protocol_name::gossip_protocol_name`].
	pub gossip_protocol_name: ProtocolName,
	/// Chain specific BEEFY on-demand justifications protocol name. See
	/// [`communication::beefy_protocol_name::justifications_protocol_name`].
	pub justifications_protocol_name: ProtocolName,

	pub _phantom: PhantomData<B>,
}

/// BEEFY gadget initialization parameters.
pub struct BeefyParams<B, BE, C, N, P, R, AuthId, TSignature, BKS>
where
	B: Block,
	BE: Backend<B>,
	C: Client<B, BE>,
	R: ProvideRuntimeApi<B>,        
	BKS: keystore::BeefyKeystore<AuthId, TSignature, Public = AuthId>,
	AuthId: Encode + Decode + Debug + Clone + Ord + Sync + Send,
	TSignature: Encode + Decode + Debug + Clone + Sync + Send, 
	R::Api: BeefyApi<B, AuthId> + MmrApi<B, MmrRootHash, NumberFor<B>>,
	N: GossipNetwork<B> + NetworkRequest +  SyncOracle + Send + Sync + 'static,
{
	/// BEEFY client
	pub client: Arc<C>,
	/// Client Backend
	pub backend: Arc<BE>,
	/// BEEFY Payload provider
	pub payload_provider: P,
	/// Runtime Api Provider
	pub runtime: Arc<R>,
	/// Local key store
	pub key_store: BKS,
	pub network_params: BeefyNetworkParams<B, N>,
	/// Minimal delta between blocks, BEEFY should vote for
	pub min_block_delta: u32,
	/// Prometheus metric registry
	pub prometheus_registry: Option<Registry>,
	/// Links between the block importer, the background voter and the RPC layer.
	pub links: BeefyVoterLinks<B, TSignature>,
	/// Handler for incoming BEEFY justifications requests from a remote peer.
	pub on_demand_justifications_handler: BeefyJustifsRequestHandler<B, C>,
	pub _auth_id : PhantomData::<AuthId>,
	pub _signature: PhantomData::<TSignature>,
}

/// Start the BEEFY gadget.
///
/// This is a thin shim around running and awaiting a BEEFY worker.
pub async fn start_beefy_gadget<B, BE, C, N, P, R, AuthId, TSignature, BKS>(beefy_params: BeefyParams<B, BE, C, N, P, R, AuthId, TSignature, BKS>)
where
	B: Block,
	BE: Backend<B>,
	C: Client<B, BE> + BlockBackend<B>,
	P: PayloadProvider<B>,
	R: ProvideRuntimeApi<B>,
	R::Api: BeefyApi<B, AuthId> + MmrApi<B, MmrRootHash, NumberFor<B>>,
	N: GossipNetwork<B> + NetworkRequest +  SyncOracle + Send + Sync + 'static,
        BKS: keystore::BeefyKeystore<AuthId, TSignature, Public = AuthId> +'static,

	AuthId: Encode + Decode + Debug + Clone + Ord + std::hash::Hash + Sync + Send + 'static,
	TSignature: Encode + Decode + Debug + Clone + Sync + Send + 'static,
{
	let BeefyParams {
		client,
		backend,
		payload_provider,
		runtime,
		key_store,
		network_params,
		min_block_delta,
		prometheus_registry,
		links,
		on_demand_justifications_handler,
		_auth_id,
		_signature,
	} = beefy_params;

	let BeefyNetworkParams { network, gossip_protocol_name, justifications_protocol_name, .. } =
		network_params;

	let known_peers = Arc::new(Mutex::new(KnownPeers::new()));
	let gossip_validator =
		Arc::new(communication::gossip::GossipValidator::new(known_peers.clone()));
	let mut gossip_engine = sc_network_gossip::GossipEngine::new(
		network.clone(),
		gossip_protocol_name,
		gossip_validator.clone(),
		None,
	);

	// The `GossipValidator` adds and removes known peers based on valid votes and network events.
	let on_demand_justifications = OnDemandJustificationsEngine::new(
		network.clone(),
		justifications_protocol_name,
		known_peers,
	);

	let metrics =
		prometheus_registry.as_ref().map(metrics::Metrics::register).and_then(
			|result| match result {
				Ok(metrics) => {
					debug!(target: LOG_TARGET, "🥩 Registered metrics");
					Some(metrics)
				},
				Err(err) => {
					debug!(target: LOG_TARGET, "🥩 Failed to register metrics: {:?}", err);
					None
				},
			},
		);

	// Subscribe to finality notifications and justifications before waiting for runtime pallet and
	// reuse the streams, so we don't miss notifications while waiting for pallet to be available.
	let mut finality_notifications = client.finality_notification_stream().fuse();
	let block_import_justif = links.from_block_import_justif_stream.subscribe(100_000).fuse();

	// Wait for BEEFY pallet to be active before starting voter.
	let persisted_state =
		match wait_for_runtime_pallet(&*runtime, &mut gossip_engine, &mut finality_notifications)
			.await
			.and_then(|best_grandpa| {
				load_or_init_voter_state(&*backend, &*runtime, best_grandpa, min_block_delta)
			}) {
			Ok(state) => state,
			Err(e) => {
				error!(target: LOG_TARGET, "Error: {:?}. Terminating.", e);
				return
			},
		};

	let worker_params = worker::WorkerParams {
		backend,
		payload_provider,
		network,
		key_store: key_store,
		gossip_engine,
		gossip_validator,
		on_demand_justifications,
		links,
		metrics,
		persisted_state,
	};

	let worker = worker::BeefyWorker::<_, _, _, _, _, _, _>::new(worker_params);

	futures::future::join(
		worker.run(block_import_justif, finality_notifications),
		on_demand_justifications_handler.run(),
	)
	.await;
}

fn load_or_init_voter_state<B, BE, R, AuthId, TSignature>(
	backend: &BE,
	runtime: &R,
	best_grandpa: <B as Block>::Header,
    min_block_delta: u32,
) -> ClientResult<PersistedState<B, AuthId, TSignature>>
where
	B: Block,
	BE: Backend<B>,
	R: ProvideRuntimeApi<B>,
    AuthId: Encode + Decode + Debug + Clone + Ord + Sync + Send + std::hash::Hash,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send,
	R::Api: BeefyApi<B, AuthId>,
{
	// Initialize voter state from AUX DB or from pallet genesis.
	if let Some(mut state) = crate::aux_schema::load_persistent(backend)? {
		// Overwrite persisted state with current best GRANDPA block.
		state.set_best_grandpa(best_grandpa);
		// Overwrite persisted data with newly provided `min_block_delta`.
		state.set_min_block_delta(min_block_delta);
		info!(target: LOG_TARGET, "🥩 Loading BEEFY voter state from db: {:?}.", state);
		Ok(state)
	} else {
		initialize_voter_state(backend, runtime, best_grandpa, min_block_delta)
	}
}

// If no persisted state present, walk back the chain from first GRANDPA notification to either:
//  - latest BEEFY finalized block, or if none found on the way,
//  - BEEFY pallet genesis;
// Enqueue any BEEFY mandatory blocks (session boundaries) found on the way, for voter to finalize.
fn initialize_voter_state<B, BE, R, AuthId, TSignature>(
	backend: &BE,
	runtime: &R,
	best_grandpa: <B as Block>::Header,
	min_block_delta: u32,
) -> ClientResult<PersistedState<B, AuthId, TSignature>>
where
	B: Block,
	BE: Backend<B>,
    R: ProvideRuntimeApi<B>,
    AuthId: Encode + Decode + Debug + Clone + Ord + Sync + Send + std::hash::Hash,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send,
	R::Api: BeefyApi<B, AuthId>,
{
	// Walk back the imported blocks and initialize voter either, at the last block with
	// a BEEFY justification, or at pallet genesis block; voter will resume from there.
	let blockchain = backend.blockchain();
	let mut sessions = VecDeque::new();
	let mut header = best_grandpa.clone();
	let state = loop {
		if let Some(true) = blockchain
			.justifications(header.hash())
			.ok()
			.flatten()
			.map(|justifs| justifs.get(BEEFY_ENGINE_ID).is_some())
		{
			info!(
				target: LOG_TARGET,
				"🥩 Initialize BEEFY voter at last BEEFY finalized block: {:?}.",
				*header.number()
			);
			let best_beefy = *header.number();
			// If no session boundaries detected so far, just initialize new rounds here.
			if sessions.is_empty() {
				let active_set = expect_validator_set(runtime, BlockId::hash(header.hash()))?;
				let mut rounds = Rounds::new(best_beefy, active_set);
				// Mark the round as already finalized.
				rounds.conclude(best_beefy);
				sessions.push_front(rounds);
			}
			let state =
				PersistedState::checked_new(best_grandpa, best_beefy, sessions, min_block_delta)
					.ok_or_else(|| ClientError::Backend("Invalid BEEFY chain".into()))?;
			break state
		}

		if *header.number() == One::one() {
			// We've reached chain genesis, initialize voter here.
			let genesis_num = *header.number();
			let genesis_set = expect_validator_set(runtime, BlockId::hash(header.hash()))
				.and_then(genesis_set_sanity_check)?;
			info!(
				target: LOG_TARGET,
				"🥩 Loading BEEFY voter state from genesis on what appears to be first startup. \
				Starting voting rounds at block {:?}, genesis validator set {:?}.",
				genesis_num,
				genesis_set,
			);

			sessions.push_front(Rounds::new(genesis_num, genesis_set));
			break PersistedState::checked_new(best_grandpa, Zero::zero(), sessions, min_block_delta)
				.ok_or_else(|| ClientError::Backend("Invalid BEEFY chain".into()))?
		}

		if let Some(active) = worker::find_authorities_change::<B, AuthId>(&header) {
			info!(
				target: LOG_TARGET,
				"🥩 Marking block {:?} as BEEFY Mandatory.",
				*header.number()
			);
			sessions.push_front(Rounds::new(*header.number(), active));
		}

		// Check if state is still available if we move up the chain.
		let parent_hash = *header.parent_hash();
		runtime
			.runtime_api()
			.validator_set(&BlockId::hash(parent_hash))
			.ok()
			.flatten()
			.ok_or_else(|| {
				let msg = format!("{}. Could not initialize BEEFY voter.", parent_hash);
				error!(target: LOG_TARGET, "🥩 {}", msg);
				ClientError::Consensus(sp_consensus::Error::StateUnavailable(msg))
			})?;

		// Move up the chain.
		header = blockchain.expect_header(parent_hash)?;
	};

	aux_schema::write_current_version(backend)?;
	aux_schema::write_voter_state(backend, &state)?;
	Ok(state)
}

/// Wait for BEEFY runtime pallet to be available, return active validator set.
/// Should be called only once during worker initialization.
async fn wait_for_runtime_pallet<B, R, AuthId,>(
	runtime: &R,
	mut gossip_engine: &mut GossipEngine<B>,
	finality: &mut Fuse<FinalityNotifications<B>>,
) -> ClientResult<<B as Block>::Header>
where
	B: Block,
	R: ProvideRuntimeApi<B>,
    AuthId: Encode + Decode + Debug + Clone + Ord + Sync + Send + std::hash::Hash,
    R::Api: BeefyApi<B, AuthId>,
{
	info!(target: LOG_TARGET, "🥩 BEEFY gadget waiting for BEEFY pallet to become available...");
	loop {
		futures::select! {
			notif = finality.next() => {
				let notif = match notif {
					Some(notif) => notif,
					None => break
				};
				let at = BlockId::hash(notif.header.hash());
				if let Some(active) = runtime.runtime_api().validator_set(&at).ok().flatten() {
					// Beefy pallet available, return best grandpa at the time.
					info!(
						target: LOG_TARGET, "🥩 BEEFY pallet available: block {:?} validator set {:?}",
						notif.header.number(), active
					);
					return Ok(notif.header)
				}
			},
			_ = gossip_engine => {
				break
			}
		}
	}
	let err_msg = "🥩 Gossip engine has unexpectedly terminated.".into();
	error!(target: LOG_TARGET, "{}", err_msg);
	Err(ClientError::Backend(err_msg))
}

fn genesis_set_sanity_check<AuthId: Encode + Decode + Debug + Clone + Ord + Sync + Send + std::hash::Hash>(
	active: ValidatorSet<AuthId>,
) -> ClientResult<ValidatorSet<AuthId>> {
	if active.id() == GENESIS_AUTHORITY_SET_ID {
		Ok(active)
	} else {
		error!(target: LOG_TARGET, "🥩 Unexpected ID for genesis validator set {:?}.", active);
		Err(ClientError::Backend("BEEFY Genesis sanity check failed.".into()))
	}
}

fn expect_validator_set<B, R, AuthId>(
	runtime: &R,
	at: BlockId<B>,
) -> ClientResult<ValidatorSet<AuthId>>
where
    B: Block,
    R: ProvideRuntimeApi<B>,
    AuthId: Encode + Decode + Debug + Clone + Ord + Sync + Send + std::hash::Hash,
    R::Api: BeefyApi<B, AuthId>,
{
	runtime
		.runtime_api()
		.validator_set(&at)
		.ok()
		.flatten()
		.ok_or_else(|| ClientError::Backend("BEEFY pallet expected to be active.".into()))
}
