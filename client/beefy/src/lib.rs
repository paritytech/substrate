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

use beefy_primitives::{BeefyApi, MmrRootHash, PayloadProvider};
use parking_lot::Mutex;
use prometheus::Registry;
use sc_client_api::{Backend, BlockBackend, BlockchainEvents, Finalizer};
use sc_consensus::BlockImport;
use sc_network::ProtocolName;
use sc_network_common::service::NetworkRequest;
use sc_network_gossip::Network as GossipNetwork;
use sp_api::{NumberFor, ProvideRuntimeApi};
use sp_blockchain::HeaderBackend;
use sp_consensus::{Error as ConsensusError, SyncOracle};
use sp_keystore::SyncCryptoStorePtr;
use sp_mmr_primitives::MmrApi;
use sp_runtime::traits::Block;
use std::{marker::PhantomData, sync::Arc};

mod error;
mod keystore;
mod metrics;
mod round;
mod worker;

pub mod communication;
pub mod import;
pub mod justification;

#[cfg(test)]
mod tests;

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
};

pub use communication::beefy_protocol_name::{
	gossip_protocol_name, justifications_protocol_name as justifs_protocol_name,
};

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
pub struct BeefyVoterLinks<B: Block> {
	// BlockImport -> Voter links
	/// Stream of BEEFY signed commitments from block import to voter.
	pub from_block_import_justif_stream: BeefyVersionedFinalityProofStream<B>,

	// Voter -> RPC links
	/// Sends BEEFY signed commitments from voter to RPC.
	pub to_rpc_justif_sender: BeefyVersionedFinalityProofSender<B>,
	/// Sends BEEFY best block hashes from voter to RPC.
	pub to_rpc_best_block_sender: BeefyBestBlockSender<B>,
}

/// Links used by the BEEFY RPC layer, from the BEEFY background voter.
#[derive(Clone)]
pub struct BeefyRPCLinks<B: Block> {
	/// Stream of signed commitments coming from the voter.
	pub from_voter_justif_stream: BeefyVersionedFinalityProofStream<B>,
	/// Stream of BEEFY best block hashes coming from the voter.
	pub from_voter_best_beefy_stream: BeefyBestBlockStream<B>,
}

/// Make block importer and link half necessary to tie the background voter to it.
pub fn beefy_block_import_and_links<B, BE, RuntimeApi, I>(
	wrapped_block_import: I,
	backend: Arc<BE>,
	runtime: Arc<RuntimeApi>,
) -> (BeefyBlockImport<B, BE, RuntimeApi, I>, BeefyVoterLinks<B>, BeefyRPCLinks<B>)
where
	B: Block,
	BE: Backend<B>,
	I: BlockImport<B, Error = ConsensusError, Transaction = sp_api::TransactionFor<RuntimeApi, B>>
		+ Send
		+ Sync,
	RuntimeApi: ProvideRuntimeApi<B> + Send + Sync,
	RuntimeApi::Api: BeefyApi<B>,
{
	// Voter -> RPC links
	let (to_rpc_justif_sender, from_voter_justif_stream) =
		BeefyVersionedFinalityProofStream::<B>::channel();
	let (to_rpc_best_block_sender, from_voter_best_beefy_stream) =
		BeefyBestBlockStream::<B>::channel();

	// BlockImport -> Voter links
	let (to_voter_justif_sender, from_block_import_justif_stream) =
		BeefyVersionedFinalityProofStream::<B>::channel();

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
pub struct BeefyParams<B: Block, BE, C, N, P, R> {
	/// BEEFY client
	pub client: Arc<C>,
	/// Client Backend
	pub backend: Arc<BE>,
	/// BEEFY Payload provider
	pub payload_provider: P,
	/// Runtime Api Provider
	pub runtime: Arc<R>,
	/// Local key store
	pub key_store: Option<SyncCryptoStorePtr>,
	/// BEEFY voter network params
	pub network_params: BeefyNetworkParams<B, N>,
	/// Minimal delta between blocks, BEEFY should vote for
	pub min_block_delta: u32,
	/// Prometheus metric registry
	pub prometheus_registry: Option<Registry>,
	/// Links between the block importer, the background voter and the RPC layer.
	pub links: BeefyVoterLinks<B>,
	/// Handler for incoming BEEFY justifications requests from a remote peer.
	pub on_demand_justifications_handler: BeefyJustifsRequestHandler<B, C>,
}

/// Start the BEEFY gadget.
///
/// This is a thin shim around running and awaiting a BEEFY worker.
pub async fn start_beefy_gadget<B, BE, C, N, P, R>(beefy_params: BeefyParams<B, BE, C, N, P, R>)
where
	B: Block,
	BE: Backend<B>,
	C: Client<B, BE> + BlockBackend<B>,
	P: PayloadProvider<B>,
	R: ProvideRuntimeApi<B>,
	R::Api: BeefyApi<B> + MmrApi<B, MmrRootHash, NumberFor<B>>,
	N: GossipNetwork<B> + NetworkRequest + SyncOracle + Send + Sync + 'static,
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
	} = beefy_params;

	let BeefyNetworkParams { network, gossip_protocol_name, justifications_protocol_name, .. } =
		network_params;

	let known_peers = Arc::new(Mutex::new(KnownPeers::new()));
	let gossip_validator =
		Arc::new(communication::gossip::GossipValidator::new(known_peers.clone()));
	let gossip_engine = sc_network_gossip::GossipEngine::new(
		network.clone(),
		gossip_protocol_name,
		gossip_validator.clone(),
		None,
	);

	let on_demand_justifications = OnDemandJustificationsEngine::new(
		network.clone(),
		runtime.clone(),
		justifications_protocol_name,
		known_peers.clone(),
	);

	let metrics =
		prometheus_registry.as_ref().map(metrics::Metrics::register).and_then(
			|result| match result {
				Ok(metrics) => {
					log::debug!(target: "beefy", "🥩 Registered metrics");
					Some(metrics)
				},
				Err(err) => {
					log::debug!(target: "beefy", "🥩 Failed to register metrics: {:?}", err);
					None
				},
			},
		);

	let worker_params = worker::WorkerParams {
		client,
		backend,
		payload_provider,
		runtime,
		network,
		key_store: key_store.into(),
		known_peers,
		gossip_engine,
		gossip_validator,
		on_demand_justifications,
		links,
		metrics,
		min_block_delta,
	};

	let worker = worker::BeefyWorker::<_, _, _, _, _, _>::new(worker_params);

	futures::future::join(worker.run(), on_demand_justifications_handler.run()).await;
}
