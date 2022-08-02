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

use beefy_primitives::{BeefyApi, MmrRootHash};
use prometheus::Registry;
use sc_client_api::{Backend, BlockchainEvents, Finalizer};
use sc_consensus::BlockImport;
use sc_network_gossip::Network as GossipNetwork;
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_consensus::{Error as ConsensusError, SyncOracle};
use sp_keystore::SyncCryptoStorePtr;
use sp_mmr_primitives::MmrApi;
use sp_runtime::traits::Block;
use std::sync::Arc;

mod error;
mod gossip;
mod keystore;
mod metrics;
mod round;
mod worker;

pub mod import;
pub mod justification;
pub mod notification;

#[cfg(test)]
mod tests;

use crate::{
	import::BeefyBlockImport,
	notification::{
		BeefyBestBlockSender, BeefyBestBlockStream, BeefySignedCommitmentSender,
		BeefySignedCommitmentStream,
	},
};

pub use beefy_protocol_name::standard_name as protocol_standard_name;

pub(crate) mod beefy_protocol_name {
	use sc_chain_spec::ChainSpec;

	const NAME: &str = "/beefy/1";
	/// Old names for the notifications protocol, used for backward compatibility.
	pub(crate) const LEGACY_NAMES: [&str; 1] = ["/paritytech/beefy/1"];

	/// Name of the notifications protocol used by BEEFY.
	///
	/// Must be registered towards the networking in order for BEEFY to properly function.
	pub fn standard_name<Hash: AsRef<[u8]>>(
		genesis_hash: &Hash,
		chain_spec: &Box<dyn ChainSpec>,
	) -> std::borrow::Cow<'static, str> {
		let chain_prefix = match chain_spec.fork_id() {
			Some(fork_id) => format!("/{}/{}", hex::encode(genesis_hash), fork_id),
			None => format!("/{}", hex::encode(genesis_hash)),
		};
		format!("{}{}", chain_prefix, NAME).into()
	}
}

/// Returns the configuration value to put in
/// [`sc_network::config::NetworkConfiguration::extra_sets`].
/// For standard protocol name see [`beefy_protocol_name::standard_name`].
pub fn beefy_peers_set_config(
	protocol_name: std::borrow::Cow<'static, str>,
) -> sc_network::config::NonDefaultSetConfig {
	let mut cfg = sc_network::config::NonDefaultSetConfig::new(protocol_name, 1024 * 1024);

	cfg.allow_non_reserved(25, 25);
	cfg.add_fallback_names(beefy_protocol_name::LEGACY_NAMES.iter().map(|&n| n.into()).collect());
	cfg
}

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
	pub from_block_import_justif_stream: BeefySignedCommitmentStream<B>,

	// Voter -> RPC links
	/// Sends BEEFY signed commitments from voter to RPC.
	pub to_rpc_justif_sender: BeefySignedCommitmentSender<B>,
	/// Sends BEEFY best block hashes from voter to RPC.
	pub to_rpc_best_block_sender: BeefyBestBlockSender<B>,
}

/// Links used by the BEEFY RPC layer, from the BEEFY background voter.
#[derive(Clone)]
pub struct BeefyRPCLinks<B: Block> {
	/// Stream of signed commitments coming from the voter.
	pub from_voter_justif_stream: BeefySignedCommitmentStream<B>,
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
		notification::BeefySignedCommitmentStream::<B>::channel();
	let (to_rpc_best_block_sender, from_voter_best_beefy_stream) =
		notification::BeefyBestBlockStream::<B>::channel();

	// BlockImport -> Voter links
	let (to_voter_justif_sender, from_block_import_justif_stream) =
		notification::BeefySignedCommitmentStream::<B>::channel();

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

/// BEEFY gadget initialization parameters.
pub struct BeefyParams<B, BE, C, N, R>
where
	B: Block,
	BE: Backend<B>,
	C: Client<B, BE>,
	R: ProvideRuntimeApi<B>,
	R::Api: BeefyApi<B> + MmrApi<B, MmrRootHash>,
	N: GossipNetwork<B> + Clone + SyncOracle + Send + Sync + 'static,
{
	/// BEEFY client
	pub client: Arc<C>,
	/// Client Backend
	pub backend: Arc<BE>,
	/// Runtime Api Provider
	pub runtime: Arc<R>,
	/// Local key store
	pub key_store: Option<SyncCryptoStorePtr>,
	/// Gossip network
	pub network: N,
	/// Minimal delta between blocks, BEEFY should vote for
	pub min_block_delta: u32,
	/// Prometheus metric registry
	pub prometheus_registry: Option<Registry>,
	/// Chain specific GRANDPA protocol name. See [`beefy_protocol_name::standard_name`].
	pub protocol_name: std::borrow::Cow<'static, str>,
	/// Links between the block importer, the background voter and the RPC layer.
	pub links: BeefyVoterLinks<B>,
}

/// Start the BEEFY gadget.
///
/// This is a thin shim around running and awaiting a BEEFY worker.
pub async fn start_beefy_gadget<B, BE, C, N, R>(beefy_params: BeefyParams<B, BE, C, N, R>)
where
	B: Block,
	BE: Backend<B>,
	C: Client<B, BE>,
	R: ProvideRuntimeApi<B>,
	R::Api: BeefyApi<B> + MmrApi<B, MmrRootHash>,
	N: GossipNetwork<B> + Clone + SyncOracle + Send + Sync + 'static,
{
	let BeefyParams {
		client,
		backend,
		runtime,
		key_store,
		network,
		min_block_delta,
		prometheus_registry,
		protocol_name,
		links,
	} = beefy_params;

	let sync_oracle = network.clone();
	let gossip_validator = Arc::new(gossip::GossipValidator::new());
	let gossip_engine = sc_network_gossip::GossipEngine::new(
		network,
		protocol_name,
		gossip_validator.clone(),
		None,
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
		runtime,
		sync_oracle,
		key_store: key_store.into(),
		gossip_engine,
		gossip_validator,
		links,
		metrics,
		min_block_delta,
	};

	let worker = worker::BeefyWorker::<_, _, _, _, _>::new(worker_params);

	worker.run().await
}
