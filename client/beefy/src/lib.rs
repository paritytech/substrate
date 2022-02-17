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

use std::sync::Arc;

use log::debug;
use prometheus::Registry;

use sc_client_api::{Backend, BlockchainEvents, Finalizer};
use sc_network_gossip::{GossipEngine, Network as GossipNetwork};

use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_keystore::SyncCryptoStorePtr;
use sp_runtime::traits::Block;

use beefy_primitives::BeefyApi;

use crate::notification::{BeefyBestBlockSender, BeefySignedCommitmentSender};

mod error;
mod gossip;
mod keystore;
mod metrics;
mod round;
mod worker;

pub mod notification;
pub use beefy_protocol_name::standard_name as protocol_standard_name;

pub(crate) mod beefy_protocol_name {
	use sc_chain_spec::ChainSpec;

	const NAME: &'static str = "/beefy/1";
	/// Old names for the notifications protocol, used for backward compatibility.
	pub(crate) const LEGACY_NAMES: [&'static str; 1] = ["/paritytech/beefy/1"];

	/// Name of the notifications protocol used by BEEFY.
	///
	/// Must be registered towards the networking in order for BEEFY to properly function.
	pub fn standard_name<Hash: std::fmt::Display>(
		genesis_hash: &Hash,
		chain_spec: &Box<dyn ChainSpec>,
	) -> std::borrow::Cow<'static, str> {
		let chain_prefix = match chain_spec.fork_id() {
			Some(fork_id) => format!("/{}/{}", genesis_hash, fork_id),
			None => format!("/{}", genesis_hash),
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
	BlockchainEvents<B> + HeaderBackend<B> + Finalizer<B, BE> + ProvideRuntimeApi<B> + Send + Sync
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

/// BEEFY gadget initialization parameters.
pub struct BeefyParams<B, BE, C, N>
where
	B: Block,
	BE: Backend<B>,
	C: Client<B, BE>,
	C::Api: BeefyApi<B>,
	N: GossipNetwork<B> + Clone + Send + 'static,
{
	/// BEEFY client
	pub client: Arc<C>,
	/// Client Backend
	pub backend: Arc<BE>,
	/// Local key store
	pub key_store: Option<SyncCryptoStorePtr>,
	/// Gossip network
	pub network: N,
	/// BEEFY signed commitment sender
	pub signed_commitment_sender: BeefySignedCommitmentSender<B>,
	/// BEEFY best block sender
	pub beefy_best_block_sender: BeefyBestBlockSender<B>,
	/// Minimal delta between blocks, BEEFY should vote for
	pub min_block_delta: u32,
	/// Prometheus metric registry
	pub prometheus_registry: Option<Registry>,
	/// Chain specific GRANDPA protocol name. See [`beefy_protocol_name::standard_name`].
	pub protocol_name: std::borrow::Cow<'static, str>,
}

/// Start the BEEFY gadget.
///
/// This is a thin shim around running and awaiting a BEEFY worker.
pub async fn start_beefy_gadget<B, BE, C, N>(beefy_params: BeefyParams<B, BE, C, N>)
where
	B: Block,
	BE: Backend<B>,
	C: Client<B, BE>,
	C::Api: BeefyApi<B>,
	N: GossipNetwork<B> + Clone + Send + 'static,
{
	let BeefyParams {
		client,
		backend,
		key_store,
		network,
		signed_commitment_sender,
		beefy_best_block_sender,
		min_block_delta,
		prometheus_registry,
		protocol_name,
	} = beefy_params;

	let gossip_validator = Arc::new(gossip::GossipValidator::new());
	let gossip_engine = GossipEngine::new(network, protocol_name, gossip_validator.clone(), None);

	let metrics =
		prometheus_registry.as_ref().map(metrics::Metrics::register).and_then(
			|result| match result {
				Ok(metrics) => {
					debug!(target: "beefy", "🥩 Registered metrics");
					Some(metrics)
				},
				Err(err) => {
					debug!(target: "beefy", "🥩 Failed to register metrics: {:?}", err);
					None
				},
			},
		);

	let worker_params = worker::WorkerParams {
		client,
		backend,
		key_store: key_store.into(),
		signed_commitment_sender,
		beefy_best_block_sender,
		gossip_engine,
		gossip_validator,
		min_block_delta,
		metrics,
	};

	let worker = worker::BeefyWorker::<_, _, _>::new(worker_params);

	worker.run().await
}
