// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use std::{convert::TryFrom, fmt::Debug, sync::Arc};

use beefy_primitives::BeefyApi;
use codec::Codec;
use log::debug;
use prometheus::Registry;

use sc_client_api::{Backend, BlockchainEvents, Finalizer};
use sc_network_gossip::{
	GossipEngine, Network as GossipNetwork, ValidationResult as GossipValidationResult, Validator as GossipValidator,
	ValidatorContext as GossipValidatorContext,
};

use sp_api::ProvideRuntimeApi;
use sp_application_crypto::AppPublic;
use sp_blockchain::HeaderBackend;
use sp_consensus::SyncOracle as SyncOracleT;
use sp_keystore::SyncCryptoStorePtr;
use sp_runtime::traits::Block;

mod error;
mod metrics;
mod round;
mod worker;

pub mod notification;

pub const BEEFY_PROTOCOL_NAME: &str = "/paritytech/beefy/1";

/// Returns the configuration value to put in
/// [`sc_network::config::NetworkConfiguration::extra_sets`].
pub fn beefy_peers_set_config() -> sc_network::config::NonDefaultSetConfig {
	sc_network::config::NonDefaultSetConfig {
		notifications_protocol: BEEFY_PROTOCOL_NAME.into(),
		max_notification_size: 1024 * 1024,
		set_config: sc_network::config::SetConfig {
			in_peers: 25,
			out_peers: 25,
			reserved_nodes: Vec::new(),
			non_reserved_mode: sc_network::config::NonReservedPeerMode::Accept,
		},
	}
}

/// A convenience BEEFY client trait that defines all the type bounds a BEEFY client
/// has to satisfy. Ideally that should actually be a trait alias. Unfortunately as
/// of today, Rust does not allow a type alias to be used as a trait bound. Tracking
/// issue is <https://github.com/rust-lang/rust/issues/41517>.
pub trait Client<B, BE, P>:
	BlockchainEvents<B> + HeaderBackend<B> + Finalizer<B, BE> + ProvideRuntimeApi<B> + Send + Sync
where
	B: Block,
	BE: Backend<B>,
	P: sp_core::Pair,
	P::Public: AppPublic + Codec,
	P::Signature: Clone + Codec + Debug + PartialEq + TryFrom<Vec<u8>>,
{
	// empty
}

impl<B, BE, P, T> Client<B, BE, P> for T
where
	B: Block,
	BE: Backend<B>,
	P: sp_core::Pair,
	P::Public: AppPublic + Codec,
	P::Signature: Clone + Codec + Debug + PartialEq + TryFrom<Vec<u8>>,
	T: BlockchainEvents<B> + HeaderBackend<B> + Finalizer<B, BE> + ProvideRuntimeApi<B> + Send + Sync,
{
	// empty
}

/// Allows all gossip messages to get through.
struct AllowAll<Hash> {
	topic: Hash,
}

impl<B> GossipValidator<B> for AllowAll<B::Hash>
where
	B: Block,
{
	fn validate(
		&self,
		_context: &mut dyn GossipValidatorContext<B>,
		_sender: &sc_network::PeerId,
		_data: &[u8],
	) -> GossipValidationResult<B::Hash> {
		GossipValidationResult::ProcessAndKeep(self.topic)
	}
}

/// Start the BEEFY gadget.
///
/// This is a thin shim around running and awaiting a BEEFY worker.
pub async fn start_beefy_gadget<B, P, BE, C, N, SO>(
	client: Arc<C>,
	key_store: SyncCryptoStorePtr,
	network: N,
	signed_commitment_sender: notification::BeefySignedCommitmentSender<B, P::Signature>,
	_sync_oracle: SO,
	prometheus_registry: Option<Registry>,
) where
	B: Block,
	P: sp_core::Pair,
	P::Public: AppPublic + Codec,
	P::Signature: Clone + Codec + Debug + PartialEq + TryFrom<Vec<u8>>,
	BE: Backend<B>,
	C: Client<B, BE, P>,
	C::Api: BeefyApi<B, P::Public>,
	N: GossipNetwork<B> + Clone + Send + 'static,
	SO: SyncOracleT + Send + 'static,
{
	let gossip_engine = GossipEngine::new(
		network,
		BEEFY_PROTOCOL_NAME,
		Arc::new(AllowAll {
			topic: worker::topic::<B>(),
		}),
		None,
	);

	let metrics = prometheus_registry
		.as_ref()
		.map(metrics::Metrics::register)
		.and_then(|result| match result {
			Ok(metrics) => {
				debug!(target: "beefy", "🥩 Registered metrics");
				Some(metrics)
			}
			Err(err) => {
				debug!(target: "beefy", "🥩 Failed to register metrics: {:?}", err);
				None
			}
		});

	let worker = worker::BeefyWorker::<_, P::Signature, _, BE, P>::new(
		client.clone(),
		key_store,
		signed_commitment_sender,
		gossip_engine,
		metrics,
	);

	worker.run().await
}
