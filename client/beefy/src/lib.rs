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

use beefy_primitives::BeefyApi;
use codec::Codec;
use sc_client_api::{Backend as BackendT, BlockchainEvents, Finalizer};
use sc_network_gossip::{
	GossipEngine, Network as GossipNetwork, ValidationResult as GossipValidationResult, Validator as GossipValidator,
	ValidatorContext as GossipValidatorContext,
};
use sp_api::{BlockId, ProvideRuntimeApi};
use sp_application_crypto::AppPublic;
use sp_blockchain::HeaderBackend;
use sp_consensus::SyncOracle as SyncOracleT;
use sp_keystore::SyncCryptoStorePtr;
use sp_runtime::traits::{Block as BlockT, Zero};
use std::{convert::TryFrom, fmt::Debug, sync::Arc};

mod error;
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

/// Allows all gossip messages to get through.
struct AllowAll<Hash> {
	topic: Hash,
}

impl<Block> GossipValidator<Block> for AllowAll<Block::Hash>
where
	Block: BlockT,
{
	fn validate(
		&self,
		_context: &mut dyn GossipValidatorContext<Block>,
		_sender: &sc_network::PeerId,
		_data: &[u8],
	) -> GossipValidationResult<Block::Hash> {
		GossipValidationResult::ProcessAndKeep(self.topic)
	}
}

pub async fn start_beefy_gadget<Block, Pair, Backend, Client, Network, SyncOracle>(
	client: Arc<Client>,
	key_store: SyncCryptoStorePtr,
	network: Network,
	signed_commitment_sender: notification::BeefySignedCommitmentSender<Block, Pair::Signature>,
	_sync_oracle: SyncOracle,
) where
	Block: BlockT,
	Pair: sp_core::Pair,
	Pair::Public: AppPublic + Codec,
	Pair::Signature: Clone + Codec + Debug + PartialEq + TryFrom<Vec<u8>>,
	Backend: BackendT<Block>,
	Client: BlockchainEvents<Block>
		+ HeaderBackend<Block>
		+ Finalizer<Block, Backend>
		+ ProvideRuntimeApi<Block>
		+ Send
		+ Sync,
	Client::Api: BeefyApi<Block, Pair::Public>,
	Network: GossipNetwork<Block> + Clone + Send + 'static,
	SyncOracle: SyncOracleT + Send + 'static,
{
	let gossip_engine = GossipEngine::new(
		network,
		BEEFY_PROTOCOL_NAME,
		Arc::new(AllowAll {
			topic: worker::topic::<Block>(),
		}),
		None,
	);

	let at = BlockId::hash(client.info().best_hash);

	let validator_set = client
		.runtime_api()
		.validator_set(&at)
		.expect("Failed to get BEEFY validator set");

	let best_finalized_block = client.info().finalized_number;
	let best_block_voted_on = Zero::zero();

	let worker = worker::BeefyWorker::<_, Pair::Public, Pair::Signature, _>::new(
		validator_set,
		key_store,
		client.finality_notification_stream(),
		gossip_engine,
		signed_commitment_sender,
		best_finalized_block,
		best_block_voted_on,
	);

	worker.run().await
}
