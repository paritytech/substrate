// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.?

use std::sync::Arc;
use std::collections::{BTreeMap};
use std::io;
use futures::sync::oneshot;
use network::{NetworkConfiguration, NonReservedPeerMode, ErrorKind};
use network_devp2p::{NetworkService};
use primitives::block::{ExtrinsicHash, Header, HeaderHash};
use primitives::Hash;
use light_client::LightClient;
use full::{ConsensusService, StatementStream, BftMessageStream};
use full::chain::Client;
use full::message::{Statement, LocalizedBftMessage};
use full::protocol::Protocol as FullProtocol;
use light::protocol::Protocol as LightProtocol;
use handler::ProtocolHandler;
use sync_provider::{SyncProvider, ProtocolStatus, TransactionStats, PeerInfo};
use io::NetSyncIo;
use config::{ProtocolConfig};
use error::Error;

/// Type that represents fetch completion future.
pub type FetchFuture = oneshot::Receiver<Vec<u8>>;

/// Transaction pool interface
pub trait TransactionPool: Send + Sync {
	/// Get transactions from the pool that are ready to be propagated.
	fn transactions(&self) -> Vec<(ExtrinsicHash, Vec<u8>)>;
	/// Import a transction into the pool.
	fn import(&self, transaction: &[u8]) -> Option<ExtrinsicHash>;
}

/// Service initialization parameters.
pub struct Params {
	/// Configuration.
	pub config: ProtocolConfig,
	/// Network layer configuration.
	pub network_config: NetworkConfiguration,
	/// Transaction pool.
	pub transaction_pool: Arc<TransactionPool>,
}

/// Polkadot network service. Handles network IO and manages connectivity.
pub struct Service {
	data: Arc<ServiceData>,
}

struct ServiceData {
	/// Network service
	network: NetworkService,
	/// Devp2p protocol handler
	handler: Arc<ProtocolHandler>,
}

impl Service {
	/// Creates and registers full protocol with the network service.
	pub fn new_full(chain: Arc<Client>, params: Params) -> Result<(Arc<Service>, Arc<ConsensusService>), Error> {
		let service = NetworkService::new(params.network_config.clone(), None)?;
		let data = Arc::new(ServiceData {
			network: service,
			handler: Arc::new(ProtocolHandler::Full(FullProtocol::new(
				params.config, chain, params.transaction_pool)?,
			)),
		});
		let sync = Arc::new(Service { data: data.clone(), });

		Ok((sync, data))
	}

	/// Creates and register light protocol with the network service
	pub fn new_light(_light_client: Arc<LightClient>, params: Params) -> Result<Arc<Service>, Error> {
		let service = NetworkService::new(params.network_config.clone(), None)?;
		let data = Arc::new(ServiceData {
			network: service,
			handler: Arc::new(ProtocolHandler::Light(LightProtocol)),
		});
		let sync = Arc::new(Service { data, });

		Ok(sync)
	}

	/// Called when a new block is imported by the client.
	pub fn on_block_imported(&self, hash: HeaderHash, header: &Header) {
		self.data.network.with_context(self.data.handler.protocol_id(), |context| {
			self.data.handler.on_block_imported(&mut NetSyncIo::new(context), hash, header)
		});
	}

	/// Called when new transactons are imported by the client.
	pub fn on_new_transactions(&self, transactions: &[(ExtrinsicHash, Vec<u8>)]) {
		self.data.network.with_context(self.data.handler.protocol_id(), |context| {
			self.data.handler.on_new_transactions(&mut NetSyncIo::new(context), transactions);
		});
	}

	fn start(&self) {
		match self.data.network.start().map_err(Into::into) {
			Err(ErrorKind::Io(ref e)) if  e.kind() == io::ErrorKind::AddrInUse =>
				warn!("Network port {:?} is already in use, make sure that another instance of Polkadot client is not running or change the port using the --port option.",
					self.data.network.config().listen_address.expect("Listen address is not set.")),
			Err(err) => warn!("Error starting network: {}", err),
			_ => {},
		};

		self.data.network.register_protocol(
			self.data.handler.clone(),
			self.data.handler.protocol_id(),
			1,
			&[0u8])
		.unwrap_or_else(|e| warn!("Error registering polkadot protocol: {:?}", e));
	}

	fn stop(&self) {
		self.data.handler.abort();
		self.data.network.stop().unwrap_or_else(|e| warn!("Error stopping network: {:?}", e));
	}
}

impl Drop for Service {
	fn drop(&mut self) {
		self.stop();
	}
}

impl SyncProvider for Service {
	/// Get sync status
	fn status(&self) -> ProtocolStatus {
		self.data.handler.status()
	}

	/// Get sync peers
	fn peers(&self) -> Vec<PeerInfo> {
		self.data.network.with_context_eval(self.data.handler.protocol_id(), |ctx| {
			let peer_ids = self.data.network.connected_peers();

			peer_ids.into_iter().filter_map(|peer_id| {
				let session_info = match ctx.session_info(peer_id) {
					None => return None,
					Some(info) => info,
				};

				Some(PeerInfo {
					id: session_info.id.map(|id| format!("{:x}", id)),
					client_version: session_info.client_version,
					capabilities: session_info.peer_capabilities.into_iter().map(|c| c.to_string()).collect(),
					remote_address: session_info.remote_address,
					local_address: session_info.local_address,
					dot_info: self.data.handler.protocol_peer_info(peer_id),
				})
			}).collect()
		}).unwrap_or_else(Vec::new)
	}

	fn node_id(&self) -> Option<String> {
		self.data.network.external_url()
	}

	fn transactions_stats(&self) -> BTreeMap<ExtrinsicHash, TransactionStats> {
		self.data.handler.transactions_stats()
	}
}

/// ConsensusService
const CONSENSUS_SERVICE_PROOF: &str = "ConsensusService is returned only if full_handler.is_some(); qed";

impl ConsensusService for ServiceData {
	fn statements(&self) -> StatementStream {
		self.handler.full()
			.expect(CONSENSUS_SERVICE_PROOF)
			.statements()
	}

	fn connect_to_authorities(&self, _addresses: &[String]) {
		//TODO: implement me
	}

	fn fetch_candidate(&self, hash: &Hash) -> oneshot::Receiver<Vec<u8>> {
		self.network.with_context_eval(self.handler.protocol_id(), |context| {
			self.handler.full()
				.expect(CONSENSUS_SERVICE_PROOF)
				.fetch_candidate(&mut NetSyncIo::new(context), hash)
		}).expect("DOT Service is registered")
	}

	fn send_statement(&self, statement: Statement) {
		self.network.with_context(self.handler.protocol_id(), |context| {
			self.handler.full()
				.expect(CONSENSUS_SERVICE_PROOF)
				.send_statement(&mut NetSyncIo::new(context), statement);
		});
	}

	fn set_local_candidate(&self, candidate: Option<(Hash, Vec<u8>)>) {
		self.handler.full()
			.expect(CONSENSUS_SERVICE_PROOF)
			.set_local_candidate(candidate)
	}

	fn bft_messages(&self) -> BftMessageStream {
		self.handler.full()
			.expect(CONSENSUS_SERVICE_PROOF)
			.bft_messages()
	}

	fn send_bft_message(&self, message: LocalizedBftMessage) {
		self.network.with_context(self.handler.protocol_id(), |context| {
			self.handler.full()
				.expect(CONSENSUS_SERVICE_PROOF)
				.send_bft_message(&mut NetSyncIo::new(context), message);
		});
	}
}

/// Trait for managing network
pub trait ManageNetwork : Send + Sync {
	/// Set to allow unreserved peers to connect
	fn accept_unreserved_peers(&self);
	/// Set to deny unreserved peers to connect
	fn deny_unreserved_peers(&self);
	/// Remove reservation for the peer
	fn remove_reserved_peer(&self, peer: String) -> Result<(), String>;
	/// Add reserved peer
	fn add_reserved_peer(&self, peer: String) -> Result<(), String>;
	/// Start network
	fn start_network(&self);
	/// Stop network
	fn stop_network(&self);
}


impl ManageNetwork for Service {
	fn accept_unreserved_peers(&self) {
		self.data.network.set_non_reserved_mode(NonReservedPeerMode::Accept);
	}

	fn deny_unreserved_peers(&self) {
		self.data.network.set_non_reserved_mode(NonReservedPeerMode::Deny);
	}

	fn remove_reserved_peer(&self, peer: String) -> Result<(), String> {
		self.data.network.remove_reserved_peer(&peer).map_err(|e| format!("{:?}", e))
	}

	fn add_reserved_peer(&self, peer: String) -> Result<(), String> {
		self.data.network.add_reserved_peer(&peer).map_err(|e| format!("{:?}", e))
	}

	fn start_network(&self) {
		self.start();
	}

	fn stop_network(&self) {
		self.stop();
	}
}
