// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

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

use std::collections::HashMap;
use std::sync::Arc;
use std::io;
use std::time::Duration;
use futures::sync::{oneshot, mpsc};
use network::{NetworkProtocolHandler, NetworkContext, PeerId, ProtocolId,
NetworkConfiguration , NonReservedPeerMode, ErrorKind};
use network_devp2p::{NetworkService};
use core_io::{TimerToken};
use io::NetSyncIo;
use protocol::{Protocol, ProtocolContext, Context, ProtocolStatus, PeerInfo as ProtocolPeerInfo};
use config::{ProtocolConfig};
use error::Error;
use chain::Client;
use message::LocalizedBftMessage;
use specialization::Specialization;
use on_demand::OnDemandService;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT};

/// Type that represents fetch completion future.
pub type FetchFuture = oneshot::Receiver<Vec<u8>>;
/// Type that represents bft messages stream.
pub type BftMessageStream<B> = mpsc::UnboundedReceiver<LocalizedBftMessage<B>>;

const TICK_TOKEN: TimerToken = 0;
const TICK_TIMEOUT: Duration = Duration::from_millis(1000);

const PROPAGATE_TOKEN: TimerToken = 1;
const PROPAGATE_TIMEOUT: Duration = Duration::from_millis(5000);

bitflags! {
	/// Node roles bitmask.
	pub struct Role: u32 {
		/// No network.
		const NONE = 0b00000000;
		/// Full node, does not participate in consensus.
		const FULL = 0b00000001;
		/// Light client node.
		const LIGHT = 0b00000010;
		/// Act as an authority
		const AUTHORITY = 0b00000100;
	}
}

/// Sync status
pub trait SyncProvider<B: BlockT>: Send + Sync {
	/// Get sync status
	fn status(&self) -> ProtocolStatus<B>;
	/// Get peers information
	fn peers(&self) -> Vec<PeerInfo<B>>;
	/// Get this node id if available.
	fn node_id(&self) -> Option<String>;
}

/// Transaction pool interface
pub trait TransactionPool<B: BlockT>: Send + Sync {
	/// Get transactions from the pool that are ready to be propagated.
	fn transactions(&self) -> Vec<(B::Hash, B::Extrinsic)>;
	/// Import a transction into the pool.
	fn import(&self, transaction: &B::Extrinsic) -> Option<B::Hash>;
	/// Notify the pool about transactions broadcast.
	fn on_broadcasted(&self, propagations: HashMap<B::Hash, Vec<String>>);
}

/// ConsensusService
pub trait ConsensusService<B: BlockT>: Send + Sync {
	/// Maintain connectivity to given addresses.
	fn connect_to_authorities(&self, addresses: &[String]);

	/// Get BFT message stream for messages corresponding to consensus on given
	/// parent hash.
	fn bft_messages(&self, parent_hash: B::Hash) -> BftMessageStream<B>;
	/// Send out a BFT message.
	fn send_bft_message(&self, message: LocalizedBftMessage<B>);
}

/// Service able to execute closure in the network context.
pub trait ExecuteInContext<B: BlockT>: Send + Sync {
	/// Execute closure in network context.
	fn execute_in_context<F: Fn(&mut Context<B>)>(&self, closure: F);
}

/// devp2p Protocol handler
struct ProtocolHandler<B: BlockT, S: Specialization<B>> {
	protocol: Protocol<B, S>,
}

/// Peer connection information
#[derive(Debug)]
pub struct PeerInfo<B: BlockT> {
	/// Public node id
	pub id: Option<String>,
	/// Node client ID
	pub client_version: String,
	/// Capabilities
	pub capabilities: Vec<String>,
	/// Remote endpoint address
	pub remote_address: String,
	/// Local endpoint address
	pub local_address: String,
	/// Dot protocol info.
	pub dot_info: Option<ProtocolPeerInfo<B>>,
}

/// Service initialization parameters.
pub struct Params<B: BlockT, S> {
	/// Configuration.
	pub config: ProtocolConfig,
	/// Network layer configuration.
	pub network_config: NetworkConfiguration,
	/// Polkadot relay chain access point.
	pub chain: Arc<Client<B>>,
	/// On-demand service reference.
	pub on_demand: Option<Arc<OnDemandService<B>>>,
	/// Transaction pool.
	pub transaction_pool: Arc<TransactionPool<B>>,
	/// Protocol specialization.
	pub specialization: S,
}

/// Polkadot network service. Handles network IO and manages connectivity.
pub struct Service<B: BlockT + 'static, S: Specialization<B>> where B::Header: HeaderT<Number=u64> {
	/// Network service
	network: NetworkService,
	/// Devp2p protocol handler
	handler: Arc<ProtocolHandler<B, S>>,
	/// Devp2p protocol ID.
	protocol_id: ProtocolId,
}

impl<B: BlockT + 'static, S: Specialization<B>> Service<B, S> where B::Header: HeaderT<Number=u64> {
	/// Creates and register protocol with the network service
	pub fn new(params: Params<B, S>, protocol_id: ProtocolId) -> Result<Arc<Service<B, S>>, Error> {
		let service = NetworkService::new(params.network_config.clone(), None)?;
		let sync = Arc::new(Service {
			network: service,
			protocol_id,
			handler: Arc::new(ProtocolHandler {
				protocol: Protocol::new(
					params.config,
					params.chain.clone(),
					params.on_demand,
					params.transaction_pool,
					params.specialization
				)?,
			}),
		});

		Ok(sync)
	}

	/// Called when a new block is imported by the client.
	pub fn on_block_imported(&self, hash: B::Hash, header: &B::Header) {
		self.network.with_context(self.protocol_id, |context| {
			self.handler.protocol.on_block_imported(&mut NetSyncIo::new(context), hash, header)
		});
	}

	/// Called when new transactons are imported by the client.
	pub fn trigger_repropagate(&self) {
		self.network.with_context(self.protocol_id, |context| {
			self.handler.protocol.propagate_extrinsics(&mut NetSyncIo::new(context));
		});
	}

	/// Execute a closure with the chain-specific network specialization.
	/// If the network is unavailable, this will return `None`.
	pub fn with_spec<F, U>(&self, f: F) -> Option<U>
		where F: FnOnce(&mut S, &mut Context<B>) -> U
	{
		let mut res = None;
		self.network.with_context(self.protocol_id, |context| {
			res = Some(self.handler.protocol.with_spec(&mut NetSyncIo::new(context), f))
		});

		res
	}

	fn start(&self) {
		match self.network.start().map_err(|e| e.0.into()) {
			Err(ErrorKind::Io(ref e)) if  e.kind() == io::ErrorKind::AddrInUse =>
				warn!("Network port is already in use, make sure that another instance of Polkadot client is not running or change the port using the --port option."),
			Err(err) => warn!("Error starting network: {}", err),
			_ => {},
		};
		self.network.register_protocol(self.handler.clone(), self.protocol_id, &[(::protocol::CURRENT_VERSION as u8, ::protocol::CURRENT_PACKET_COUNT)])
			.unwrap_or_else(|e| warn!("Error registering polkadot protocol: {:?}", e));
	}

	fn stop(&self) {
		self.handler.protocol.abort();
		self.network.stop();
	}
}

impl<B: BlockT + 'static, S: Specialization<B>> Drop for Service<B, S> where B::Header: HeaderT<Number=u64> {
	fn drop(&mut self) {
		self.stop();
	}
}

impl<B: BlockT + 'static, S: Specialization<B>> ExecuteInContext<B> for Service<B, S> where B::Header: HeaderT<Number=u64> {
	fn execute_in_context<F: Fn(&mut ::protocol::Context<B>)>(&self, closure: F) {
		self.network.with_context(self.protocol_id, |context| {
			closure(&mut ProtocolContext::new(self.handler.protocol.context_data(), &mut NetSyncIo::new(context)))
		});
	}
}

impl<B: BlockT + 'static, S: Specialization<B>> SyncProvider<B> for Service<B, S> where B::Header: HeaderT<Number=u64> {
	/// Get sync status
	fn status(&self) -> ProtocolStatus<B> {
		self.handler.protocol.status()
	}

	/// Get sync peers
	fn peers(&self) -> Vec<PeerInfo<B>> {
		self.network.with_context_eval(self.protocol_id, |ctx| {
			let peer_ids = self.network.connected_peers();

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
					dot_info: self.handler.protocol.peer_info(peer_id),
				})
			}).collect()
		}).unwrap_or_else(Vec::new)
	}

	fn node_id(&self) -> Option<String> {
		self.network.external_url()
	}
}

impl<B: BlockT + 'static, S: Specialization<B>> NetworkProtocolHandler for ProtocolHandler<B, S> where B::Header: HeaderT<Number=u64> {
	fn initialize(&self, io: &NetworkContext) {
		io.register_timer(TICK_TOKEN, TICK_TIMEOUT)
			.expect("Error registering sync timer");

		io.register_timer(PROPAGATE_TOKEN, PROPAGATE_TIMEOUT)
			.expect("Error registering transaction propagation timer");
	}

	fn read(&self, io: &NetworkContext, peer: &PeerId, _packet_id: u8, data: &[u8]) {
		self.protocol.handle_packet(&mut NetSyncIo::new(io), *peer, data);
	}

	fn connected(&self, io: &NetworkContext, peer: &PeerId) {
		self.protocol.on_peer_connected(&mut NetSyncIo::new(io), *peer);
	}

	fn disconnected(&self, io: &NetworkContext, peer: &PeerId) {
		self.protocol.on_peer_disconnected(&mut NetSyncIo::new(io), *peer);
	}

	fn timeout(&self, io: &NetworkContext, timer: TimerToken) {
		match timer {
			TICK_TOKEN => self.protocol.tick(&mut NetSyncIo::new(io)),
			PROPAGATE_TOKEN => self.protocol.propagate_extrinsics(&mut NetSyncIo::new(io)),
			_ => {}
		}
	}
}

/// Trait for managing network
pub trait ManageNetwork: Send + Sync {
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


impl<B: BlockT + 'static, S: Specialization<B>> ManageNetwork for Service<B, S> where B::Header: HeaderT<Number=u64> {
	fn accept_unreserved_peers(&self) {
		self.network.set_non_reserved_mode(NonReservedPeerMode::Accept);
	}

	fn deny_unreserved_peers(&self) {
		self.network.set_non_reserved_mode(NonReservedPeerMode::Deny);
	}

	fn remove_reserved_peer(&self, peer: String) -> Result<(), String> {
		self.network.remove_reserved_peer(&peer).map_err(|e| format!("{:?}", e))
	}

	fn add_reserved_peer(&self, peer: String) -> Result<(), String> {
		self.network.add_reserved_peer(&peer).map_err(|e| format!("{:?}", e))
	}

	fn start_network(&self) {
		self.start();
	}

	fn stop_network(&self) {
		self.stop();
	}
}
