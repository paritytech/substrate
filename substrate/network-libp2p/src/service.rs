// Copyright 2018 Parity Technologies (UK) Ltd.
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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.?

use bytes::Bytes;
use {Error, ErrorKind, NetworkConfiguration, NetworkProtocolHandler};
use {NonReservedPeerMode, NetworkContext, Severity, NodeIndex, ProtocolId};
use parking_lot::{Mutex, RwLock};
use libp2p;
use libp2p::multiaddr::{AddrComponent, Multiaddr};
use libp2p::kad::{KadSystem, KadConnecConfig, KadSystemConfig};
use libp2p::kad::{KadIncomingRequest, KadConnecController, KadPeer};
use libp2p::kad::{KadConnectionType, KadQueryEvent};
use libp2p::identify::{IdentifyInfo, IdentifyOutput, IdentifyTransportOutcome};
use libp2p::identify::{IdentifyProtocolConfig, PeerIdTransport};
use libp2p::core::{upgrade, Transport, MuxedTransport, ConnectionUpgrade};
use libp2p::core::{Endpoint, PeerId as PeerstorePeerId, PublicKey};
use libp2p::core::{SwarmController, UniqueConnecState};
use libp2p::ping;
use libp2p::transport_timeout::TransportTimeout;
use {PacketId, SessionInfo, ConnectionFilter, TimerToken};
use rand;
use std::io::{Error as IoError, ErrorKind as IoErrorKind};
use std::iter;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::sync::Arc;
use std::sync::mpsc as sync_mpsc;
use std::thread;
use std::time::{Duration, Instant};
use futures::{future, Future, Stream, IntoFuture};
use futures::sync::{mpsc, oneshot};
use tokio::runtime::current_thread;
use tokio_io::{AsyncRead, AsyncWrite};
use tokio_timer::{Interval, Deadline};

use custom_proto::{RegisteredProtocol, RegisteredProtocols};
use custom_proto::RegisteredProtocolOutput;
use network_state::NetworkState;
use timeouts;
use transport;

/// IO Service with networking.
pub struct NetworkService {
	shared: Arc<Shared>,

	/// Holds the networking-running background thread alive. The `Option` is
	/// `None` if the service is stopped.
	/// Sending a message on the channel will trigger the end of the
	/// background thread. We can then wait on the join handle.
	bg_thread: Mutex<Option<(oneshot::Sender<()>, thread::JoinHandle<()>)>>,
}

/// Common struct shared throughout all the components of the service.
struct Shared {
	/// Original configuration of the service.
	config: NetworkConfiguration,

	/// Contains the state of the network.
	network_state: NetworkState,

	/// Kademlia system. Contains the DHT.
	kad_system: KadSystem,

	/// Configuration for the Kademlia upgrade.
	kad_upgrade: KadConnecConfig,

	/// List of protocols available on the network. It is a logic error to
	/// remove protocols from this list, and the code may assume that protocols
	/// stay at the same index forever.
	protocols: RwLock<RegisteredProtocols<Arc<NetworkProtocolHandler + Send + Sync>>>,

	/// Use this channel to send a timeout request to the background thread's
	/// events loop. After the timeout, elapsed, it will call `timeout` on the
	/// `NetworkProtocolHandler`. This can be closed if the background thread
	/// is not running. The sender will be overwritten every time we start
	/// the service.
	timeouts_register_tx: RwLock<mpsc::UnboundedSender<(Duration, (Arc<NetworkProtocolHandler + Send + Sync>, ProtocolId, TimerToken))>>,

	/// Original address from the configuration, after being adjusted by the `Transport`.
	/// Contains `None` if the network hasn't started yet.
	original_listened_addr: RwLock<Option<Multiaddr>>,

	/// Contains the addresses we known about ourselves.
	listened_addrs: RwLock<Vec<Multiaddr>>,
}

impl NetworkService {
	/// Starts IO event loop
	pub fn new(
		config: NetworkConfiguration,
		filter: Option<Arc<ConnectionFilter>>
	) -> Result<NetworkService, Error> {
		// TODO: for now `filter` is always `None` ; remove it from the code or implement it
		assert!(filter.is_none());

		let network_state = NetworkState::new(&config)?;

		let local_peer_id = network_state.local_public_key().clone()
			.into_peer_id();
		let mut listen_addr = config_to_listen_addr(&config);
		listen_addr.append(AddrComponent::P2P(local_peer_id.clone().into_bytes()));
		info!(target: "sub-libp2p", "Local node address is: {}", listen_addr);

		let kad_system = KadSystem::without_init(KadSystemConfig {
			parallelism: 3,
			local_peer_id: local_peer_id.clone(),
			kbuckets_timeout: Duration::from_secs(600),
			request_timeout: Duration::from_secs(10),
			known_initial_peers: network_state.known_peers(),
		});

		let shared = Arc::new(Shared {
			network_state,
			protocols: RwLock::new(Default::default()),
			kad_system,
			kad_upgrade: KadConnecConfig::new(),
			config,
			timeouts_register_tx: RwLock::new(mpsc::unbounded().0),
			original_listened_addr: RwLock::new(None),
			listened_addrs: RwLock::new(Vec::new()),
		});

		Ok(NetworkService {
			shared,
			bg_thread: Mutex::new(None),
		})
	}

	/// Returns network configuration.
	pub fn config(&self) -> &NetworkConfiguration {
		&self.shared.config
	}

	pub fn external_url(&self) -> Option<String> {
		// TODO: in the context of libp2p, it is hard to define what an external
		// URL is, as different nodes can have multiple different ways to
		// reach us
		self.shared.original_listened_addr.read().as_ref()
			.map(|addr|
				format!("{}/p2p/{}", addr, self.shared.kad_system.local_peer_id().to_base58())
			)
	}

	/// Start network IO.
	/// Note that we could use an iterator for `protocols`, but having a
	/// generic here is too much and crashes the Rust compiler.
	// TODO (design): the notion of having a `NetworkService` alive should mean
	// that it is running ; the `start` and `stop` functions are bad design
	pub fn start(
		&self,
		protocols: Vec<(Arc<NetworkProtocolHandler + Send + Sync>, ProtocolId, &[(u8, u8)])>
	) -> Result<(), (Error, Option<SocketAddr>)> {
		// TODO: check that service is started already?

		*self.shared.protocols.write() = RegisteredProtocols(
			protocols.into_iter()
				.map(|(handler, protocol, versions)|
					RegisteredProtocol::new(handler.clone(), protocol, versions))
				.collect()
		);

		// Channel we use to signal success or failure of the bg thread
		// initialization process.
		let (init_tx, init_rx) = sync_mpsc::channel();
		// Channel the main thread uses to signal the bg thread that it
		// should stop
		let (close_tx, close_rx) = oneshot::channel();
		let (timeouts_register_tx, timeouts_register_rx) = mpsc::unbounded();
		*self.shared.timeouts_register_tx.write() = timeouts_register_tx;
			
		// Initialize all the protocols now.
		for protocol in self.shared.protocols.read().0.iter() {
			protocol.custom_data().initialize(&NetworkContextImpl {
				inner: self.shared.clone(),
				protocol: protocol.id().clone(),
				current_peer: None,
			});
		}

		let shared = self.shared.clone();
		let join_handle = thread::spawn(move || {
			// Tokio runtime that is going to run everything in this thread.
			let mut runtime = match current_thread::Runtime::new() {
				Ok(c) => c,
				Err(err) => {
					let _ = init_tx.send(Err(err.into()));
					return
				}
			};

			let fut = match init_thread(shared,
				timeouts_register_rx, close_rx) {
				Ok(future) => {
					debug!(target: "sub-libp2p", "Successfully started networking service");
					let _ = init_tx.send(Ok(()));
					future
				},
				Err(err) => {
					let _ = init_tx.send(Err(err));
					return
				}
			};

			match runtime.block_on(fut) {
				Ok(()) => debug!(target: "sub-libp2p", "libp2p future finished"),
				Err(err) => error!(target: "sub-libp2p", "error while running libp2p: {:?}", err),
			}
		});

		init_rx.recv().expect("libp2p background thread panicked")
			.map_err(|err| (err, self.shared.config.listen_address.clone()))?;

		*self.bg_thread.lock() = Some((close_tx, join_handle));
		Ok(())
	}

	/// Stop network IO.
	pub fn stop(&self) {
		if let Some((close_tx, join)) = self.bg_thread.lock().take() {
			let _ = close_tx.send(());
			if let Err(e) = join.join() {
				warn!(target: "sub-libp2p", "error while waiting on libp2p background thread: {:?}", e);
			}
		}

		debug_assert!(!self.shared.network_state.has_connected_peer());
	}

	/// Get a list of all connected peers by id.
	pub fn connected_peers(&self) -> Vec<NodeIndex> {
		self.shared.network_state.connected_peers()
	}

	/// Try to add a reserved peer.
	pub fn add_reserved_peer(&self, peer: &str) -> Result<(), Error> {
		// TODO: try to dial the peer?
		self.shared.network_state.add_reserved_peer(peer)
	}

	/// Try to remove a reserved peer.
	pub fn remove_reserved_peer(&self, peer: &str) -> Result<(), Error> {
		self.shared.network_state.remove_reserved_peer(peer)
	}

	/// Set the non-reserved peer mode.
	pub fn set_non_reserved_mode(&self, mode: NonReservedPeerMode) {
		self.shared.network_state.set_non_reserved_mode(mode)
	}

	/// Executes action in the network context
	pub fn with_context<F>(&self, protocol: ProtocolId, action: F)
		where F: FnOnce(&NetworkContext) {
		self.with_context_eval(protocol, action);
	}

	/// Evaluates function in the network context
	pub fn with_context_eval<F, T>(&self, protocol: ProtocolId, action: F)
		-> Option<T>
		where F: FnOnce(&NetworkContext) -> T {
		if !self.shared.protocols.read().has_protocol(protocol) {
			return None
		}

		Some(action(&NetworkContextImpl {
			inner: self.shared.clone(),
			protocol: protocol.clone(),
			current_peer: None,
		}))
	}
}

impl Drop for NetworkService {
	fn drop(&mut self) {
		self.stop()
	}
}

#[derive(Clone)]
struct NetworkContextImpl {
	inner: Arc<Shared>,
	protocol: ProtocolId,
	current_peer: Option<NodeIndex>,
}

impl NetworkContext for NetworkContextImpl {
	fn send(&self, peer: NodeIndex, packet_id: PacketId, data: Vec<u8>) {
		self.send_protocol(self.protocol, peer, packet_id, data)
	}

	fn send_protocol(
		&self,
		protocol: ProtocolId,
		peer: NodeIndex,
		packet_id: PacketId,
		data: Vec<u8>
	) {
		debug_assert!(self.inner.protocols.read().has_protocol(protocol),
			"invalid protocol id requested in the API of the libp2p networking");
		// TODO: could be "optimized" by building `message` only after checking the validity of
		// 		the peer, but that's probably not worth the effort
		let mut message = Bytes::with_capacity(1 + data.len());
		message.extend_from_slice(&[packet_id]);
		message.extend_from_slice(&data);
		if self.inner.network_state.send(protocol, peer, message).is_err() {
			debug!(target: "sub-libp2p", "Sending to peer {} failed. Dropping.", peer);
			self.inner.network_state.drop_peer(peer);
		}
	}

	fn respond(&self, packet_id: PacketId, data: Vec<u8>) {
		if let Some(peer) = self.current_peer {
			self.send_protocol(self.protocol, peer, packet_id, data)
		} else {
			panic!("respond() called outside of a received message");
		}
	}

	fn report_peer(&self, peer: NodeIndex, reason: Severity) {
		if let Some(info) = self.inner.network_state.peer_info(peer) {
			if let (Some(client_version), Some(remote_address)) = (info.client_version, info.remote_address) {
				info!(target: "sub-libp2p",
					"Peer {} ({} {}) reported by client: {}",
					peer,
					remote_address,
					client_version,
					reason
				);
			} else {
				info!(target: "sub-libp2p", "Peer {} reported by client: {}", peer, reason);
			}
		}
		match reason {
			Severity::Bad(reason) => self.inner.network_state.ban_peer(peer, reason),
			Severity::Useless(_) => self.inner.network_state.drop_peer(peer),
			Severity::Timeout => self.inner.network_state.drop_peer(peer),
		}
	}

	fn is_expired(&self) -> bool {
		if let Some(current_peer) = self.current_peer {
			!self.inner.network_state.is_peer_connected(current_peer)
		} else {
			// TODO: is this correct?
			true
		}
	}

	fn register_timer(&self, token: usize, duration: Duration)
		-> Result<(), Error> {
		let handler = self.inner.protocols
			.read()
			.find_protocol(self.protocol)
			.ok_or(ErrorKind::BadProtocol)?
			.custom_data()
			.clone();
		self.inner.timeouts_register_tx.read()
			.unbounded_send((duration, (handler, self.protocol, token)))
			.map_err(|err| ErrorKind::Io(IoError::new(IoErrorKind::Other, err)))?;
		Ok(())
	}

	fn peer_client_version(&self, peer: NodeIndex) -> String {
		// Devp2p returns "unknown" on unknown peer ID, so we do the same.
		self.inner.network_state.peer_client_version(peer, self.protocol)
			.unwrap_or_else(|| "unknown".to_string())
	}

	fn session_info(&self, peer: NodeIndex) -> Option<SessionInfo> {
		self.inner.network_state.session_info(peer, self.protocol)
	}

	fn protocol_version(&self, protocol: ProtocolId, peer: NodeIndex) -> Option<u8> {
		self.inner.network_state.protocol_version(peer, protocol)
	}

	fn subprotocol_name(&self) -> ProtocolId {
		self.protocol.clone()
	}
}

/// Builds the main `Future` for the network service.
///
/// - `timeouts_register_rx` should receive newly-registered timeouts.
/// - `close_rx` should be triggered when we want to close the network.
fn init_thread(
	shared: Arc<Shared>,
	timeouts_register_rx: mpsc::UnboundedReceiver<
		(Duration, (Arc<NetworkProtocolHandler + Send + Sync + 'static>, ProtocolId, TimerToken))
	>,
	close_rx: oneshot::Receiver<()>
) -> Result<impl Future<Item = (), Error = IoError>, Error> {
	// Build the transport layer.
	let transport = {
		let base = transport::build_transport(
			transport::UnencryptedAllowed::Denied,
			shared.network_state.local_private_key().clone()
		);

		let addr_resolver = {
			let shared = shared.clone();
			move |who| {
				let addrs = shared.network_state.addrs_of_peer(&who);
				for addr in &addrs {
					trace!(target: "sub-libp2p", "{:?} resolved as {}", who, addr);
				}
				addrs.into_iter()
			}
		};

		PeerIdTransport::new(base.clone(), addr_resolver).and_then({
			let shared = shared.clone();
			move |out, endpoint, remote_addr| {
				let original_addr = out.original_addr.clone();
				let info = out.info.and_then(move |info| {
					process_identify_info(shared, &info, original_addr,
						endpoint, &base)?;
					Ok(info)
				});

				let out = TransportOutput {
					socket: out.socket,
					info: Box::new(info) as Box<_>,
					original_addr: out.original_addr,
				};

				future::ok((out, remote_addr))
			}
		})
	};

	// Build the swarm. The swarm is the single entry point where successfully
	// negotiated protocols arrive.
	let (swarm_controller, swarm_future) = {
		let upgraded_transport = transport.clone()
			.and_then({
				let shared = shared.clone();
				move |out, endpoint, client_addr| {
					let original_addr = out.original_addr;
					let listener_upgrade = upgrade::or(upgrade::or(upgrade::or(
						upgrade::map_with_addr(shared.kad_upgrade.clone(), |(c, f), a| FinalUpgrade::Kad(c, f, a.clone())),
						upgrade::map(IdentifyProtocolConfig, |id| FinalUpgrade::Identify(id, original_addr))),
						upgrade::map_with_addr(ping::Ping, |(p, f), addr| FinalUpgrade::Ping(p, f, addr.clone()))),
						upgrade::map_with_addr(DelayedProtosList(shared), |c, a| FinalUpgrade::Custom(c, a.clone())));
					upgrade::apply(out.socket, listener_upgrade, endpoint, client_addr)
				}
			});
		let shared = shared.clone();

		libp2p::core::swarm(
			upgraded_transport,
			move |upgrade, _client_addr|
				listener_handle(shared.clone(), upgrade)
		)
	};

	// Listen on multiaddress.
	// TODO: change the network config to directly contain a `Multiaddr`
	{
		let listen_addr = config_to_listen_addr(&shared.config);
		debug!(target: "sub-libp2p", "Libp2p listening on {}", listen_addr);
		match swarm_controller.listen_on(listen_addr.clone()) {
			Ok(new_addr) => {
				*shared.original_listened_addr.write() = Some(new_addr.clone());
			},
			Err(_) => {
				warn!(target: "sub-libp2p", "Can't listen on {}, protocol not supported", listen_addr);
				return Err(ErrorKind::BadProtocol.into())
			},
		}
	}
	// Explicitely connect to _all_ the boostrap nodes as a temporary measure.
	for bootnode in shared.config.boot_nodes.iter() {
		match shared.network_state.add_peer(bootnode) {
			Ok(who) => {
				trace!(target: "sub-libp2p", "Dialing bootnode {:?}", who);
				for proto in shared.protocols.read().0.clone().into_iter() {
					open_peer_custom_proto(
						shared.clone(),
						transport.clone(),
						proto,
						who.clone(),
						&swarm_controller
					)
				}
			},
			Err(Error(ErrorKind::AddressParse, _)) => {
				// fallback: trying with IP:Port
				let multi = match bootnode.parse::<SocketAddr>() { 
					Ok(SocketAddr::V4(socket)) =>
						format!("/ip4/{}/tcp/{}", socket.ip(), socket.port()).parse::<Multiaddr>(),
					Ok(SocketAddr::V6(socket)) =>
						format!("/ip6/{}/tcp/{}", socket.ip(), socket.port()).parse::<Multiaddr>(),
					_ => {
						warn!(target: "sub-libp2p", "Not a valid Bootnode Address {:}", bootnode);
						continue;
					}
				};

				if let Ok(addr) = multi {
					trace!(target: "sub-libp2p", "Missing NodeIndex for Bootnode {:}. Querying", bootnode);
					for proto in shared.protocols.read().0.clone().into_iter() {
						connect_with_query_peer_id(
							shared.clone(),
							transport.clone(),
							proto,
							addr.clone(),
							&swarm_controller
						)
					}
				} else {
					warn!(target: "sub-libp2p", "Not a valid Bootnode Address {:}", bootnode);
					continue;
				}
			},
			Err(err) => warn!(target:"sub-libp2p", "Couldn't parse Bootnode Address: {}", err),
		}
	}

	// Start connecting to nodes now.
	connect_to_nodes(shared.clone(), transport.clone(), &swarm_controller);

	// Build the timeouts system for the `register_timeout` function.
	// (note: this has nothing to do with socket timeouts)
	let timeouts = timeouts::build_timeouts_stream(timeouts_register_rx)
		.for_each({
			let shared = shared.clone();
			move |(handler, protocol_id, timer_token)| {
				handler.timeout(&NetworkContextImpl {
					inner: shared.clone(),
					protocol: protocol_id,
					current_peer: None,
				}, timer_token);
				Ok(())
			}
		})
		.then(|val| {
			warn!(target: "sub-libp2p", "Timeouts stream closed unexpectedly: {:?}", val);
			val
		});

	// Start the process of periodically discovering nodes to connect to.
	let discovery = start_kademlia_discovery(shared.clone(),
		transport.clone(), swarm_controller.clone());

	// Start the process of pinging the active nodes on the network.
	let pinger = start_pinger(shared.clone(), transport, swarm_controller);

	// Merge all the futures into one!
	Ok(swarm_future
		.select(discovery).map_err(|(err, _)| err).and_then(|(_, rest)| rest)
		.select(pinger).map_err(|(err, _)| err).and_then(|(_, rest)| rest)
		.select(timeouts).map_err(|(err, _)| err).and_then(|(_, rest)| rest)
		.select(close_rx.then(|_| Ok(()))).map(|_| ()).map_err(|(err, _)| err)

		.and_then(move |_| {
			debug!(target: "sub-libp2p", "Networking ended ; disconnecting all peers");
			shared.network_state.disconnect_all();
			Ok(())
		}))
}

/// Output of the common transport layer.
struct TransportOutput<S> {
	socket: S,
	info: Box<Future<Item = IdentifyTransportOutcome, Error = IoError>>,
	original_addr: Multiaddr,
}

/// Enum of all the possible protocols our service handles.
enum FinalUpgrade<C> {
	Kad(KadConnecController, Box<Stream<Item = KadIncomingRequest, Error = IoError>>, Multiaddr),
	/// The remote identification system, and the multiaddress we see the remote as.
	Identify(IdentifyOutput<C>, Multiaddr),
	Ping(ping::Pinger, Box<Future<Item = (), Error = IoError>>, Multiaddr),
	/// `Custom` means anything not in the core libp2p and is handled
	/// by `CustomProtoConnectionUpgrade`.
	Custom(RegisteredProtocolOutput<Arc<NetworkProtocolHandler + Send + Sync>>, Multiaddr),
}

/// Called whenever we successfully open a multistream with a remote.
fn listener_handle<'a, C>(
	shared: Arc<Shared>,
	upgrade: FinalUpgrade<C>,
) -> Box<Future<Item = (), Error = IoError> + 'a>
	where C: AsyncRead + AsyncWrite + 'a {
	match upgrade {
		FinalUpgrade::Kad(controller, kademlia_stream, client_addr) => {
			trace!(target: "sub-libp2p", "Opened kademlia substream with {:?}", client_addr);
			match handle_kademlia_connection(shared, client_addr, controller, kademlia_stream) {
				Ok(fut) => Box::new(fut) as Box<_>,
				Err(err) => Box::new(future::err(err)) as Box<_>,
			}
		},

		FinalUpgrade::Identify(IdentifyOutput::Sender { sender }, original_addr) => {
			trace!(target: "sub-libp2p", "Sending back identification info");
			sender.send(
				IdentifyInfo {
					public_key: shared.network_state.local_public_key().clone(),
					protocol_version: concat!("substrate/",
						env!("CARGO_PKG_VERSION")).to_owned(),		// TODO: ?
					agent_version: concat!("substrate/",
						env!("CARGO_PKG_VERSION")).to_owned(),
					listen_addrs: shared.listened_addrs.read().clone(),
					protocols: Vec::new(),		// TODO: protocols_to_report,
				},
				&original_addr
			)
		},

		FinalUpgrade::Identify(IdentifyOutput::RemoteInfo { .. }, _) =>
			unreachable!("We are never dialing with the identify protocol"),

		FinalUpgrade::Ping(pinger, future, client_addr) => {
			let node_id = p2p_multiaddr_to_node_id(client_addr);
			match shared.network_state.ping_connection(node_id.clone()) {
				Ok((_, ping_connec)) => {
					trace!(target: "sub-libp2p", "Successfully opened ping substream with {:?}", node_id);
					let fut = ping_connec.tie_or_passthrough(pinger, future);
					Box::new(fut) as Box<_>
				},
				Err(err) => Box::new(future::err(err)) as Box<_>
			}
		},

		FinalUpgrade::Custom(custom_proto_out, client_addr) => {
			// A "custom" protocol is one that is part of substrate and not part of libp2p.
			let shared = shared.clone();
			let fut = handle_custom_connection(shared, client_addr, custom_proto_out);
			Box::new(fut) as Box<_>
		},
	}
}

/// Handles a newly-opened Kademlia connection.
fn handle_kademlia_connection(
	shared: Arc<Shared>,
	client_addr: Multiaddr,
	controller: KadConnecController,
	kademlia_stream: Box<Stream<Item = KadIncomingRequest, Error = IoError>>
) -> Result<impl Future<Item = (), Error = IoError>, IoError> {
	let node_id = p2p_multiaddr_to_node_id(client_addr);
	let (who, kad_connec) = shared.network_state
		.kad_connection(node_id.clone())?;
	
	let node_id2 = node_id.clone();
	let future = future::loop_fn(kademlia_stream, move |kademlia_stream| {
		let shared = shared.clone();
		let node_id = node_id.clone();

		let next = kademlia_stream
			.into_future()
			.map_err(|(err, _)| err);
		let deadline = Instant::now() + Duration::from_secs(20);

		Deadline::new(next, deadline)
			.map_err(|err|
				// TODO: improve the error reporting here, but tokio-timer's API is bad
				IoError::new(IoErrorKind::Other, err)
			)
			.and_then(move |(req, rest)| {
				shared.kad_system.update_kbuckets(node_id);
				match req {
					Some(KadIncomingRequest::FindNode { searched, responder }) =>
						responder.respond(build_kademlia_response(&shared, &searched)),
					Some(KadIncomingRequest::PingPong) => (),
					None => return Ok(future::Loop::Break(()))
				}
				Ok(future::Loop::Continue(rest))
			})
	}).then(move |val| {
		trace!(target: "sub-libp2p", "Closed Kademlia connection with #{} {:?} => {:?}", who, node_id2, val);
		val
	});

	Ok(kad_connec.tie_or_passthrough(controller, future))
}

/// When a remote performs a `FIND_NODE` Kademlia request for `searched`,
/// this function builds the response to send back.
fn build_kademlia_response(
	shared: &Arc<Shared>,
	searched: &PeerstorePeerId
) -> Vec<KadPeer> {
	shared.kad_system
		.known_closest_peers(searched)
		.map(move |who| {
			if who == *shared.kad_system.local_peer_id() {
				KadPeer {
					node_id: who.clone(),
					multiaddrs: shared.listened_addrs.read().clone(),
					connection_ty: KadConnectionType::Connected,
				}
			} else {
				let addrs = shared.network_state.addrs_of_peer(&who);
				let connec_ty = if shared.network_state.has_connection(&who) {
					// TODO: this only checks connections with substrate ; but what
					//       if we're connected through Kademlia only?
					KadConnectionType::Connected
				} else {
					KadConnectionType::NotConnected
				};

				KadPeer {
					node_id: who.clone(),
					multiaddrs: addrs,
					connection_ty: connec_ty,
				}
			}
		})
		// TODO: we really want to remove nodes with no multiaddress from
		// the results, but a flaw in the Kad protocol of libp2p makes it
		// impossible to return empty results ; therefore we must at least
		// return ourselves
		.filter(|p| p.node_id == *shared.kad_system.local_peer_id() ||
			!p.multiaddrs.is_empty())
		.take(20)
		.collect::<Vec<_>>()
}

/// Handles a newly-opened connection to a remote with a custom protocol
/// (eg. `/substrate/dot/0`).
/// Returns a future that corresponds to when the handling is finished.
fn handle_custom_connection(
	shared: Arc<Shared>,
	client_addr: Multiaddr,
	custom_proto_out: RegisteredProtocolOutput<Arc<NetworkProtocolHandler + Send + Sync>>
) -> impl Future<Item = (), Error = IoError> {
	let handler = custom_proto_out.custom_data;
	let protocol_id = custom_proto_out.protocol_id;

	// We're using the `PeerIdTransport` layer, so all the multiaddresses received
	// here should be of the format `/p2p/<node_id>`.
	let node_id = p2p_multiaddr_to_node_id(client_addr);

	// Determine the ID of this peer, or drop the connection if the peer is disabled,
	// if we reached `max_peers`, or a similar reason.
	// TODO: is there a better way to refuse connections than to drop the
	//		 newly-opened substream? should we refuse the connection
	//		 beforehand?
	let (who, unique_connec) = match shared.network_state.custom_proto(
		node_id.clone(),
		protocol_id,
		custom_proto_out.endpoint,
	) {
		Ok(a) => a,
		Err(err) => return future::Either::A(future::err(err.into())),
	};

	if let UniqueConnecState::Full = unique_connec.state() {
		debug!(target: "sub-libp2p",
			"Interrupting connection attempt to {:?} with {:?} because we're already connected",
			node_id,
			custom_proto_out.protocol_id
		);
		return future::Either::A(future::ok(()))
	}

	struct ProtoDisconnectGuard {
		inner: Arc<Shared>,
		who: NodeIndex,
		node_id: PeerstorePeerId,
		handler: Arc<NetworkProtocolHandler + Send + Sync>,
		protocol: ProtocolId
	}

	impl Drop for ProtoDisconnectGuard {
		fn drop(&mut self) {
			info!(target: "sub-libp2p",
				"Node {:?} with peer ID {} through protocol {:?} disconnected",
				self.node_id,
				self.who,
				self.protocol
			);
			self.handler.disconnected(&NetworkContextImpl {
				inner: self.inner.clone(),
				protocol: self.protocol,
				current_peer: Some(self.who),
			}, &self.who);

			// When any custom protocol drops, we drop the peer entirely.
			// TODO: is this correct?
			self.inner.network_state.drop_peer(self.who);
		}
	}

	let dc_guard = ProtoDisconnectGuard {
		inner: shared.clone(),
		who,
		node_id: node_id.clone(),
		handler: handler.clone(),
		protocol: protocol_id,
	};

	let fut = custom_proto_out.incoming
		.for_each({
			let shared = shared.clone();
			let handler = handler.clone();
			let node_id = node_id.clone();
			move |(packet_id, data)| {
				shared.kad_system.update_kbuckets(node_id.clone());
				handler.read(&NetworkContextImpl {
					inner: shared.clone(),
					protocol: protocol_id,
					current_peer: Some(who.clone()),
				}, &who, packet_id, &data);
				Ok(())
			}
		});

	let val = (custom_proto_out.outgoing, custom_proto_out.protocol_version);
	let final_fut = unique_connec.tie_or_stop(val, fut)
		.then(move |val| {
			// Makes sure that `dc_guard` is kept alive until here.
			drop(dc_guard);
			val
		});

	debug!(target: "sub-libp2p",
		"Successfully connected to {:?} (peer id {}) with protocol {:?} version {}",
		node_id,
		who,
		protocol_id,
		custom_proto_out.protocol_version
	);

	handler.connected(&NetworkContextImpl {
		inner: shared.clone(),
		protocol: protocol_id,
		current_peer: Some(who),
	}, &who);

	future::Either::B(final_fut)
}

/// Builds the multiaddress corresponding to the address we need to listen to
/// according to the config.
// TODO: put the `Multiaddr` directly in the `NetworkConfiguration`
fn config_to_listen_addr(config: &NetworkConfiguration) -> Multiaddr {
	if let Some(addr) = config.listen_address {
		let ip = match addr.ip() {
			IpAddr::V4(addr) => AddrComponent::IP4(addr),
			IpAddr::V6(addr) => AddrComponent::IP6(addr),
		};
		iter::once(ip).chain(iter::once(AddrComponent::TCP(addr.port()))).collect()
	} else {
		let host = AddrComponent::IP4(Ipv4Addr::new(0, 0, 0, 0));
		let port = AddrComponent::TCP(0);
		iter::once(host).chain(iter::once(port)).collect()
	}
}

/// Randomly discovers peers to connect to.
/// This works by running a round at a regular interval, and skipping if we
/// reached `min_peers`. When we are over `min_peers`, we stop trying to dial
/// nodes and only accept incoming connections.
fn start_kademlia_discovery<T, To, St, C>(shared: Arc<Shared>, transport: T,
	swarm_controller: SwarmController<St>) -> impl Future<Item = (), Error = IoError>
	where T: MuxedTransport<Output =  TransportOutput<To>> + Clone + 'static,
		T::MultiaddrFuture: 'static,
		To: AsyncRead + AsyncWrite + 'static,
		St: MuxedTransport<Output = FinalUpgrade<C>> + Clone + 'static,
		C: 'static {
	let kad_init = shared.kad_system.perform_initialization({
		let shared = shared.clone();
		let transport = transport.clone();
		let swarm_controller = swarm_controller.clone();
		move |who|
			obtain_kad_connection(
				shared.clone(),
				who.clone(),
				transport.clone(),
				swarm_controller.clone()
			)
	});

	let discovery = Interval::new(Instant::now(), Duration::from_secs(32))
		// TODO: add a timeout to the lookups
		.map_err(|err| IoError::new(IoErrorKind::Other, err))
		.and_then({
			let shared = shared.clone();
			let transport = transport.clone();
			let swarm_controller = swarm_controller.clone();
			move |_| {
				// Note that this is a small hack. We flush the caches here so
				// that we don't need to run a timer just for flushing.
				let _ = shared.network_state.flush_caches_to_disk();

				if shared.network_state.should_open_outgoing_custom_connections() != 0 {
					future::Either::A(perform_kademlia_query(shared.clone(),
						transport.clone(), swarm_controller.clone()))
				} else {
					// If we shouldn't open connections (eg. we reached
					// `min_peers`), pretend we did a lookup but with an empty
					// result.
					trace!(target: "sub-libp2p", "Bypassing kademlia discovery");
					future::Either::B(future::ok(()))
				}
			}
		})
		.for_each({
			let shared = shared.clone();
			move |_| {
				connect_to_nodes(shared.clone(), transport.clone(), &swarm_controller);
				Ok(())
			}
		});

	let final_future = kad_init
		.select(discovery)
		.map_err(|(err, _)| err)
		.and_then(|(_, rest)| rest);

	// Note that we use a Box in order to speed compilation time.
	Box::new(final_future) as Box<Future<Item = _, Error = _>>
}

/// Performs a kademlia request to a random node.
/// Note that we don't actually care about the results, so the future
/// produces `()`.
fn perform_kademlia_query<T, To, St, C>(
	shared: Arc<Shared>,
	transport: T,
	swarm_controller: SwarmController<St>
) -> impl Future<Item = (), Error = IoError>
	where T: MuxedTransport<Output =  TransportOutput<To>> + Clone + 'static,
		T::MultiaddrFuture: 'static,
		To: AsyncRead + AsyncWrite + 'static,
		St: MuxedTransport<Output = FinalUpgrade<C>> + Clone + 'static,
		C: 'static {
	// Query the node IDs that are closest to a random ID.
	// Note that the randomness doesn't have to be secure, as this only
	// influences which nodes we end up being connected to.
	let random_key = PublicKey::Ed25519((0 .. 32)
		.map(|_| -> u8 { rand::random() }).collect());
	let random_peer_id = random_key.into_peer_id();
	trace!(target: "sub-libp2p", "Start kademlia discovery for {:?}", random_peer_id);

	let future = shared.clone()
		.kad_system
		.find_node(random_peer_id, {
			let shared = shared.clone();
			let transport = transport.clone();
			let swarm_controller = swarm_controller.clone();
			move |who| obtain_kad_connection(shared.clone(), who.clone(),
				transport.clone(), swarm_controller.clone())
		})
		.filter_map(move |event|
			match event {
				KadQueryEvent::NewKnownMultiaddrs(peers) => {
					for (peer, addrs) in peers {
						for addr in addrs {
							shared.network_state.add_kad_discovered_addr(&peer, addr);
						}
					}
					None
				},
				KadQueryEvent::Finished(_) => Some(()),
			}
		)
		.into_future()
		.map_err(|(err, _)| err)
		.map(|_| ());

	// Note that we use a `Box` in order to speed up compilation.
	Box::new(future) as Box<Future<Item = _, Error = _>>
}

/// Connects to additional nodes, if necessary.
fn connect_to_nodes<T, To, St, C>(
	shared: Arc<Shared>,
	base_transport: T,
	swarm_controller: &SwarmController<St>
)
	where T: MuxedTransport<Output =  TransportOutput<To>> + Clone + 'static,
		T::MultiaddrFuture: 'static,
		To: AsyncRead + AsyncWrite + 'static,
		St: MuxedTransport<Output = FinalUpgrade<C>> + Clone + 'static,
		C: 'static {
	let num_slots = shared.network_state.should_open_outgoing_custom_connections();
	debug!(target: "sub-libp2p",
		"Outgoing connections cycle ; opening up to {} outgoing connections",
		num_slots
	);

	for _ in 0 .. num_slots {
		// Choose a random peer. We are potentially already connected to
		// this peer, but this is not a problem as this function is called
		// regularly.
		// TODO: is it ^ ?
		let peer = match shared.network_state.random_peer() {
			Some(p) => p,
			// `None` returned when no peer is known
			None => break,
		};

		// Try to dial that node for each registered protocol. Since dialing
		// upgrades the connection to use multiplexing, dialing multiple times
		// should automatically open multiple substreams.
		for proto in shared.protocols.read().0.clone().into_iter() {
			open_peer_custom_proto(
				shared.clone(),
				base_transport.clone(),
				proto,
				peer.clone(),
				swarm_controller
			)
		}
	}
}


fn connect_with_query_peer_id<T, To, St, C>(
	shared: Arc<Shared>,
	base_transport: T,
	proto: RegisteredProtocol<Arc<NetworkProtocolHandler + Send + Sync>>,
	addr: Multiaddr,
	swarm_controller: &SwarmController<St>
)
	where T: MuxedTransport<Output =  TransportOutput<To>> + Clone + 'static,
		T::MultiaddrFuture: 'static,
		To: AsyncRead + AsyncWrite + 'static,
		St: MuxedTransport<Output = FinalUpgrade<C>> + Clone + 'static,
		C: 'static,
{
	let addr2 = addr.clone();
	let with_proto = base_transport
		.clone()
		.and_then(move |out, endpoint, client_addr| {
			trace!(target: "sub-libp2p", "in");
			let socket = out.socket;
			let original_addr = out.original_addr;
			out.info
				.and_then(move |info| {
					let _ = process_identify_info(shared, &info, original_addr,
						endpoint, &base_transport);
					trace!(target: "sub-libp2p",
						"Bootnode {:} found with peer id: {:?}",
						addr2,
						info.info.public_key.into_peer_id()
					);
					upgrade::apply(socket, proto, endpoint, client_addr)
				})
		})
		.and_then(move |out, _endpoint, client_addr|
			client_addr.map(move |client_addr|
				(FinalUpgrade::Custom(out, client_addr.clone()), future::ok(client_addr))
			)
		);
	
	let with_timeout = TransportTimeout::new(with_proto, Duration::from_secs(10));
	let with_err = with_timeout
		.map_err({
			let addr = addr.clone();
			move |err| {
				warn!(target: "sub-libp2p",
					"Error while dialing {:?} to query peer id: {:?}",
					addr,
					err
				);
				err
			}
		});

	let _ = swarm_controller.dial(addr.clone(), with_err)
		.map_err(move |err|
			warn!(target: "sub-libp2p", "Error when querying peer node info {:} of {:}", err, addr)
		);
}

/// If necessary, dials the given address for the given protocol and using the
/// given `swarm_controller`. Has no effect if we already dialed earlier.
/// Checks that the peer ID matches `expected_peer_id`.
// TODO: check that the secio key matches the id given by kademlia
fn open_peer_custom_proto<T, To, St, C>(
	shared: Arc<Shared>,
	base_transport: T,
	proto: RegisteredProtocol<Arc<NetworkProtocolHandler + Send + Sync>>,
	expected_peer_id: PeerstorePeerId,
	swarm_controller: &SwarmController<St>
)
	where T: MuxedTransport<Output =  TransportOutput<To>> + Clone + 'static,
		T::MultiaddrFuture: 'static,
		To: AsyncRead + AsyncWrite + 'static,
		St: MuxedTransport<Output = FinalUpgrade<C>> + Clone + 'static,
		C: 'static,
{
	// Don't connect to ourselves.
	// TODO: remove this eventually
	if &expected_peer_id == shared.kad_system.local_peer_id() {
		trace!(target: "sub-libp2p", "Skipped connecting to {:?} because it is ourselves", expected_peer_id);
		return
	}

	let proto_id = proto.id();
	let node_id = expected_peer_id.clone();
	let shared2 = shared.clone();
	let addr: Multiaddr = AddrComponent::P2P(expected_peer_id.clone().into_bytes()).into();

	// TODO: check that the secio key matches the id given by kademlia
	let with_proto = base_transport
		.clone()
		.and_then(move |out, endpoint, client_addr| {
			let socket = out.socket;
			let original_addr = out.original_addr;
			out.info
				.and_then(move |info| {
					let actual_peer_id = info.info.public_key.into_peer_id();
					if actual_peer_id == expected_peer_id {
						Ok(socket)
					} else {
						debug!(target: "sub-libp2p",
							"Public key mismatch for node {:?} ; actual: {:?}",
							expected_peer_id,
							actual_peer_id
						);
						trace!(target: "sub-libp2p", "Removing addr {} for {:?}", original_addr, expected_peer_id);
						shared.network_state.set_invalid_kad_address(&expected_peer_id, &original_addr);
						Err(IoError::new(IoErrorKind::InvalidData, "public key mismatch when identifying peer"))
					}
				})
				.and_then(move |socket|
					upgrade::apply(socket, proto, endpoint, client_addr)
				)
		})
		.and_then(move |out, _endpoint, client_addr|
			client_addr.map(move |client_addr| {
				let out = FinalUpgrade::Custom(out, client_addr.clone());
				(out, future::ok(client_addr))
			})
		);
	
	let with_timeout = TransportTimeout::new(with_proto,
		Duration::from_secs(20));
	let with_err = with_timeout
		.map_err({
			let node_id = node_id.clone();
			move |err| {
				debug!(target: "sub-libp2p", "Error while dialing {:?} with custom proto: {:?}", node_id, err);
				err
			}
		});

	match shared2.network_state.custom_proto(node_id.clone(), proto_id, Endpoint::Dialer) {
		Ok((who, unique_connec)) => {
			if !unique_connec.is_alive() {
				trace!(target: "sub-libp2p",
					"Opening connection to #{} {:?} with proto {:?}",
					who,
					node_id,
					proto_id
				);
			}

			unique_connec.dial(&swarm_controller, &addr, with_err);
		},
		Err(err) => {
			trace!(target: "sub-libp2p",
				"Error while opening connection to {:?} with proto {:?} => {:?}",
				node_id,
				proto_id,
				err
			);
		},
	}
}

/// Obtain a Kademlia connection to the given peer.
fn obtain_kad_connection<T, To, St, C>(shared: Arc<Shared>,
	who: PeerstorePeerId, transport: T, swarm_controller: SwarmController<St>)
	-> impl Future<Item = KadConnecController, Error = IoError>
	where T: MuxedTransport<Output =  TransportOutput<To>> + Clone + 'static,
		T::MultiaddrFuture: 'static,
		To: AsyncRead + AsyncWrite + 'static,
		St: MuxedTransport<Output = FinalUpgrade<C>> + Clone + 'static,
		C: 'static {
	let kad_upgrade = shared.kad_upgrade.clone();
	let addr: Multiaddr = AddrComponent::P2P(who.clone().into_bytes()).into();
	let transport = transport
		.and_then(move |out, endpoint, client_addr|
			upgrade::apply(out.socket, kad_upgrade.clone(),
				endpoint, client_addr)
		)
		.and_then(move |(ctrl, fut), _, client_addr| {
			client_addr.map(|client_addr| {
				let out = FinalUpgrade::Kad(ctrl, fut, client_addr.clone());
				(out, future::ok(client_addr))
			})
		});
	
	let future = shared.network_state
		.kad_connection(who.clone())
		.into_future()
		.map(move |(_, k)| k.dial(&swarm_controller, &addr, transport))
		.flatten();

	// Note that we use a Box in order to speed up compilation.
	Box::new(future) as Box<Future<Item = _, Error = _>>
}

/// Processes the information about a node.
///
/// - `original_addr` is the address used to originally dial this node.
/// - `endpoint` is whether we dialed or listened to this node.
/// - `transport` is used for the `nat_traversal` method.
///
/// Returns an error if the node has been refused access.
fn process_identify_info(
	shared: Arc<Shared>,
	info: &IdentifyTransportOutcome,
	original_addr: Multiaddr,
	endpoint: Endpoint,
	transport: &impl Transport
) -> Result<(), IoError> {
	let node_id = info.info.public_key.clone().into_peer_id();
	let _peer_id = shared.network_state.set_peer_info(node_id.clone(), endpoint,
		info.info.agent_version.clone(), original_addr.clone(),
		original_addr.clone())?;	// TODO: wrong local addr

	if let Some(ref original_listened_addr) = *shared.original_listened_addr.read() {
		if let Some(mut ext_addr) = transport.nat_traversal(original_listened_addr, &info.observed_addr) {
			let mut listened_addrs = shared.listened_addrs.write();
			if !listened_addrs.iter().any(|a| a == &ext_addr) {
				trace!(target: "sub-libp2p",
					"NAT traversal: remote observes us as {}; registering {} as one of our own addresses",
					info.observed_addr,
					ext_addr
				);
				listened_addrs.push(ext_addr.clone());
				ext_addr.append(AddrComponent::P2P(shared.kad_system
					.local_peer_id().clone().into_bytes()));
				info!(target: "sub-libp2p", "New external node address: {}", ext_addr);
			}
		}
	}

	for addr in info.info.listen_addrs.iter() {
		shared.network_state.add_kad_discovered_addr(&node_id, addr.clone());
	}

	Ok(())
}

/// Returns a future that regularly pings every peer we're connected to.
/// If a peer doesn't respond after a while, we disconnect it.
fn start_pinger<T, To, St, C>(
	shared: Arc<Shared>,
	transport: T,
	swarm_controller: SwarmController<St>
) -> impl Future<Item = (), Error = IoError>
	where T: MuxedTransport<Output = TransportOutput<To>> + Clone + 'static,
		T::MultiaddrFuture: 'static,
		To: AsyncRead + AsyncWrite + 'static,
		St: MuxedTransport<Output = FinalUpgrade<C>> + Clone + 'static,
		C: 'static {
	let transport = transport
		.and_then(move |out, endpoint, client_addr|
			upgrade::apply(out.socket, ping::Ping, endpoint, client_addr)
		)
		.and_then(move |(ctrl, fut), _, client_addr| {
			client_addr.map(|client_addr| {
				let out = FinalUpgrade::Ping(ctrl, fut, client_addr.clone());
				(out, future::ok(client_addr))
			})
		});

	let fut = Interval::new(Instant::now(), Duration::from_secs(30))
		.map_err(|err| IoError::new(IoErrorKind::Other, err))
		.for_each(move |_|
			ping_all(shared.clone(), transport.clone(), &swarm_controller))
		.then(|val| {
			warn!(target: "sub-libp2p", "Pinging stream has stopped: {:?}", val);
			val
		});

	// Note that we use a Box in order to speed compilation time.
	Box::new(fut) as Box<Future<Item = _, Error = _>>
}

/// Pings all the nodes we're connected to and disconnects any node that
/// doesn't respond. Returns a `Future` when all the pings have either
/// suceeded or timed out.
fn ping_all<T, St, C>(
	shared: Arc<Shared>,
	transport: T,
	swarm_controller: &SwarmController<St>
) -> impl Future<Item = (), Error = IoError>
	where T: MuxedTransport<Output = FinalUpgrade<C>> + Clone + 'static,
		T::MultiaddrFuture: 'static,
		St: MuxedTransport<Output = FinalUpgrade<C>> + Clone + 'static,
		C: 'static {
	let mut ping_futures = Vec::new();

	for (peer, who, pinger) in shared.network_state.cleanup_and_prepare_ping() {
		let shared = shared.clone();

		let addr = Multiaddr::from(AddrComponent::P2P(who.clone().into_bytes()));
		let fut = pinger
			.dial(&swarm_controller, &addr, transport.clone())
			.and_then(move |mut p| {
				trace!(target: "sub-libp2p", "Pinging peer #{} aka. {:?}", peer, who);
				p.ping()
					.map(|()| who)
					.map_err(|err| IoError::new(IoErrorKind::Other, err))
			});
		let ping_start_time = Instant::now();
		let fut = Deadline::new(fut, ping_start_time + Duration::from_secs(30))
			.then(move |val|
				match val {
					Err(err) => {
						trace!(target: "sub-libp2p", "Error while pinging #{:?} => {:?}", peer, err);
						shared.network_state.report_ping_failed(peer);
						// Return Ok, otherwise we would close the ping service
						Ok(())
					},
					Ok(who) => {
						let elapsed = ping_start_time.elapsed();
						trace!(target: "sub-libp2p", "Pong from #{:?} in {:?}", peer, elapsed);
						shared.network_state.report_ping_duration(peer, elapsed);
						shared.kad_system.update_kbuckets(who);
						Ok(())
					}
				}
			);
		ping_futures.push(fut);
	}

	let future = future::loop_fn(ping_futures, |ping_futures| {
		if ping_futures.is_empty() {
			let fut = future::ok(future::Loop::Break(()));
			return future::Either::A(fut)
		}

		let fut = future::select_all(ping_futures)
			.map(|((), _, rest)| future::Loop::Continue(rest))
			.map_err(|(err, _, _)| err);
		future::Either::B(fut)
	});

	// Note that we use a Box in order to speed up compilation.
	Box::new(future) as Box<Future<Item = _, Error = _>>
}

/// Expects a multiaddr of the format `/p2p/<node_id>` and returns the node ID.
/// Panics if the format is not correct.
fn p2p_multiaddr_to_node_id(client_addr: Multiaddr) -> PeerstorePeerId {
	let (first, second);
	{
		let mut iter = client_addr.iter();
		first = iter.next();
		second = iter.next();
	}
	match (first, second) {
		(Some(AddrComponent::P2P(node_id)), None) =>
			PeerstorePeerId::from_bytes(node_id).expect("libp2p always reports a valid node id"),
		_ => panic!("Reported multiaddress is in the wrong format ; programmer error")
	}
}

/// Since new protocols are added after the networking starts, we have to load the protocols list
/// in a lazy way. This is what this wrapper does.
#[derive(Clone)]
struct DelayedProtosList(Arc<Shared>);
// `Maf` is short for `MultiaddressFuture`
impl<C, Maf> ConnectionUpgrade<C, Maf> for DelayedProtosList
where C: AsyncRead + AsyncWrite + 'static,		// TODO: 'static :-/
	Maf: Future<Item = Multiaddr, Error = IoError> + 'static,		// TODO: 'static :(
{
	type NamesIter = <RegisteredProtocols<Arc<NetworkProtocolHandler + Send + Sync>> as ConnectionUpgrade<C, Maf>>::NamesIter;
	type UpgradeIdentifier = <RegisteredProtocols<Arc<NetworkProtocolHandler + Send + Sync>> as ConnectionUpgrade<C, Maf>>::UpgradeIdentifier;

	fn protocol_names(&self) -> Self::NamesIter {
		ConnectionUpgrade::<C, Maf>::protocol_names(&*self.0.protocols.read())
	}

	type Output = <RegisteredProtocols<Arc<NetworkProtocolHandler + Send + Sync>> as ConnectionUpgrade<C, Maf>>::Output;
	type MultiaddrFuture = <RegisteredProtocols<Arc<NetworkProtocolHandler + Send + Sync>> as ConnectionUpgrade<C, Maf>>::MultiaddrFuture;
	type Future = <RegisteredProtocols<Arc<NetworkProtocolHandler + Send + Sync>> as ConnectionUpgrade<C, Maf>>::Future;

	#[inline]
	fn upgrade(self, socket: C, id: Self::UpgradeIdentifier, endpoint: Endpoint,
		remote_addr: Maf) -> Self::Future
	{
		self.0.protocols.read()
			.clone()
			.upgrade(socket, id, endpoint, remote_addr)
	}
}

#[cfg(test)]
mod tests {
	use super::NetworkService;

	#[test]
	fn builds_and_finishes_in_finite_time() {
		// Checks that merely starting the network doesn't end up in an infinite loop.
		let service = NetworkService::new(Default::default(), None).unwrap();
		service.start(vec![]).map_err(|(err, _)| err).unwrap();
	}
}
