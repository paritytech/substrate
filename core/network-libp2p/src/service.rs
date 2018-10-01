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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use fnv::FnvHashMap;
use parking_lot::Mutex;
use libp2p::core::{nodes::swarm::ConnectedPoint, Multiaddr, PeerId as PeerstorePeerId};
use libp2p::multiaddr::Protocol;
use {PacketId, SessionInfo, TimerToken};
use service_task::ServiceEvent;
use std::io::{Error as IoError, ErrorKind as IoErrorKind};
use std::sync::Arc;
use std::sync::mpsc as sync_mpsc;
use std::thread;
use std::time::Duration;
use futures::{prelude::*, Future, stream, Stream, select_all};
use futures::sync::{mpsc, oneshot};
use tokio::runtime::current_thread;
use {Error, ErrorKind, NetworkConfiguration, NetworkProtocolHandler, parse_str_addr};
use {NonReservedPeerMode, NetworkContext, Severity, NodeIndex, ProtocolId};

use custom_proto::{RegisteredProtocol, RegisteredProtocols};
use service_task::start_service;
use timeouts;

/// IO Service with networking.
pub struct NetworkService {
	/// Information about peers.
	peer_infos: Arc<Mutex<FnvHashMap<NodeIndex, PeerInfos>>>,

	/// Use this channel to send a timeout request to the background thread's
	/// events loop. After the timeout, elapsed, it will call `timeout` on the
	/// `NetworkProtocolHandler`.
	timeouts_register_tx: mpsc::UnboundedSender<(Duration, (Arc<NetworkProtocolHandler + Send + Sync>, ProtocolId, TimerToken))>,

	/// Sender for messages to send to the background thread.
	msg_tx: mpsc::UnboundedSender<MsgToBgThread>,

	/// Sender for messages to the backgound service task, and handle for the background thread.
	/// Dropping the sender should close the task and the thread.
	bg_thread: Option<(oneshot::Sender<()>, thread::JoinHandle<()>)>,

	/// Original configuration of the service.
	config: NetworkConfiguration,

	/// List of registered protocols.
	registered_custom: Arc<RegisteredProtocols<Arc<NetworkProtocolHandler + Send + Sync>>>,

	/// The external URL to report to the user.
	external_url: Option<String>,
}

/// Known information about a peer.
struct PeerInfos {
	/// Id of the peer.
	id: PeerstorePeerId,

	/// List of open custom protocols, and their version.
	protocols: Vec<(ProtocolId, u8)>,

	/// How we are connected to the remote.
	endpoint: ConnectedPoint,

	/// Latest known ping duration.
	ping: Option<Duration>,

	/// The client version of the remote, or `None` if not known.
	client_version: Option<String>,

	/// The local multiaddress used to communicate with the remote, or `None`
	/// if not known.
	// TODO: never filled ; also shouldn't be an `Option`
	local_address: Option<Multiaddr>,
}

/// Message to send to the service task.
#[derive(Debug, Clone)]
enum MsgToBgThread {
	/// Call `add_reserved_peer` on the network service.
	AddReservedPeer(PeerstorePeerId, Multiaddr),
	/// Call `remove_reserved_peer` on the network service.
	RemoveReservedPeer(PeerstorePeerId, Multiaddr),
	/// Call `set_non_reserved_mode` on the network service.
	SetNonReserved(NonReservedPeerMode),
	/// Call `send_custom_message` on the network service.
	SendCustomMessage(NodeIndex, ProtocolId, PacketId, Vec<u8>),
	/// Call `drop_peer` on the network service.
	DropNode(NodeIndex),
	/// Call `ban_peer` on the network service.
	BanNode(NodeIndex),
}

impl NetworkService {
	/// Starts the networking service.
	///
	/// Note that we could use an iterator for `protocols`, but having a
	/// generic here is too much and crashes the Rust compiler.
	pub fn new(
		config: NetworkConfiguration,
		protocols: Vec<(Arc<NetworkProtocolHandler + Send + Sync>, ProtocolId, &[(u8, u8)])>
	) -> Result<NetworkService, Error> {
		// Start by creating the protocols list.
		let registered_custom = Arc::new(RegisteredProtocols(protocols.into_iter()
			.map(|(handler, protocol, versions)|
				RegisteredProtocol::new(handler.clone(), protocol, versions))
			.collect()));

		let (init_tx, init_rx) = sync_mpsc::channel();
		let (close_tx, close_rx) = oneshot::channel();
		let (timeouts_register_tx, timeouts_register_rx) = mpsc::unbounded();
		let peer_infos = Arc::new(Mutex::new(Default::default()));
		let timeouts_register_tx_clone = timeouts_register_tx.clone();
		let (msg_tx, msg_rx) = mpsc::unbounded();
		let registered_custom_clone = registered_custom.clone();
		let config_clone = config.clone();
		let peer_infos_clone = peer_infos.clone();
		let msg_tx_clone = msg_tx.clone();

		// Initialize all the protocols now.
		// TODO: remove this `initialize` method eventually, as it's only used for timers
		for protocol in registered_custom.0.iter() {
			protocol.custom_data().initialize(&NetworkContextImpl {
				peer_infos: peer_infos.clone(),
				registered_custom: registered_custom.clone(),
				msg_tx: msg_tx.clone(),
				timeouts_register_tx: timeouts_register_tx.clone(),
				protocol: protocol.id(),
				current_peer: None,
			});
		}

		let join_handle = thread::spawn(move || {
			// Tokio runtime that is going to run everything in this thread.
			let mut runtime = match current_thread::Runtime::new() {
				Ok(c) => c,
				Err(err) => {
					let _ = init_tx.send(Err(err.into()));
					return
				}
			};

			let fut = match init_thread(
				config_clone,
				registered_custom_clone,
				peer_infos_clone,
				timeouts_register_tx_clone,
				timeouts_register_rx,
				msg_tx_clone,
				msg_rx
			) {
				Ok((future, external_url)) => {
					debug!(target: "sub-libp2p", "Successfully started networking service");
					let _ = init_tx.send(Ok(external_url));
					future
				},
				Err(err) => {
					let _ = init_tx.send(Err(err));
					return
				}
			};

			let fut = fut.map_err(|_| ())
				.select(close_rx.then(|_| Ok(())))
				.map(|_| ()).map_err(|_| ());
			match runtime.block_on(fut) {
				Ok(()) => debug!(target: "sub-libp2p", "libp2p future finished"),
				Err(err) => error!(target: "sub-libp2p", "Error while running libp2p: {:?}", err),
			}
		});

		let external_url = init_rx.recv().expect("libp2p background thread panicked")?;

		Ok(NetworkService {
			config,
			peer_infos,
			timeouts_register_tx,
			msg_tx,
			external_url,
			bg_thread: Some((close_tx, join_handle)),
			registered_custom,
		})
	}

	/// Returns network configuration.
	// TODO: is this method really necessary? we could remove the `config` field if not
	pub fn config(&self) -> &NetworkConfiguration {
		&self.config
	}

	pub fn external_url(&self) -> Option<String> {
		// TODO: cleanup this in external API layers
		self.external_url.clone()
	}

	/// Get a list of all connected peers by id.
	pub fn connected_peers(&self) -> Vec<NodeIndex> {
		self.peer_infos.lock().keys().cloned().collect()
	}

	/// Try to add a reserved peer.
	pub fn add_reserved_peer(&self, peer: &str) -> Result<(), Error> {
		let (peer_id, addr) = parse_str_addr(peer)?;
		let _ = self.msg_tx.unbounded_send(MsgToBgThread::AddReservedPeer(peer_id, addr));
		Ok(())
	}

	/// Try to remove a reserved peer.
	pub fn remove_reserved_peer(&self, peer: &str) -> Result<(), Error> {
		let (peer_id, addr) = parse_str_addr(peer)?;
		let _ = self.msg_tx.unbounded_send(MsgToBgThread::RemoveReservedPeer(peer_id, addr));
		Ok(())
	}

	/// Set the non-reserved peer mode.
	pub fn set_non_reserved_mode(&self, mode: NonReservedPeerMode) {
		let _ = self.msg_tx.unbounded_send(MsgToBgThread::SetNonReserved(mode));
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
		if !self.registered_custom.has_protocol(protocol) {
			return None
		}

		Some(action(&NetworkContextImpl {
			peer_infos: self.peer_infos.clone(),
			registered_custom: self.registered_custom.clone(),
			msg_tx: self.msg_tx.clone(),
			timeouts_register_tx: self.timeouts_register_tx.clone(),
			protocol: protocol.clone(),
			current_peer: None,
		}))
	}
}

impl Drop for NetworkService {
	fn drop(&mut self) {
		if let Some((sender, join)) = self.bg_thread.take() {
			drop(sender);
			if let Err(e) = join.join() {
				warn!(target: "sub-libp2p", "error while waiting on libp2p background thread: {:?}", e);
			}
		}
	}
}

/// Builds the main `Future` for the network service.
///
/// Also returns a diagnostic external node address, to report to the user.
fn init_thread(
	config: NetworkConfiguration,
	registered_custom: Arc<RegisteredProtocols<Arc<NetworkProtocolHandler + Send + Sync>>>,
	peers: Arc<Mutex<FnvHashMap<NodeIndex, PeerInfos>>>,
	timeouts_register_tx: mpsc::UnboundedSender<
		(Duration, (Arc<NetworkProtocolHandler + Send + Sync + 'static>, ProtocolId, TimerToken))
	>,
	timeouts_register_rx: mpsc::UnboundedReceiver<
		(Duration, (Arc<NetworkProtocolHandler + Send + Sync + 'static>, ProtocolId, TimerToken))
	>,
	msg_tx: mpsc::UnboundedSender<MsgToBgThread>,
	mut msg_rx: mpsc::UnboundedReceiver<MsgToBgThread>,
) -> Result<(impl Future<Item = (), Error = IoError>, Option<String>), Error> {
	// Build the timeouts system for the `register_timeout` function.
	// (note: this has nothing to do with socket timeouts)
	let timeouts = timeouts::build_timeouts_stream(timeouts_register_rx)
		.for_each({
			let peers = peers.clone();
			let msg_tx = msg_tx.clone();
			let registered_custom = registered_custom.clone();
			let timeouts_register_tx = timeouts_register_tx.clone();
			move |(handler, protocol_id, timer_token)| {
				handler.timeout(&NetworkContextImpl {
					peer_infos: peers.clone(),
					registered_custom: registered_custom.clone(),
					msg_tx: msg_tx.clone(),
					protocol: protocol_id,
					current_peer: None,
					timeouts_register_tx: timeouts_register_tx.clone(),
				}, timer_token);
				Ok(())
			}
		})
		.then(|val| {
			warn!(target: "sub-libp2p", "Timeouts stream closed unexpectedly: {:?}", val);
			val
		});

	// Start the main service.
	let mut service = start_service(config, registered_custom.clone())?;

	// Build the external URL to report to the user.
	let external_url = service
		.listeners()
		.next()
		.map(|addr| {
			let mut addr = addr.clone();
			addr.append(Protocol::P2p(service.peer_id().clone().into()));
			addr.to_string()
		});

	let service_stream = stream::poll_fn(move || {
		loop {
			match msg_rx.poll() {
				Ok(Async::NotReady) => break,
				Ok(Async::Ready(None)) => return Ok(Async::Ready(None)),
				Ok(Async::Ready(Some(MsgToBgThread::AddReservedPeer(peer_id, addr)))) => {
					service.add_reserved_peer(peer_id, addr);
				},
				Ok(Async::Ready(Some(MsgToBgThread::RemoveReservedPeer(peer_id, addr)))) => {
					service.remove_reserved_peer(peer_id, addr);
				},
				Ok(Async::Ready(Some(MsgToBgThread::SetNonReserved(mode)))) => {
					service.set_non_reserved_mode(mode);
				},
				Ok(Async::Ready(Some(MsgToBgThread::SendCustomMessage(node_index, protocol_id, packet_id, data)))) => {
					service.send_custom_message(node_index, protocol_id, packet_id, data);
				},
				Ok(Async::Ready(Some(MsgToBgThread::DropNode(node_index)))) => {
					service.drop_node(node_index);
				},
				Ok(Async::Ready(Some(MsgToBgThread::BanNode(node_index)))) => {
					service.ban_node(node_index);
				},
				Err(()) => unreachable!("An unbounded receiver never errors"),
			}
		}

		service.poll()
	})
	.for_each(move |event| {
		macro_rules! ctxt {
			($protocol:expr, $node_index:expr) => (
				NetworkContextImpl {
					peer_infos: peers.clone(),
					registered_custom: registered_custom.clone(),
					msg_tx: msg_tx.clone(),
					timeouts_register_tx: timeouts_register_tx.clone(),
					protocol: $protocol,
					current_peer: Some($node_index),
				}
			);
		}

		match event {
			ServiceEvent::NewNode { node_index, peer_id, endpoint } => {
				peers.lock().insert(node_index, PeerInfos {
					id: peer_id,
					protocols: Vec::new(),
					endpoint,
					ping: None,
					client_version: None,
					local_address: None,	// TODO: fill
				});
			},
			ServiceEvent::NodeClosed { node_index, closed_custom_protocols } => {
				let old = peers.lock().remove(&node_index);
				debug_assert!(old.is_some());
				for protocol in closed_custom_protocols {
					registered_custom.find_protocol(protocol)
					.expect("we passed a list of protocols when building the service, and never \
						modify that list ; therefore all the reported ids should always be valid")
						.custom_data()
						.disconnected(&ctxt!(protocol, node_index), &node_index);
				}
			},
			ServiceEvent::ClosedCustomProtocols { node_index, protocols } => {
				peers.lock().get_mut(&node_index)
					.expect("peers is kept in sync with the state in the service")
					.protocols
					.retain(|&(ref p, _)| !protocols.iter().any(|pr| pr == p));
				for protocol in protocols {
					registered_custom.find_protocol(protocol)
					.expect("we passed a list of protocols when building the service, and never \
						modify that list ; therefore all the reported ids should always be valid")
						.custom_data()
						.disconnected(&ctxt!(protocol, node_index), &node_index);
				}
			},
			ServiceEvent::PingDuration(node_index, ping) =>
				peers.lock().get_mut(&node_index)
					.expect("peers is kept in sync with the state in the service")
					.ping = Some(ping),
			ServiceEvent::NodeInfos { node_index, client_version } =>
				peers.lock().get_mut(&node_index)
					.expect("peers is kept in sync with the state in the service")
					.client_version = Some(client_version),
			ServiceEvent::OpenedCustomProtocol { node_index, protocol, version } => {
				peers.lock().get_mut(&node_index)
					.expect("peers is kept in sync with the state in the service")
					.protocols
					.push((protocol, version));
				registered_custom.find_protocol(protocol)
					.expect("we passed a list of protocols when building the service, and never \
						modify that list ; therefore all the reported ids should always be valid")
					.custom_data()
					.connected(&ctxt!(protocol, node_index), &node_index)
			},
			ServiceEvent::ClosedCustomProtocol { node_index, protocol } => {
				peers.lock().get_mut(&node_index)
					.expect("peers is kept in sync with the state in the service")
					.protocols
					.retain(|&(ref p, _)| p != &protocol);
				registered_custom.find_protocol(protocol)
					.expect("we passed a list of protocols when building the service, and never \
						modify that list ; therefore all the reported ids should always be valid")
					.custom_data()
					.disconnected(&ctxt!(protocol, node_index), &node_index)
			},
			ServiceEvent::CustomMessage { node_index, protocol_id, packet_id, data } => {
				registered_custom.find_protocol(protocol_id)
					.expect("we passed a list of protocols when building the service, and never \
						modify that list ; therefore all the reported ids should always be valid")
					.custom_data()
					.read(&ctxt!(protocol_id, node_index), &node_index, packet_id, &data)
			},
		};
		Ok(())
	});

	// Merge all futures into one.
	let futures: Vec<Box<Future<Item = (), Error = IoError>>> = vec![
		Box::new(service_stream),
		Box::new(timeouts),
	];
	let final_future = select_all(futures)
		.and_then(move |_| {
			debug!(target: "sub-libp2p", "Networking ended");
			Ok(())
		})
		.map_err(|(r, _, _)| r);
	
	Ok((final_future, external_url))
}

#[derive(Clone)]
struct NetworkContextImpl {
	peer_infos: Arc<Mutex<FnvHashMap<NodeIndex, PeerInfos>>>,
	msg_tx: mpsc::UnboundedSender<MsgToBgThread>,
	protocol: ProtocolId,
	current_peer: Option<NodeIndex>,
	registered_custom: Arc<RegisteredProtocols<Arc<NetworkProtocolHandler + Send + Sync>>>,
	/// Clone of `NetworkService::timeouts_register_tx`.
	timeouts_register_tx: mpsc::UnboundedSender<(Duration, (Arc<NetworkProtocolHandler + Send + Sync>, ProtocolId, TimerToken))>,
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
		let msg = MsgToBgThread::SendCustomMessage(peer, protocol, packet_id, data);
		let _ = self.msg_tx.unbounded_send(msg);
	}

	fn respond(&self, packet_id: PacketId, data: Vec<u8>) {
		if let Some(peer) = self.current_peer {
			self.send_protocol(self.protocol, peer, packet_id, data)
		} else {
			panic!("respond() called outside of a received message");
		}
	}

	fn report_peer(&self, node_index: NodeIndex, reason: Severity) {
		let peer_infos = self.peer_infos.lock();
		if let Some(info) = peer_infos.get(&node_index) {
			if let Some(ref client_version) = info.client_version {
				info!(target: "sub-libp2p",
					"Peer {:?} ({:?} {}) reported by client: {}",
					info.id,
					info.endpoint,
					client_version,
					reason
				);
			} else {
				info!(target: "sub-libp2p", "Peer {:?} reported by client: {}", info.id, reason);
			}
		}

		let _ = self.msg_tx.unbounded_send(match reason {
			Severity::Bad(_) => MsgToBgThread::BanNode(node_index),
			Severity::Useless(_) => MsgToBgThread::DropNode(node_index),
			Severity::Timeout => MsgToBgThread::DropNode(node_index),
		});
	}

	fn is_expired(&self) -> bool {
		let peer_infos = self.peer_infos.lock();
		let current_peer = self.current_peer.as_ref()
			.expect("Called is_expired outside of a context");
		!peer_infos.contains_key(current_peer)
	}

	fn register_timer(&self, token: usize, duration: Duration)
		-> Result<(), Error> {
		let handler = self.registered_custom
			.find_protocol(self.protocol)
			.ok_or(ErrorKind::BadProtocol)?
			.custom_data()
			.clone();
		self.timeouts_register_tx
			.unbounded_send((duration, (handler, self.protocol, token)))
			.map_err(|err| ErrorKind::Io(IoError::new(IoErrorKind::Other, err)))?;
		Ok(())
	}

	fn peer_client_version(&self, peer: NodeIndex) -> String {
		// Devp2p returns "unknown" on unknown peer ID, so we do the same.
		// TODO: implement more directly, without going through `session_info`
		self.session_info(peer)
			.map(|info| info.client_version)
			.unwrap_or_else(|| "unknown".to_string())
	}

	fn session_info(&self, peer: NodeIndex) -> Option<SessionInfo> {
		let peer_infos = self.peer_infos.lock();
		let info = match peer_infos.get(&peer) {
			Some(info) => info,
			None => return None,
		};

		let protocol_id = self.protocol;
		let protocol_version = match info.protocols.iter().find(|&(ref p, _)| p == &protocol_id) {
			Some(&(_, vers)) => vers,
			None => return None,
		};

		Some(SessionInfo {
			id: info.id.clone(),
			client_version: info.client_version.clone().take().unwrap_or(String::new()),
			protocol_version: From::from(protocol_version),
			capabilities: Vec::new(),		// TODO: list of supported protocols ; hard
			peer_capabilities: Vec::new(),	// TODO: difference with `peer_capabilities`?
			ping: info.ping,
			originated: if let ConnectedPoint::Dialer { .. } = info.endpoint { true } else { false },
			remote_address: String::new(),		// TODO:
			local_address: info.local_address.as_ref().map(|a| a.to_string())
				.unwrap_or(String::new()),
		})
	}

	fn protocol_version(&self, protocol: ProtocolId, peer: NodeIndex) -> Option<u8> {
		let peer_infos = self.peer_infos.lock();
		let info = match peer_infos.get(&peer) {
			Some(info) => info,
			None => return None,
		};

		let protocol_version = match info.protocols.iter().find(|&(ref p, _)| p == &protocol) {
			Some(&(_, vers)) => vers,
			None => return None,
		};

		Some(protocol_version)
	}

	fn subprotocol_name(&self) -> ProtocolId {
		self.protocol.clone()
	}
}

#[cfg(test)]
mod tests {
	use super::NetworkService;

	#[test]
	fn builds_and_finishes_in_finite_time() {
		// Checks that merely starting the network doesn't end up in an infinite loop.
		let _service = NetworkService::new(Default::default(), vec![]).unwrap();
	}
}
