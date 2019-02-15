// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

use std::collections::HashMap;
use std::sync::Arc;
use std::{io, thread};
use log::{warn, debug, error, trace};
use futures::{Async, Future, Stream, stream, sync::oneshot};
use parking_lot::Mutex;
use network_libp2p::{ProtocolId, PeerId, NetworkConfiguration, NodeIndex, ErrorKind, Severity};
use network_libp2p::{start_service, parse_str_addr, Service as NetworkService, ServiceEvent as NetworkServiceEvent};
use network_libp2p::{Protocol as Libp2pProtocol, RegisteredProtocol};
use consensus::import_queue::{ImportQueue, Link};
use crate::consensus_gossip::ConsensusGossip;
use crate::message::Message;
use crate::protocol::{self, Context, Protocol, ProtocolMsg, ProtocolStatus, PeerInfo};
use crate::config::Params;
use crossbeam_channel::{self as channel, Receiver, Sender, TryRecvError};
use crate::error::Error;
use runtime_primitives::traits::{Block as BlockT, NumberFor};
use crate::specialization::NetworkSpecialization;

use tokio::prelude::task::AtomicTask;
use tokio::runtime::Runtime;

/// Type that represents fetch completion future.
pub type FetchFuture = oneshot::Receiver<Vec<u8>>;

/// Sync status
pub trait SyncProvider<B: BlockT>: Send + Sync {
	/// Get sync status
	fn status(&self) -> ProtocolStatus<B>;
	/// Get currently connected peers
	fn peers(&self) -> Vec<(NodeIndex, Option<PeerId>, PeerInfo<B>)>;
}

/// Minimum Requirements for a Hash within Networking
pub trait ExHashT:
	::std::hash::Hash + Eq + ::std::fmt::Debug + Clone + Send + Sync + 'static
{
}
impl<T> ExHashT for T where
	T: ::std::hash::Hash + Eq + ::std::fmt::Debug + Clone + Send + Sync + 'static
{
}

/// Transaction pool interface
pub trait TransactionPool<H: ExHashT, B: BlockT>: Send + Sync {
	/// Get transactions from the pool that are ready to be propagated.
	fn transactions(&self) -> Vec<(H, B::Extrinsic)>;
	/// Import a transaction into the pool.
	fn import(&self, transaction: &B::Extrinsic) -> Option<H>;
	/// Notify the pool about transactions broadcast.
	fn on_broadcasted(&self, propagations: HashMap<H, Vec<String>>);
}

/// A link implementation that connects to the network.
pub struct NetworkLink<B: BlockT, S: NetworkSpecialization<B>> {
	/// The protocol sender
	pub(crate) protocol_sender: Sender<ProtocolMsg<B, S>>,
	/// The network sender
	pub(crate) network_sender: NetworkChan<B>,
}

impl<B: BlockT, S: NetworkSpecialization<B>> Link<B> for NetworkLink<B, S> {
	fn block_imported(&self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self.protocol_sender.send(ProtocolMsg::BlockImportedSync(hash.clone(), number));
	}

	fn justification_imported(&self, who: NodeIndex, hash: &B::Hash, number: NumberFor<B>, success: bool) {
		let _ = self.protocol_sender.send(ProtocolMsg::JustificationImportResult(hash.clone(), number, success));
		if !success {
			let reason = Severity::Bad(format!("Invalid justification provided for #{}", hash).to_string());
			let _ = self.network_sender.send(NetworkMsg::ReportPeer(who, reason));
		}
	}

	fn request_justification(&self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self.protocol_sender.send(ProtocolMsg::RequestJustification(hash.clone(), number));
	}

	fn maintain_sync(&self) {
		let _ = self.protocol_sender.send(ProtocolMsg::MaintainSync);
	}

	fn useless_peer(&self, who: NodeIndex, reason: &str) {
		trace!(target:"sync", "Useless peer {}, {}", who, reason);
		self.network_sender.send(NetworkMsg::ReportPeer(who, Severity::Useless(reason.to_string())));
	}

	fn note_useless_and_restart_sync(&self, who: NodeIndex, reason: &str) {
		trace!(target:"sync", "Bad peer {}, {}", who, reason);
		// is this actually malign or just useless?
		self.network_sender.send(NetworkMsg::ReportPeer(who, Severity::Useless(reason.to_string())));
		let _ = self.protocol_sender.send(ProtocolMsg::RestartSync);
	}

	fn restart(&self) {
		let _ = self.protocol_sender.send(ProtocolMsg::RestartSync);
	}
}

/// Substrate network service. Handles network IO and manages connectivity.
pub struct Service<B: BlockT + 'static, S: NetworkSpecialization<B>> {
	/// Network service
	network: Arc<Mutex<NetworkService<Message<B>>>>,
	/// Protocol sender
	protocol_sender: Sender<ProtocolMsg<B, S>>,
	/// Sender for messages to the background service task, and handle for the background thread.
	/// Dropping the sender should close the task and the thread.
	/// This is an `Option` because we need to extract it in the destructor.
	bg_thread: Option<(oneshot::Sender<()>, thread::JoinHandle<()>)>,
}

impl<B: BlockT + 'static, S: NetworkSpecialization<B>> Service<B, S> {
	/// Creates and register protocol with the network service
	pub fn new<H: ExHashT>(
		params: Params<B, S, H>,
		protocol_id: ProtocolId,
		import_queue: Box<ImportQueue<B>>,
	) -> Result<(Arc<Service<B, S>>, NetworkChan<B>), Error> {
		let (network_chan, network_port) = network_channel(protocol_id);
		let protocol_sender = Protocol::new(
			network_chan.clone(),
			params.config,
			params.chain,
			import_queue.clone(),
			params.on_demand,
			params.transaction_pool,
			params.specialization,
		)?;
		let versions = [(protocol::CURRENT_VERSION as u8)];
		let registered = RegisteredProtocol::new(protocol_id, &versions[..]);
		let (thread, network) = start_thread(
			protocol_sender.clone(),
			network_port,
			params.network_config,
			registered,
		)?;

		let service = Arc::new(Service {
			network,
			protocol_sender: protocol_sender.clone(),
			bg_thread: Some(thread),
		});

		// connect the import-queue to the network service.
		let link = NetworkLink {
			protocol_sender,
			network_sender: network_chan.clone(),
		};

		import_queue.start(Box::new(link))?;

		Ok((service, network_chan))
	}

	/// Returns the downloaded bytes per second averaged over the past few seconds.
	#[inline]
	pub fn average_download_per_sec(&self) -> u64 {
		self.network.lock().average_download_per_sec()
	}

	/// Returns the uploaded bytes per second averaged over the past few seconds.
	#[inline]
	pub fn average_upload_per_sec(&self) -> u64 {
		self.network.lock().average_upload_per_sec()
	}

	/// Called when a new block is imported by the client.
	pub fn on_block_imported(&self, hash: B::Hash, header: B::Header) {
		let _ = self
			.protocol_sender
			.send(ProtocolMsg::BlockImported(hash, header));
	}

	/// Called when a new block is finalized by the client.
	pub fn on_block_finalized(&self, hash: B::Hash, header: B::Header) {
		let _ = self
			.protocol_sender
			.send(ProtocolMsg::BlockFinalized(hash, header));
	}

	/// Called when new transactons are imported by the client.
	pub fn trigger_repropagate(&self) {
		let _ = self.protocol_sender.send(ProtocolMsg::PropagateExtrinsics);
	}

	/// Make sure an important block is propagated to peers.
	///
	/// In chain-based consensus, we often need to make sure non-best forks are
	/// at least temporarily synced.
	pub fn announce_block(&self, hash: B::Hash) {
		let _ = self.protocol_sender.send(ProtocolMsg::AnnounceBlock(hash));
	}

	/// Send a consensus message through the gossip
	pub fn gossip_consensus_message(&self, topic: B::Hash, message: Vec<u8>, broadcast: bool) {
		let _ = self
			.protocol_sender
			.send(ProtocolMsg::GossipConsensusMessage(
				topic, message, broadcast,
			));
	}

	/// Execute a closure with the chain-specific network specialization.
	pub fn with_spec<F>(&self, f: F)
		where F: FnOnce(&mut S, &mut Context<B>) + Send + 'static
	{
		let _ = self
			.protocol_sender
			.send(ProtocolMsg::ExecuteWithSpec(Box::new(f)));
	}

	/// Execute a closure with the consensus gossip.
	pub fn with_gossip<F>(&self, f: F)
		where F: FnOnce(&mut ConsensusGossip<B>, &mut Context<B>) + Send + 'static
	{
		let _ = self
			.protocol_sender
			.send(ProtocolMsg::ExecuteWithGossip(Box::new(f)));
	}
}

impl<B: BlockT + 'static, S: NetworkSpecialization<B>> ::consensus::SyncOracle for Service<B, S> {
	fn is_major_syncing(&self) -> bool {
		let (sender, port) = channel::unbounded();
		let _ = self
			.protocol_sender
			.send(ProtocolMsg::IsMajorSyncing(sender));
		port.recv().expect("1. Protocol keeps handling messages until all senders are dropped,
			or the ProtocolMsg::Stop message is received,
			2 Service keeps a sender to protocol, and the ProtocolMsg::Stop is never sent.")
	}
	fn is_offline(&self) -> bool {
		let (sender, port) = channel::unbounded();
		let _ = self
			.protocol_sender
			.send(ProtocolMsg::IsOffline(sender));
		port.recv().expect("1. Protocol keeps handling messages until all senders are dropped,
			or the ProtocolMsg::Stop message is received,
			2 Service keeps a sender to protocol, and the ProtocolMsg::Stop is never sent.")
	}
}

impl<B: BlockT + 'static, S: NetworkSpecialization<B>> Drop for Service<B, S> {
	fn drop(&mut self) {
		if let Some((sender, join)) = self.bg_thread.take() {
			let _ = sender.send(());
			if let Err(e) = join.join() {
				error!("Error while waiting on background thread: {:?}", e);
			}
		}
	}
}

impl<B: BlockT + 'static, S: NetworkSpecialization<B>> SyncProvider<B> for Service<B, S> {
	/// Get sync status
	fn status(&self) -> ProtocolStatus<B> {
		let (sender, port) = channel::unbounded();
		let _ = self.protocol_sender.send(ProtocolMsg::Status(sender));
		port.recv().expect("1. Protocol keeps handling messages until all senders are dropped,
			or the ProtocolMsg::Stop message is received,
			2 Service keeps a sender to protocol, and the ProtocolMsg::Stop is never sent.")
	}

	fn peers(&self) -> Vec<(NodeIndex, Option<PeerId>, PeerInfo<B>)> {
		let (sender, port) = channel::unbounded();
		let _ = self.protocol_sender.send(ProtocolMsg::Peers(sender));
		let peers = port.recv().expect("1. Protocol keeps handling messages until all senders are dropped,
			or the ProtocolMsg::Stop message is received,
			2 Service keeps a sender to protocol, and the ProtocolMsg::Stop is never sent.");
		let network = self.network.lock();
		peers.into_iter().map(|(idx, info)| {
			(idx, network.peer_id_of_node(idx).map(|p| p.clone()), info)
		}).collect::<Vec<_>>()
	}
}

/// Trait for managing network
pub trait ManageNetwork {
	/// Set to allow unreserved peers to connect
	fn accept_unreserved_peers(&self);
	/// Set to deny unreserved peers to connect
	fn deny_unreserved_peers(&self);
	/// Remove reservation for the peer
	fn remove_reserved_peer(&self, peer: PeerId);
	/// Add reserved peer
	fn add_reserved_peer(&self, peer: String) -> Result<(), String>;
	/// Returns a user-friendly identifier of our node.
	fn node_id(&self) -> Option<String>;
}

impl<B: BlockT + 'static, S: NetworkSpecialization<B>> ManageNetwork for Service<B, S> {
	fn accept_unreserved_peers(&self) {
		self.network.lock().accept_unreserved_peers();
	}

	fn deny_unreserved_peers(&self) {
		self.network.lock().deny_unreserved_peers();
	}

	fn remove_reserved_peer(&self, peer: PeerId) {
		self.network.lock().remove_reserved_peer(peer);
	}

	fn add_reserved_peer(&self, peer: String) -> Result<(), String> {
		let (addr, peer_id) = parse_str_addr(&peer).map_err(|e| format!("{:?}", e))?;
		self.network.lock().add_reserved_peer(addr, peer_id);
		Ok(())
	}

	fn node_id(&self) -> Option<String> {
		let network = self.network.lock();
		let ret = network
			.listeners()
			.next()
			.map(|addr| {
				let mut addr = addr.clone();
				addr.append(Libp2pProtocol::P2p(network.peer_id().clone().into()));
				addr.to_string()
			});
		ret
	}
}


/// Create a NetworkPort/Chan pair.
pub fn network_channel<B: BlockT + 'static>(protocol_id: ProtocolId) -> (NetworkChan<B>, NetworkPort<B>) {
	let (network_sender, network_receiver) = channel::unbounded();
	let task_notify = Arc::new(AtomicTask::new());
	let network_port = NetworkPort::new(network_receiver, protocol_id, task_notify.clone());
	let network_chan = NetworkChan::new(network_sender, task_notify);
	(network_chan, network_port)
}


/// A sender of NetworkMsg that notifies a task when a message has been sent.
#[derive(Clone)]
pub struct NetworkChan<B: BlockT + 'static> {
	sender: Sender<NetworkMsg<B>>,
	task_notify: Arc<AtomicTask>,
}

impl<B: BlockT + 'static> NetworkChan<B> {
	/// Create a new network chan.
	pub fn new(sender: Sender<NetworkMsg<B>>, task_notify: Arc<AtomicTask>) -> Self {
		 NetworkChan {
			sender,
			task_notify,
		}
	}

	/// Send a messaging, to be handled on a stream. Notify the task handling the stream.
	pub fn send(&self, msg: NetworkMsg<B>) {
		let _ = self.sender.send(msg);
		self.task_notify.notify();
	}
}

impl<B: BlockT + 'static> Drop for NetworkChan<B> {
	/// Notifying the task when a sender is dropped(when all are dropped, the stream is finished).
	fn drop(&mut self) {
		self.task_notify.notify();
	}
}


/// A receiver of NetworkMsg that makes the protocol-id available with each message.
pub struct NetworkPort<B: BlockT + 'static> {
	receiver: Receiver<NetworkMsg<B>>,
	protocol_id: ProtocolId,
	task_notify: Arc<AtomicTask>,
}

impl<B: BlockT + 'static> NetworkPort<B> {
	/// Create a new network port for a given protocol-id.
	pub fn new(receiver: Receiver<NetworkMsg<B>>, protocol_id: ProtocolId, task_notify: Arc<AtomicTask>) -> Self {
		Self {
			receiver,
			protocol_id,
			task_notify,
		}
	}

	/// Receive a message, if any is currently-enqueued.
	/// Register the current tokio task for notification when a new message is available.
	pub fn take_one_message(&self) -> Result<Option<(ProtocolId, NetworkMsg<B>)>, ()> {
		self.task_notify.register();
		match self.receiver.try_recv() {
			Ok(msg) => Ok(Some((self.protocol_id.clone(), msg))),
			Err(TryRecvError::Empty) => Ok(None),
			Err(TryRecvError::Disconnected) => Err(()),
		}
	}

	/// Get a reference to the underlying crossbeam receiver.
	#[cfg(any(test, feature = "test-helpers"))]
	pub fn receiver(&self) -> &Receiver<NetworkMsg<B>> {
		&self.receiver
	}
}

/// Messages to be handled by NetworkService.
#[derive(Debug)]
pub enum NetworkMsg<B: BlockT + 'static> {
	/// Ask network to convert a list of nodes, to a list of peers.
	PeerIds(Vec<NodeIndex>, Sender<Vec<(NodeIndex, Option<PeerId>)>>),
	/// Send an outgoing custom message.
	Outgoing(NodeIndex, Message<B>),
	/// Report a peer.
	ReportPeer(NodeIndex, Severity),
	/// Get a peer id.
	GetPeerId(NodeIndex, Sender<Option<String>>),
}

/// Starts the background thread that handles the networking.
fn start_thread<B: BlockT + 'static, S: NetworkSpecialization<B>>(
	protocol_sender: Sender<ProtocolMsg<B, S>>,
	network_port: NetworkPort<B>,
	config: NetworkConfiguration,
	registered: RegisteredProtocol<Message<B>>,
) -> Result<((oneshot::Sender<()>, thread::JoinHandle<()>), Arc<Mutex<NetworkService<Message<B>>>>), Error> {
	let protocol_id = registered.id();

	// Start the main service.
	let service = match start_service(config, Some(registered)) {
		Ok(service) => Arc::new(Mutex::new(service)),
		Err(err) => {
			match err.kind() {
				ErrorKind::Io(ref e) if e.kind() == io::ErrorKind::AddrInUse =>
					warn!("Network port is already in use, make sure that another instance of Substrate client is not running or change the port using the --port option."),
				_ => warn!("Error starting network: {}", err),
			};
			return Err(err.into())
		},
	};

	let (close_tx, close_rx) = oneshot::channel();
	let service_clone = service.clone();
	let mut runtime = Runtime::new()?;
	let thread = thread::Builder::new().name("network".to_string()).spawn(move || {
		let fut = run_thread(protocol_sender, service_clone, network_port, protocol_id)
			.select(close_rx.then(|_| Ok(())))
			.map(|(val, _)| val)
			.map_err(|(err,_ )| err);

		// Note that we use `block_on` and not `block_on_all` because we want to kill the thread
		// instantly if `close_rx` receives something.
		match runtime.block_on(fut) {
			Ok(()) => debug!(target: "sub-libp2p", "Networking thread finished"),
			Err(err) => error!(target: "sub-libp2p", "Error while running libp2p: {:?}", err),
		};
	})?;

	Ok(((close_tx, thread), service))
}

/// Runs the background thread that handles the networking.
fn run_thread<B: BlockT + 'static, S: NetworkSpecialization<B>>(
	protocol_sender: Sender<ProtocolMsg<B, S>>,
	network_service: Arc<Mutex<NetworkService<Message<B>>>>,
	network_port: NetworkPort<B>,
	protocol_id: ProtocolId,
) -> impl Future<Item = (), Error = io::Error> {

	let network_service_2 = network_service.clone();

	// Protocol produces a stream of messages about what happens in sync.
	let protocol = stream::poll_fn(move || {
		match network_port.take_one_message() {
			Ok(Some(message)) => Ok(Async::Ready(Some(message))),
			Ok(None) => Ok(Async::NotReady),
			Err(_) => Err(())
		}
	}).for_each(move |(protocol_id, msg)| {
		// Handle message from Protocol.
		match msg {
			NetworkMsg::PeerIds(node_idxs, sender) => {
				let reply = node_idxs.into_iter().map(|idx| {
					(idx, network_service_2.lock().peer_id_of_node(idx).map(|p| p.clone()))
				}).collect::<Vec<_>>();
				let _ = sender.send(reply);
			}
			NetworkMsg::Outgoing(who, outgoing_message) => {
				network_service_2
					.lock()
					.send_custom_message(who, protocol_id, outgoing_message);
			},
			NetworkMsg::ReportPeer(who, severity) => {
				match severity {
					Severity::Bad(_) => network_service_2.lock().ban_node(who),
					Severity::Useless(_) => network_service_2.lock().drop_node(who),
					Severity::Timeout => network_service_2.lock().drop_node(who),
				}
			},
			NetworkMsg::GetPeerId(who, sender) => {
				let node_id = network_service_2
					.lock()
					.peer_id_of_node(who)
					.cloned()
					.map(|id| id.to_base58());
				let _ = sender.send(node_id);
			},
		}
		Ok(())
	})
	.then(|res| {
		match res {
			Ok(()) => (),
			Err(_) => error!("Protocol disconnected"),
		};
		Ok(())
	});

	// The network service produces events about what happens on the network. Let's process them.
	let network = stream::poll_fn(move || network_service.lock().poll()).for_each(move |event| {
		match event {
			NetworkServiceEvent::ClosedCustomProtocols { node_index, protocols, debug_info } => {
				if !protocols.is_empty() {
					debug_assert_eq!(protocols, &[protocol_id]);
					let _ = protocol_sender.send(
						ProtocolMsg::PeerDisconnected(node_index, debug_info));
				}
			}
			NetworkServiceEvent::OpenedCustomProtocol { node_index, version, debug_info, .. } => {
				debug_assert_eq!(version, protocol::CURRENT_VERSION as u8);
				let _ = protocol_sender.send(ProtocolMsg::PeerConnected(node_index, debug_info));
			}
			NetworkServiceEvent::ClosedCustomProtocol { node_index, debug_info, .. } => {
				let _ = protocol_sender.send(ProtocolMsg::PeerDisconnected(node_index, debug_info));
			}
			NetworkServiceEvent::CustomMessage { node_index, message, .. } => {
				let _ = protocol_sender.send(ProtocolMsg::CustomMessage(node_index, message));
				return Ok(())
			}
			NetworkServiceEvent::Clogged { node_index, messages, .. } => {
				debug!(target: "sync", "{} clogging messages:", messages.len());
				for msg in messages.into_iter().take(5) {
					debug!(target: "sync", "{:?}", msg);
					let _ = protocol_sender.send(ProtocolMsg::PeerClogged(node_index, Some(msg)));
				}
			}
		};
		Ok(())
	});

	// Merge all futures into one.
	let futures: Vec<Box<Future<Item = (), Error = io::Error> + Send>> = vec![
		Box::new(protocol) as Box<_>,
		Box::new(network) as Box<_>
	];

	futures::select_all(futures)
		.and_then(move |_| {
			debug!("Networking ended");
			Ok(())
		})
		.map_err(|(r, _, _)| r)
}
