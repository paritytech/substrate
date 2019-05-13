// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
use std::sync::atomic::{AtomicBool, Ordering};
use std::{io, thread, time::Duration};

use log::{warn, debug, error, info};
use futures::{Async, Future, Stream, sync::oneshot, sync::mpsc};
use parking_lot::{Mutex, RwLock};
use network_libp2p::{ProtocolId, NetworkConfiguration};
use network_libp2p::{start_service, parse_str_addr, Service as NetworkService, ServiceEvent as NetworkServiceEvent};
use network_libp2p::{RegisteredProtocol, NetworkState};
use peerset::PeersetHandle;
use consensus::import_queue::{ImportQueue, Link};
use runtime_primitives::{traits::{Block as BlockT, NumberFor}, ConsensusEngineId};

use crate::consensus_gossip::{ConsensusGossip, MessageRecipient as GossipMessageRecipient};
use crate::message::Message;
use crate::protocol::{self, Context, CustomMessageOutcome, Protocol, ConnectedPeer, ProtocolMsg, ProtocolStatus, PeerInfo};
use crate::config::Params;
use crate::error::Error;
use crate::specialization::NetworkSpecialization;

use crossbeam_channel::{self as channel, Receiver, Sender, TryRecvError};
use tokio::prelude::task::AtomicTask;
use tokio::runtime::Builder as RuntimeBuilder;

/// Interval at which we send status updates on the SyncProvider status stream.
const STATUS_INTERVAL: Duration = Duration::from_millis(5000);

pub use network_libp2p::PeerId;

/// Type that represents fetch completion future.
pub type FetchFuture = oneshot::Receiver<Vec<u8>>;

/// Sync status
pub trait SyncProvider<B: BlockT>: Send + Sync {
	/// Get a stream of sync statuses.
	fn status(&self) -> mpsc::UnboundedReceiver<ProtocolStatus<B>>;
	/// Get network state.
	fn network_state(&self) -> NetworkState;
	/// Get currently connected peers
	fn peers(&self) -> Vec<(PeerId, PeerInfo<B>)>;
	/// Are we in the process of downloading the chain?
	fn is_major_syncing(&self) -> bool;
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
#[derive(Clone)]
pub struct NetworkLink<B: BlockT, S: NetworkSpecialization<B>> {
	/// The protocol sender
	pub(crate) protocol_sender: mpsc::UnboundedSender<ProtocolMsg<B, S>>,
	/// The network sender
	pub(crate) network_sender: NetworkChan<B>,
}

impl<B: BlockT, S: NetworkSpecialization<B>> Link<B> for NetworkLink<B, S> {
	fn block_imported(&self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::BlockImportedSync(hash.clone(), number));
	}

	fn blocks_processed(&self, processed_blocks: Vec<B::Hash>, has_error: bool) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::BlocksProcessed(processed_blocks, has_error));
	}

	fn justification_imported(&self, who: PeerId, hash: &B::Hash, number: NumberFor<B>, success: bool) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::JustificationImportResult(hash.clone(), number, success));
		if !success {
			info!("Invalid justification provided by {} for #{}", who, hash);
			let _ = self.network_sender.send(NetworkMsg::ReportPeer(who.clone(), i32::min_value()));
			let _ = self.network_sender.send(NetworkMsg::DisconnectPeer(who.clone()));
		}
	}

	fn clear_justification_requests(&self) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::ClearJustificationRequests);
	}

	fn request_justification(&self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::RequestJustification(hash.clone(), number));
	}

	fn report_peer(&self, who: PeerId, reputation_change: i32) {
		self.network_sender.send(NetworkMsg::ReportPeer(who, reputation_change));
	}

	fn restart(&self) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::RestartSync);
	}
}

/// A cloneable handle for reporting cost/benefits of peers.
#[derive(Clone)]
pub struct ReportHandle {
	inner: PeersetHandle, // wraps it so we don't have to worry about breaking API.
}

impl ReportHandle {
	/// Report a given peer as either beneficial (+) or costly (-) according to the
	/// given scalar.
	pub fn report_peer(&self, who: PeerId, cost_benefit: i32) {
		self.inner.report_peer(who, cost_benefit);
	}
}

/// Substrate network service. Handles network IO and manages connectivity.
pub struct Service<B: BlockT + 'static, S: NetworkSpecialization<B>> {
	/// Sinks to propagate status updates.
	status_sinks: Arc<Mutex<Vec<mpsc::UnboundedSender<ProtocolStatus<B>>>>>,
	/// Are we connected to any peer?
	is_offline: Arc<AtomicBool>,
	/// Are we actively catching up with the chain?
	is_major_syncing: Arc<AtomicBool>,
	/// Peers whom we are connected with.
	peers: Arc<RwLock<HashMap<PeerId, ConnectedPeer<B>>>>,
	/// Network service
	network: Arc<Mutex<NetworkService<Message<B>>>>,
	/// Peerset manager (PSM); manages the reputation of nodes and indicates the network which
	/// nodes it should be connected to or not.
	peerset: PeersetHandle,
	/// Protocol sender
	protocol_sender: mpsc::UnboundedSender<ProtocolMsg<B, S>>,
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
		let (network_chan, network_port) = network_channel();
		let status_sinks = Arc::new(Mutex::new(Vec::new()));
		// Start in off-line mode, since we're not connected to any nodes yet.
		let is_offline = Arc::new(AtomicBool::new(true));
		let is_major_syncing = Arc::new(AtomicBool::new(false));
		let peers: Arc<RwLock<HashMap<PeerId, ConnectedPeer<B>>>> = Arc::new(Default::default());
		let (protocol, protocol_sender) = Protocol::new(
			peers.clone(),
			network_chan.clone(),
			params.config,
			params.chain,
			params.on_demand,
			params.transaction_pool,
			params.specialization,
		)?;
		let versions: Vec<_> = ((protocol::MIN_VERSION as u8)..=(protocol::CURRENT_VERSION as u8)).collect();
		let registered = RegisteredProtocol::new(protocol_id, &versions);
		let (thread, network, peerset) = start_thread(
			is_offline.clone(),
			is_major_syncing.clone(),
			protocol,
			import_queue.clone(),
			network_port,
			status_sinks.clone(),
			params.network_config,
			registered,
		)?;

		let service = Arc::new(Service {
			status_sinks,
			is_offline,
			is_major_syncing,
			peers,
			peerset,
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

	/// Returns the network identity of the node.
	pub fn local_peer_id(&self) -> PeerId {
		self.network.lock().peer_id().clone()
	}

	/// Called when a new block is imported by the client.
	pub fn on_block_imported(&self, hash: B::Hash, header: B::Header) {
		let _ = self
			.protocol_sender
			.unbounded_send(ProtocolMsg::BlockImported(hash, header));
	}

	/// Called when a new block is finalized by the client.
	pub fn on_block_finalized(&self, hash: B::Hash, header: B::Header) {
		let _ = self
			.protocol_sender
			.unbounded_send(ProtocolMsg::BlockFinalized(hash, header));
	}

	/// Called when new transactons are imported by the client.
	pub fn trigger_repropagate(&self) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::PropagateExtrinsics);
	}

	/// Make sure an important block is propagated to peers.
	///
	/// In chain-based consensus, we often need to make sure non-best forks are
	/// at least temporarily synced.
	pub fn announce_block(&self, hash: B::Hash) {
		let _ = self.protocol_sender.unbounded_send(ProtocolMsg::AnnounceBlock(hash));
	}

	/// Send a consensus message through the gossip
	pub fn gossip_consensus_message(
		&self,
		topic: B::Hash,
		engine_id: ConsensusEngineId,
		message: Vec<u8>,
		recipient: GossipMessageRecipient,
	) {
		let _ = self
			.protocol_sender
			.unbounded_send(ProtocolMsg::GossipConsensusMessage(
				topic, engine_id, message, recipient,
			));
	}

	/// Report a given peer as either beneficial (+) or costly (-) according to the
	/// given scalar.
	pub fn report_peer(&self, who: PeerId, cost_benefit: i32) {
		self.peerset.report_peer(who, cost_benefit);
	}

	/// Execute a closure with the chain-specific network specialization.
	pub fn with_spec<F>(&self, f: F)
		where F: FnOnce(&mut S, &mut Context<B>) + Send + 'static
	{
		let _ = self
			.protocol_sender
			.unbounded_send(ProtocolMsg::ExecuteWithSpec(Box::new(f)));
	}

	/// Execute a closure with the consensus gossip.
	pub fn with_gossip<F>(&self, f: F)
		where F: FnOnce(&mut ConsensusGossip<B>, &mut Context<B>) + Send + 'static
	{
		let _ = self
			.protocol_sender
			.unbounded_send(ProtocolMsg::ExecuteWithGossip(Box::new(f)));
	}

	/// Are we in the process of downloading the chain?
	/// Used by both SyncProvider and SyncOracle.
	fn is_major_syncing(&self) -> bool {
		self.is_major_syncing.load(Ordering::Relaxed)
	}
}

impl<B: BlockT + 'static, S: NetworkSpecialization<B>> ::consensus::SyncOracle for Service<B, S> {
	fn is_major_syncing(&self) -> bool {
		self.is_major_syncing()
	}

	fn is_offline(&self) -> bool {
		self.is_offline.load(Ordering::Relaxed)
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
	fn is_major_syncing(&self) -> bool {
		self.is_major_syncing()
	}

	/// Get sync status
	fn status(&self) -> mpsc::UnboundedReceiver<ProtocolStatus<B>> {
		let (sink, stream) = mpsc::unbounded();
		self.status_sinks.lock().push(sink);
		stream
	}

	fn network_state(&self) -> NetworkState {
		self.network.lock().state()
	}

	fn peers(&self) -> Vec<(PeerId, PeerInfo<B>)> {
		let peers = (*self.peers.read()).clone();
		peers.into_iter().map(|(idx, connected)| (idx, connected.peer_info)).collect()
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
}

impl<B: BlockT + 'static, S: NetworkSpecialization<B>> ManageNetwork for Service<B, S> {
	fn accept_unreserved_peers(&self) {
		self.peerset.set_reserved_only(false);
	}

	fn deny_unreserved_peers(&self) {
		self.peerset.set_reserved_only(true);
	}

	fn remove_reserved_peer(&self, peer: PeerId) {
		self.peerset.remove_reserved_peer(peer);
	}

	fn add_reserved_peer(&self, peer: String) -> Result<(), String> {
		let (peer_id, addr) = parse_str_addr(&peer).map_err(|e| format!("{:?}", e))?;
		self.peerset.add_reserved_peer(peer_id.clone());
		self.network.lock().add_known_address(peer_id, addr);
		Ok(())
	}
}


/// Create a NetworkPort/Chan pair.
pub fn network_channel<B: BlockT + 'static>() -> (NetworkChan<B>, NetworkPort<B>) {
	let (network_sender, network_receiver) = channel::unbounded();
	let task_notify = Arc::new(AtomicTask::new());
	let network_port = NetworkPort::new(network_receiver, task_notify.clone());
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
	task_notify: Arc<AtomicTask>,
}

impl<B: BlockT + 'static> NetworkPort<B> {
	/// Create a new network port for a given protocol-id.
	pub fn new(receiver: Receiver<NetworkMsg<B>>, task_notify: Arc<AtomicTask>) -> Self {
		Self {
			receiver,
			task_notify,
		}
	}

	/// Receive a message, if any is currently-enqueued.
	/// Register the current tokio task for notification when a new message is available.
	pub fn take_one_message(&self) -> Result<Option<NetworkMsg<B>>, ()> {
		self.task_notify.register();
		match self.receiver.try_recv() {
			Ok(msg) => Ok(Some(msg)),
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
	/// Send an outgoing custom message.
	Outgoing(PeerId, Message<B>),
	/// Disconnect a peer we're connected to, or do nothing if we're not connected.
	DisconnectPeer(PeerId),
	/// Performs a reputation adjustement on a peer.
	ReportPeer(PeerId, i32),
	/// Synchronization response.
	#[cfg(any(test, feature = "test-helpers"))]
	Synchronized,
}

/// Starts the background thread that handles the networking.
fn start_thread<B: BlockT + 'static, S: NetworkSpecialization<B>, H: ExHashT>(
	is_offline: Arc<AtomicBool>,
	is_major_syncing: Arc<AtomicBool>,
	protocol: Protocol<B, S, H>,
	import_queue: Box<ImportQueue<B>>,
	network_port: NetworkPort<B>,
	status_sinks: Arc<Mutex<Vec<mpsc::UnboundedSender<ProtocolStatus<B>>>>>,
	config: NetworkConfiguration,
	registered: RegisteredProtocol<Message<B>>,
) -> Result<((oneshot::Sender<()>, thread::JoinHandle<()>), Arc<Mutex<NetworkService<Message<B>>>>, PeersetHandle), Error> {
	// Start the main service.
	let (service, peerset) = match start_service(config, registered) {
		Ok((service, peerset)) => (Arc::new(Mutex::new(service)), peerset),
		Err(err) => {
			warn!("Error starting network: {}", err);
			return Err(err.into())
		},
	};

	let (close_tx, close_rx) = oneshot::channel();
	let service_clone = service.clone();
	let mut runtime = RuntimeBuilder::new().name_prefix("libp2p-").build()?;
	let peerset_clone = peerset.clone();
	let thread = thread::Builder::new().name("network".to_string()).spawn(move || {
		let fut = run_thread(is_offline, is_major_syncing, protocol, service_clone, import_queue, network_port, status_sinks, peerset_clone)
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

	Ok(((close_tx, thread), service, peerset))
}

/// Runs the background thread that handles the networking.
fn run_thread<B: BlockT + 'static, S: NetworkSpecialization<B>, H: ExHashT>(
	is_offline: Arc<AtomicBool>,
	is_major_syncing: Arc<AtomicBool>,
	mut protocol: Protocol<B, S, H>,
	network_service: Arc<Mutex<NetworkService<Message<B>>>>,
	import_queue: Box<ImportQueue<B>>,
	network_port: NetworkPort<B>,
	status_sinks: Arc<Mutex<Vec<mpsc::UnboundedSender<ProtocolStatus<B>>>>>,
	peerset: PeersetHandle,
) -> impl Future<Item = (), Error = io::Error> {
	// Interval at which we send status updates on the `status_sinks`.
	let mut status_interval = tokio::timer::Interval::new_interval(STATUS_INTERVAL);

	futures::future::poll_fn(move || {
		while let Ok(Async::Ready(_)) = status_interval.poll() {
			let status = protocol.status();
			status_sinks.lock().retain(|sink| sink.unbounded_send(status.clone()).is_ok());
		}

		match protocol.poll() {
			Ok(Async::Ready(())) => return Ok(Async::Ready(())),
			Ok(Async::NotReady) => {}
			Err(err) => void::unreachable(err),
		}

		loop {
			match network_port.take_one_message() {
				Ok(None) => break,
				Ok(Some(NetworkMsg::Outgoing(who, outgoing_message))) =>
					network_service.lock().send_custom_message(&who, outgoing_message),
				Ok(Some(NetworkMsg::ReportPeer(who, reputation))) =>
					peerset.report_peer(who, reputation),
				Ok(Some(NetworkMsg::DisconnectPeer(who))) =>
					network_service.lock().drop_node(&who),
				#[cfg(any(test, feature = "test-helpers"))]
				Ok(Some(NetworkMsg::Synchronized)) => {}

				Err(_) => return Ok(Async::Ready(())),
			}
		}

		loop {
			let outcome = match network_service.lock().poll() {
				Ok(Async::NotReady) => break,
				Ok(Async::Ready(Some(NetworkServiceEvent::OpenedCustomProtocol { peer_id, version, debug_info, .. }))) => {
					debug_assert!(
						version <= protocol::CURRENT_VERSION as u8
						&& version >= protocol::MIN_VERSION as u8
					);
					protocol.on_peer_connected(peer_id, debug_info);
					CustomMessageOutcome::None
				}
				Ok(Async::Ready(Some(NetworkServiceEvent::ClosedCustomProtocol { peer_id, debug_info, .. }))) => {
					protocol.on_peer_disconnected(peer_id, debug_info);
					CustomMessageOutcome::None
				},
				Ok(Async::Ready(Some(NetworkServiceEvent::CustomMessage { peer_id, message, .. }))) =>
					protocol.on_custom_message(peer_id, message),
				Ok(Async::Ready(Some(NetworkServiceEvent::Clogged { peer_id, messages, .. }))) => {
					debug!(target: "sync", "{} clogging messages:", messages.len());
					for msg in messages.into_iter().take(5) {
						debug!(target: "sync", "{:?}", msg);
						protocol.on_clogged_peer(peer_id.clone(), Some(msg));
					}
					CustomMessageOutcome::None
				}
				Ok(Async::Ready(None)) => return Ok(Async::Ready(())),
				Err(err) => {
					error!(target: "sync", "Error in the network: {:?}", err);
					return Err(err)
				}
			};

			match outcome {
				CustomMessageOutcome::BlockImport(origin, blocks) =>
					import_queue.import_blocks(origin, blocks),
				CustomMessageOutcome::JustificationImport(origin, hash, nb, justification) =>
					import_queue.import_justification(origin, hash, nb, justification),
				CustomMessageOutcome::None => {}
			}
		}

		is_offline.store(protocol.is_offline(), Ordering::Relaxed);
		is_major_syncing.store(protocol.is_major_syncing(), Ordering::Relaxed);

		Ok(Async::NotReady)
	})
}
