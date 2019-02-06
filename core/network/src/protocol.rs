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

use parity_codec::Encode;
use crossbeam_channel::{self as channel, Receiver, Sender, select};
use network_libp2p::{NodeIndex, Severity};
use primitives::storage::StorageKey;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{As, Block as BlockT, Header as HeaderT, NumberFor, Zero};
use consensus::import_queue::ImportQueue;
use crate::message::{self, Message};
use crate::message::generic::Message as GenericMessage;
use crate::consensus_gossip::ConsensusGossip;
use crate::on_demand::OnDemandService;
use crate::specialization::NetworkSpecialization;
use crate::sync::{ChainSync, Status as SyncStatus, SyncState};
use crate::service::{NetworkChan, NetworkMsg, TransactionPool, ExHashT};
use crate::config::{ProtocolConfig, Roles};
use rustc_hex::ToHex;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;
use std::thread;
use std::time;
use std::cmp;
use log::{trace, debug, warn};
use crate::chain::Client;
use client::light::fetcher::ChangesProof;
use crate::error;

const REQUEST_TIMEOUT_SEC: u64 = 40;
const TICK_TIMEOUT: time::Duration = time::Duration::from_millis(1000);
const PROPAGATE_TIMEOUT: time::Duration = time::Duration::from_millis(5000);

/// Current protocol version.
pub(crate) const CURRENT_VERSION: u32 = 1;

// Maximum allowed entries in `BlockResponse`
const MAX_BLOCK_DATA_RESPONSE: u32 = 128;
/// When light node connects to the full node and the full node is behind light node
/// for at least `LIGHT_MAXIMAL_BLOCKS_DIFFERENCE` blocks, we consider it unuseful
/// and disconnect to free connection slot.
const LIGHT_MAXIMAL_BLOCKS_DIFFERENCE: u64 = 8192;

// Lock must always be taken in order declared here.
pub struct Protocol<B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> {
	network_chan: NetworkChan,
	port: Receiver<ProtocolMsg<B, S>>,
	config: ProtocolConfig,
	on_demand: Option<Arc<OnDemandService<B>>>,
	genesis_hash: B::Hash,
	sync: ChainSync<B>,
	specialization: S,
	consensus_gossip: ConsensusGossip<B>,
	context_data: ContextData<B, H>,
	// Connected peers pending Status message.
	handshaking_peers: HashMap<NodeIndex, time::Instant>,
	transaction_pool: Arc<TransactionPool<H, B>>,
}
/// Syncing status and statistics
#[derive(Clone)]
pub struct ProtocolStatus<B: BlockT> {
	/// Sync status.
	pub sync: SyncStatus<B>,
	/// Total number of connected peers
	pub num_peers: usize,
	/// Total number of active peers.
	pub num_active_peers: usize,
}

/// Peer information
#[derive(Debug)]
struct Peer<B: BlockT, H: ExHashT> {
	/// Protocol version
	protocol_version: u32,
	/// Roles
	roles: Roles,
	/// Peer best block hash
	best_hash: B::Hash,
	/// Peer best block number
	best_number: <B::Header as HeaderT>::Number,
	/// Pending block request if any
	block_request: Option<message::BlockRequest<B>>,
	/// Pending block request timestamp
	block_request_timestamp: Option<time::Instant>,
	/// Pending block justification request if any
	justification_request: Option<message::BlockRequest<B>>,
	/// Pending block justification request timestamp
	justification_request_timestamp: Option<time::Instant>,
	/// Holds a set of transactions known to this peer.
	known_extrinsics: HashSet<H>,
	/// Holds a set of blocks known to this peer.
	known_blocks: HashSet<B::Hash>,
	/// Request counter,
	next_request_id: message::RequestId,
}

impl<B: BlockT, H: ExHashT> Peer<B, H> {
	fn min_request_timestamp(&self) -> Option<&time::Instant> {
		match (self.block_request_timestamp, self.justification_request_timestamp) {
			(Some(t1), Some(t2)) if t1 < t2 => self.block_request_timestamp.as_ref(),
			(Some(_), Some(_)) => self.justification_request_timestamp.as_ref(),
			(Some(_), None) => self.block_request_timestamp.as_ref(),
			(None, Some(_)) => self.justification_request_timestamp.as_ref(),
			_ => None,
		}
	}
}

/// Info about a peer's known state.
#[derive(Clone, Debug)]
pub struct PeerInfo<B: BlockT> {
	/// Roles
	pub roles: Roles,
	/// Protocol version
	pub protocol_version: u32,
	/// Peer best block hash
	pub best_hash: B::Hash,
	/// Peer best block number
	pub best_number: <B::Header as HeaderT>::Number,
}

/// Context for a network-specific handler.
pub trait Context<B: BlockT> {
	/// Get a reference to the client.
	fn client(&self) -> &crate::chain::Client<B>;

	/// Point out that a peer has been malign or irresponsible or appeared lazy.
	fn report_peer(&mut self, who: NodeIndex, reason: Severity);

	/// Get peer info.
	fn peer_info(&self, peer: NodeIndex) -> Option<PeerInfo<B>>;

	/// Send a message to a peer.
	fn send_message(&mut self, who: NodeIndex, data: crate::message::Message<B>);
}

/// Protocol context.
pub(crate) struct ProtocolContext<'a, B: 'a + BlockT, H: 'a + ExHashT> {
	network_chan: &'a NetworkChan,
	context_data: &'a mut ContextData<B, H>,
}

impl<'a, B: BlockT + 'a, H: 'a + ExHashT> ProtocolContext<'a, B, H> {
	pub(crate) fn new(
		context_data: &'a mut ContextData<B, H>,
		network_chan: &'a NetworkChan,
	) -> Self {
		ProtocolContext {
			network_chan,
			context_data,
		}
	}

	/// Send a message to a peer.
	pub fn send_message(&mut self, who: NodeIndex, message: Message<B>) {
		send_message(
			&mut self.context_data.peers,
			&self.network_chan,
			who,
			message,
		)
	}

	/// Point out that a peer has been malign or irresponsible or appeared lazy.
	pub fn report_peer(&mut self, who: NodeIndex, reason: Severity) {
		let _ = self
			.network_chan
			.send(NetworkMsg::ReportPeer(who, reason));
	}

	/// Get peer info.
	pub fn peer_info(&self, peer: NodeIndex) -> Option<PeerInfo<B>> {
		self.context_data.peers.get(&peer).map(|p| PeerInfo {
			roles: p.roles,
			protocol_version: p.protocol_version,
			best_hash: p.best_hash,
			best_number: p.best_number,
		})
	}
}

impl<'a, B: BlockT + 'a, H: ExHashT + 'a> Context<B> for ProtocolContext<'a, B, H> {
	fn send_message(&mut self, who: NodeIndex, message: Message<B>) {
		ProtocolContext::send_message(self, who, message);
	}

	fn report_peer(&mut self, who: NodeIndex, reason: Severity) {
		ProtocolContext::report_peer(self, who, reason);
	}

	fn peer_info(&self, who: NodeIndex) -> Option<PeerInfo<B>> {
		ProtocolContext::peer_info(self, who)
	}

	fn client(&self) -> &Client<B> {
		&*self.context_data.chain
	}
}

/// Data necessary to create a context.
pub(crate) struct ContextData<B: BlockT, H: ExHashT> {
	// All connected peers
	peers: HashMap<NodeIndex, Peer<B, H>>,
	pub chain: Arc<Client<B>>,
}

/// A task, consisting of a user-provided closure, to be executed on the Protocol thread.
pub trait SpecTask<B: BlockT, S: NetworkSpecialization<B>>  {
    fn call_box(self: Box<Self>, spec: &mut S, context: &mut Context<B>);
}

impl<B: BlockT, S: NetworkSpecialization<B>, F: FnOnce(&mut S, &mut Context<B>)> SpecTask<B, S> for F {
    fn call_box(self: Box<F>, spec: &mut S, context: &mut Context<B>) {
        (*self)(spec, context)
    }
}

/// A task, consisting of a user-provided closure, to be executed on the Protocol thread.
pub trait GossipTask<B: BlockT>  {
    fn call_box(self: Box<Self>, gossip: &mut ConsensusGossip<B>, context: &mut Context<B>);
}

impl<B: BlockT, F: FnOnce(&mut ConsensusGossip<B>, &mut Context<B>)> GossipTask<B> for F {
    fn call_box(self: Box<F>, gossip: &mut ConsensusGossip<B>, context: &mut Context<B>) {
        (*self)(gossip, context)
    }
}

/// Messages sent to Protocol.
pub enum ProtocolMsg<B: BlockT, S: NetworkSpecialization<B>,> {
	/// A peer connected, with debug info.
	PeerConnected(NodeIndex, String),
	/// A peer disconnected, with debug info.
	PeerDisconnected(NodeIndex, String),
	/// A custom message from another peer.
	CustomMessage(NodeIndex, Message<B>),
	/// Ask the protocol for its status.
	Status(Sender<ProtocolStatus<B>>),
	/// Tell protocol to propagate extrinsics.
	PropagateExtrinsics,
	/// Execute a closure with the chain-specific network specialization.
	ExecuteWithSpec(Box<SpecTask<B, S> + Send + 'static>),
	/// Execute a closure with the consensus gossip.
	ExecuteWithGossip(Box<GossipTask<B> + Send + 'static>),
	/// Incoming gossip consensus message.
	GossipConsensusMessage(B::Hash, Vec<u8>, bool),
	/// Is protocol currently major-syncing?
	IsMajorSyncing(Sender<bool>),
	/// Is protocol currently offline?
	IsOffline(Sender<bool>),
	/// Return a list of peers currently known to protocol.
	Peers(Sender<Vec<(NodeIndex, PeerInfo<B>)>>),
	/// Let protocol know a peer is currenlty clogged.
	PeerClogged(NodeIndex, Option<Message<B>>),
	/// Tell protocol to maintain sync.
	MaintainSync,
	/// Tell protocol to restart sync.
	RestartSync,
	/// Propagate a block to peers.
	AnnounceBlock(B::Hash),
	/// Tell protocol that a block was imported (sent by the import-queue).
	BlockImportedSync(B::Hash, NumberFor<B>),
	/// Tell protocol to request justification for a block.
	RequestJustification(B::Hash, NumberFor<B>),
	/// A block has been imported (sent by the client).
	BlockImported(B::Hash, B::Header),
	/// A block has been finalized (sent by the client).
	BlockFinalized(B::Hash, B::Header),
	/// Tell protocol to abort sync (does not stop protocol).
	/// Only used in tests.
	#[cfg(any(test, feature = "test-helpers"))]
	Abort,
	/// Tell protocol to abort sync and stop.
	Stop,
	/// Tell protocol to perform regular maintenance.
	Tick,
}

impl<B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> Protocol<B, S, H> {
	/// Create a new instance.
	pub fn new<I: 'static + ImportQueue<B>>(
		network_chan: NetworkChan,
		config: ProtocolConfig,
		chain: Arc<Client<B>>,
		import_queue: Arc<I>,
		on_demand: Option<Arc<OnDemandService<B>>>,
		transaction_pool: Arc<TransactionPool<H, B>>,
		specialization: S,
	) -> error::Result<Sender<ProtocolMsg<B, S>>> {
		let (sender, port) = channel::unbounded();
		let info = chain.info()?;
		let sync = ChainSync::new(config.roles, &info, import_queue);
		let _ = thread::Builder::new()
			.name("Protocol".into())
			.spawn(move || {
				let mut protocol = Protocol {
					network_chan,
					port,
					config: config,
					context_data: ContextData {
						peers: HashMap::new(),
						chain,
					},
					on_demand,
					genesis_hash: info.chain.genesis_hash,
					sync,
					specialization: specialization,
					consensus_gossip: ConsensusGossip::new(),
					handshaking_peers: HashMap::new(),
					transaction_pool: transaction_pool,
				};
				let tick_timeout = channel::tick(TICK_TIMEOUT);
				let propagate_timeout = channel::tick(PROPAGATE_TIMEOUT);
				while protocol.run(&tick_timeout, &propagate_timeout) {
					// Running until all senders have been dropped...
				}
			})
			.expect("Protocol thread spawning failed");
		Ok(sender)
	}

	fn run(
		&mut self,
		tick_timeout: &Receiver<time::Instant>,
		propagate_timeout: &Receiver<time::Instant>,
	) -> bool {
		let msg = select! {
			recv(self.port) -> event => {
				match event {
					Ok(msg) => msg,
					// Our sender has been dropped, quit.
					Err(_) => {
						ProtocolMsg::Stop
					},
				}
			},
			recv(tick_timeout) -> _ => {
				ProtocolMsg::Tick
			},
			recv(propagate_timeout) -> _ => {
				ProtocolMsg::PropagateExtrinsics
			},
		};
		self.handle_msg(msg)
	}

	fn handle_msg(&mut self, msg: ProtocolMsg<B, S>) -> bool {
		match msg {
			ProtocolMsg::Peers(sender) => {
				let peers = self.context_data.peers.iter().map(|(idx, p)| {
					(
						*idx,
						PeerInfo {
							roles: p.roles,
							protocol_version: p.protocol_version,
							best_hash: p.best_hash,
							best_number: p.best_number,
						}
					)
				}).collect();
				let _ = sender.send(peers);
			},
			ProtocolMsg::PeerDisconnected(who, debug_info) => self.on_peer_disconnected(who, debug_info),
			ProtocolMsg::PeerConnected(who, debug_info) => self.on_peer_connected(who, debug_info),
			ProtocolMsg::PeerClogged(who, message) => self.on_clogged_peer(who, message),
			ProtocolMsg::CustomMessage(who, message) => {
				self.on_custom_message(who, message)
			},
			ProtocolMsg::Status(sender) => self.status(sender),
			ProtocolMsg::BlockImported(hash, header) => self.on_block_imported(hash, &header),
			ProtocolMsg::BlockFinalized(hash, header) => self.on_block_finalized(hash, &header),
			ProtocolMsg::ExecuteWithSpec(task) => {
				let mut context =
					ProtocolContext::new(&mut self.context_data, &self.network_chan);
				task.call_box(&mut self.specialization, &mut context);
			},
			ProtocolMsg::ExecuteWithGossip(task) => {
				let mut context =
					ProtocolContext::new(&mut self.context_data, &self.network_chan);
				task.call_box(&mut self.consensus_gossip, &mut context);
			}
			ProtocolMsg::GossipConsensusMessage(topic, message, broadcast) => {
				self.gossip_consensus_message(topic, message, broadcast)
			}
			ProtocolMsg::IsMajorSyncing(sender) => {
				let is_syncing = self.sync.status().is_major_syncing();
				let _ = sender.send(is_syncing);
			}
			ProtocolMsg::IsOffline(sender) => {
				let is_offline = self.sync.status().is_offline();
				let _ = sender.send(is_offline);
			}
			ProtocolMsg::MaintainSync => {
				let mut context =
					ProtocolContext::new(&mut self.context_data, &self.network_chan);
				self.sync.maintain_sync(&mut context);
			}
			ProtocolMsg::RestartSync => {
				let mut context =
					ProtocolContext::new(&mut self.context_data, &self.network_chan);
				self.sync.restart(&mut context);
			}
			ProtocolMsg::AnnounceBlock(hash) => self.announce_block(hash),
			ProtocolMsg::BlockImportedSync(hash, number) => self.sync.block_imported(&hash, number),
			ProtocolMsg::RequestJustification(hash, number) => {
				let mut context =
					ProtocolContext::new(&mut self.context_data, &self.network_chan);
				self.sync.request_justification(&hash, number, &mut context);
			},
			ProtocolMsg::PropagateExtrinsics => self.propagate_extrinsics(),
			ProtocolMsg::Tick => self.tick(),
			#[cfg(any(test, feature = "test-helpers"))]
			ProtocolMsg::Abort => self.abort(),
			ProtocolMsg::Stop => {
				self.stop();
				return false;
			},
		}
		true
	}

	fn handle_response(&mut self, who: NodeIndex, response: &message::BlockResponse<B>) -> Option<message::BlockRequest<B>> {
		let request = if let Some(ref mut peer) = self.context_data.peers.get_mut(&who) {
			match (peer.block_request.take(), peer.justification_request.take()) {
				(Some(block_request), Some(justification_request)) => {
					if block_request.id == response.id {
						peer.block_request_timestamp = None;
						peer.justification_request = Some(justification_request);
						block_request
					} else if justification_request.id == response.id {
						peer.justification_request_timestamp = None;
						peer.block_request = Some(block_request);
						justification_request
					} else {
						peer.justification_request_timestamp = None;
						peer.block_request_timestamp = None;
						trace!(target: "sync", "Ignoring mismatched response packet from {} (expected {} or {} got {})",
							who,
							block_request.id,
							justification_request.id,
							response.id,
						);
						return None;
					}
				},
				(Some(block_request), None) => {
					if block_request.id == response.id {
						peer.block_request_timestamp = None;
						block_request
					} else {
						peer.block_request_timestamp = None;
						trace!(target: "sync", "Ignoring mismatched response packet from {} (expected {} got {})",
							who,
							block_request.id,
							response.id,
						);
						return None;
					}
				},
				(None, Some(justification_request)) => {
					if justification_request.id == response.id {
						peer.justification_request_timestamp = None;
						justification_request
					} else {
						peer.justification_request_timestamp = None;
						trace!(target: "sync", "Ignoring mismatched response packet from {} (expected {} got {})",
							who,
							justification_request.id,
							response.id,
						);
						return None;
					}
				},
				(None, None) => {
					let _ = self
						.network_chan
						.send(NetworkMsg::ReportPeer(who, Severity::Bad("Unexpected response packet received from peer".to_string())));
					return None;
				},
			}
		} else {
			let _ = self
				.network_chan
				.send(NetworkMsg::ReportPeer(who, Severity::Bad("Unexpected packet received from peer".to_string())));
			return None;
		};

		Some(request)
	}

	/// Returns protocol status
	fn status(&mut self, sender: Sender<ProtocolStatus<B>>) {
		let status = ProtocolStatus {
			sync: self.sync.status(),
			num_peers: self.context_data.peers.values().count(),
			num_active_peers: self
				.context_data
				.peers
				.values()
				.filter(|p| p.block_request.is_some())
				.count(),
		};
		let _ = sender.send(status);
	}

	fn on_custom_message(&mut self, who: NodeIndex, message: Message<B>) {
		match message {
			GenericMessage::Status(s) => self.on_status_message(who, s),
			GenericMessage::BlockRequest(r) => self.on_block_request(who, r),
			GenericMessage::BlockResponse(r) => {
				if let Some(request) = self.handle_response(who, &r) {
					self.on_block_response(who, request, r);
				}
			},
			GenericMessage::BlockAnnounce(announce) => self.on_block_announce(who, announce),
			GenericMessage::Transactions(m) => self.on_extrinsics(who, m),
			GenericMessage::RemoteCallRequest(request) => self.on_remote_call_request(who, request),
			GenericMessage::RemoteCallResponse(response) => self.on_remote_call_response(who, response),
			GenericMessage::RemoteReadRequest(request) => self.on_remote_read_request(who, request),
			GenericMessage::RemoteReadResponse(response) => self.on_remote_read_response(who, response),
			GenericMessage::RemoteHeaderRequest(request) => self.on_remote_header_request(who, request),
			GenericMessage::RemoteHeaderResponse(response) => self.on_remote_header_response(who, response),
			GenericMessage::RemoteChangesRequest(request) => self.on_remote_changes_request(who, request),
			GenericMessage::RemoteChangesResponse(response) => self.on_remote_changes_response(who, response),
			GenericMessage::Consensus(topic, msg, broadcast) => {
				self.consensus_gossip.on_incoming(
					&mut ProtocolContext::new(&mut self.context_data, &self.network_chan),
					who,
					topic,
					msg,
					broadcast,
				);
			}
			other => self.specialization.on_message(
				&mut ProtocolContext::new(&mut self.context_data, &self.network_chan),
				who,
				&mut Some(other),
			),
		}
	}

	fn send_message(&mut self, who: NodeIndex, message: Message<B>) {
		send_message::<B, H>(
			&mut self.context_data.peers,
			&self.network_chan,
			who,
			message,
		);
	}

	fn gossip_consensus_message(&mut self, topic: B::Hash, message: Vec<u8>, broadcast: bool) {
		self.consensus_gossip.multicast(
			&mut ProtocolContext::new(&mut self.context_data, &self.network_chan),
			topic,
			message,
			broadcast,
		);
	}

	/// Called when a new peer is connected
	fn on_peer_connected(&mut self, who: NodeIndex, debug_info: String) {
		trace!(target: "sync", "Connecting {}: {}", who, debug_info);
		self.handshaking_peers.insert(who, time::Instant::now());
		self.send_status(who);
	}

	/// Called by peer when it is disconnecting
	fn on_peer_disconnected(&mut self, peer: NodeIndex, debug_info: String) {
		trace!(target: "sync", "Disconnecting {}: {}", peer, debug_info);
		// lock all the the peer lists so that add/remove peer events are in order
		let removed = {
			self.handshaking_peers.remove(&peer);
			self.context_data.peers.remove(&peer).is_some()
		};
		if removed {
			let mut context = ProtocolContext::new(&mut self.context_data, &self.network_chan);
			self.consensus_gossip.peer_disconnected(&mut context, peer);
			self.sync.peer_disconnected(&mut context, peer);
			self.specialization.on_disconnect(&mut context, peer);
			self.on_demand.as_ref().map(|s| s.on_disconnect(peer));
		}
	}

	/// Called as a back-pressure mechanism if the networking detects that the peer cannot process
	/// our messaging rate fast enough.
	pub fn on_clogged_peer(
		&self,
		who: NodeIndex,
		_message: Option<Message<B>>,
	) {
		// We don't do anything but print some diagnostics for now.
		if let Some(peer) = self.context_data.peers.get(&who) {
			debug!(target: "sync", "Clogged peer {} (protocol_version: {:?}; roles: {:?}; \
				known_extrinsics: {:?}; known_blocks: {:?}; best_hash: {:?}; best_number: {:?})",
				who, peer.protocol_version, peer.roles, peer.known_extrinsics, peer.known_blocks,
				peer.best_hash, peer.best_number);
		} else {
			debug!(target: "sync", "Peer clogged before being properly connected");
		}
	}

	fn on_block_request(&mut self, peer: NodeIndex, request: message::BlockRequest<B>) {
		trace!(target: "sync", "BlockRequest {} from {}: from {:?} to {:?} max {:?}",
			request.id,
			peer,
			request.from,
			request.to,
			request.max);
		let mut blocks = Vec::new();
		let mut id = match request.from {
			message::FromBlock::Hash(h) => BlockId::Hash(h),
			message::FromBlock::Number(n) => BlockId::Number(n),
		};
		let max = cmp::min(request.max.unwrap_or(u32::max_value()), MAX_BLOCK_DATA_RESPONSE) as usize;
		let get_header = request.fields.contains(message::BlockAttributes::HEADER);
		let get_body = request.fields.contains(message::BlockAttributes::BODY);
		let get_justification = request
			.fields
			.contains(message::BlockAttributes::JUSTIFICATION);
		while let Some(header) = self.context_data.chain.header(&id).unwrap_or(None) {
			if blocks.len() >= max {
				break;
			}
			let number = header.number().clone();
			let hash = header.hash();
			let parent_hash = header.parent_hash().clone();
			let justification = if get_justification { self.context_data.chain.justification(&BlockId::Hash(hash)).unwrap_or(None) } else { None };
			let block_data = message::generic::BlockData {
				hash: hash,
				header: if get_header { Some(header) } else { None },
				body: if get_body {
					self.context_data
						.chain
						.body(&BlockId::Hash(hash))
						.unwrap_or(None)
				} else {
					None
				},
				receipt: None,
				message_queue: None,
				justification,
			};
			blocks.push(block_data);
			match request.direction {
				message::Direction::Ascending => id = BlockId::Number(number + As::sa(1)),
				message::Direction::Descending => {
					if number == As::sa(0) {
						break;
					}
					id = BlockId::Hash(parent_hash)
				}
			}
		}
		let response = message::generic::BlockResponse {
			id: request.id,
			blocks: blocks,
		};
		trace!(target: "sync", "Sending BlockResponse with {} blocks", response.blocks.len());
		self.send_message(peer, GenericMessage::BlockResponse(response))
	}

	fn on_block_response(
		&mut self,
		peer: NodeIndex,
		request: message::BlockRequest<B>,
		response: message::BlockResponse<B>,
	) {
		let blocks_range = match (
				response.blocks.first().and_then(|b| b.header.as_ref().map(|h| h.number())),
				response.blocks.last().and_then(|b| b.header.as_ref().map(|h| h.number())),
			) {
				(Some(first), Some(last)) if first != last => format!(" ({}..{})", first, last),
				(Some(first), Some(_)) => format!(" ({})", first),
				_ => Default::default(),
			};
		trace!(target: "sync", "BlockResponse {} from {} with {} blocks {}",
			response.id, peer, response.blocks.len(), blocks_range);

		// TODO [andre]: move this logic to the import queue so that
		// justifications are imported asynchronously (#1482)
		if request.fields == message::BlockAttributes::JUSTIFICATION {
			self.sync.on_block_justification_data(
				&mut ProtocolContext::new(&mut self.context_data, &self.network_chan),
				peer,
				request,
				response,
			);
		} else {
			// import_queue.import_blocks also acquires sync.write();
			// Break the cycle by doing these separately from the outside;
			let new_blocks = {
				self.sync.on_block_data(&mut ProtocolContext::new(&mut self.context_data, &self.network_chan), peer, request, response)
			};

			if let Some((origin, new_blocks)) = new_blocks {
				let import_queue = self.sync.import_queue();
				import_queue.import_blocks(origin, new_blocks);
			}
		}
	}

	/// Perform time based maintenance.
	fn tick(&mut self) {
		self.consensus_gossip.collect_garbage(|_| true);
		self.maintain_peers();
		self.sync.tick(&mut ProtocolContext::new(&mut self.context_data, &self.network_chan));
		self.on_demand
			.as_ref()
			.map(|s| s.maintain_peers());
	}

	fn maintain_peers(&mut self) {
		let tick = time::Instant::now();
		let mut aborting = Vec::new();
		{
			for (who, timestamp) in self
				.context_data
				.peers
				.iter()
				.filter_map(|(id, peer)| peer.min_request_timestamp().map(|r| (id, r)))
				.chain(self.handshaking_peers.iter())
			{
				if (tick - *timestamp).as_secs() > REQUEST_TIMEOUT_SEC {
					trace!(target: "sync", "Timeout {}", who);
					aborting.push(*who);
				}
			}
		}

		self.specialization
			.maintain_peers(&mut ProtocolContext::new(
				&mut self.context_data,
				&self.network_chan,
			));
		for p in aborting {
			let _ = self
				.network_chan
				.send(NetworkMsg::ReportPeer(p, Severity::Timeout));
		}
	}

	#[allow(dead_code)]
	fn peer_info(&mut self, peer: NodeIndex) -> Option<PeerInfo<B>> {
		self.context_data.peers.get(&peer).map(|p| PeerInfo {
			roles: p.roles,
			protocol_version: p.protocol_version,
			best_hash: p.best_hash,
			best_number: p.best_number,
		})
	}

	/// Called by peer to report status
	fn on_status_message(&mut self, who: NodeIndex, status: message::Status<B>) {
		trace!(target: "sync", "New peer {} {:?}", who, status);
		{
			if self.context_data.peers.contains_key(&who) {
				debug!("Unexpected status packet from {}", who);
				return;
			}
			if status.genesis_hash != self.genesis_hash {
				let reason = format!(
					"Peer is on different chain (our genesis: {} theirs: {})",
					self.genesis_hash, status.genesis_hash
				);
				self.network_chan.send(NetworkMsg::ReportPeer(
					who,
					Severity::Bad(reason),
				));
				return;
			}
			if status.version != CURRENT_VERSION {
				let reason = format!("Peer using unsupported protocol version {}", status.version);
				self.network_chan.send(NetworkMsg::ReportPeer(
					who,
					Severity::Bad(reason),
				));
				return;
			}
			if self.config.roles & Roles::LIGHT == Roles::LIGHT {
				let self_best_block = self
					.context_data
					.chain
					.info()
					.ok()
					.and_then(|info| info.best_queued_number)
					.unwrap_or_else(|| Zero::zero());
				let blocks_difference = self_best_block
					.as_()
					.checked_sub(status.best_number.as_())
					.unwrap_or(0);
				if blocks_difference > LIGHT_MAXIMAL_BLOCKS_DIFFERENCE {
					self.network_chan.send(NetworkMsg::ReportPeer(
						who,
						Severity::Useless(
							"Peer is far behind us and will unable to serve light requests"
								.to_string(),
						),
					));
					return;
				}
			}

			let peer = Peer {
				protocol_version: status.version,
				roles: status.roles,
				best_hash: status.best_hash,
				best_number: status.best_number,
				block_request: None,
				block_request_timestamp: None,
				justification_request: None,
				justification_request_timestamp: None,
				known_extrinsics: HashSet::new(),
				known_blocks: HashSet::new(),
				next_request_id: 0,
			};
			self.context_data.peers.insert(who.clone(), peer);
			self.handshaking_peers.remove(&who);
			debug!(target: "sync", "Connected {}", who);
		}

		let mut context = ProtocolContext::new(&mut self.context_data, &self.network_chan);
		self.on_demand
			.as_ref()
			.map(|s| s.on_connect(who, status.roles, status.best_number));
		self.sync.new_peer(&mut context, who);
		self.consensus_gossip
			.new_peer(&mut context, who, status.roles);
		self.specialization.on_connect(&mut context, who, status);
	}

	/// Called when peer sends us new extrinsics
	fn on_extrinsics(&mut self, who: NodeIndex, extrinsics: message::Transactions<B::Extrinsic>) {
		// Accept extrinsics only when fully synced
		if self.sync.status().state != SyncState::Idle {
			trace!(target: "sync", "{} Ignoring extrinsics while syncing", who);
			return;
		}
		trace!(target: "sync", "Received {} extrinsics from {}", extrinsics.len(), who);
		if let Some(ref mut peer) = self.context_data.peers.get_mut(&who) {
			for t in extrinsics {
				if let Some(hash) = self.transaction_pool.import(&t) {
					peer.known_extrinsics.insert(hash);
				} else {
					trace!(target: "sync", "Extrinsic rejected");
				}
			}
		}
	}

	/// Called when we propagate ready extrinsics to peers.
	fn propagate_extrinsics(&mut self) {
		debug!(target: "sync", "Propagating extrinsics");

		// Accept transactions only when fully synced
		if self.sync.status().state != SyncState::Idle {
			return;
		}

		let extrinsics = self.transaction_pool.transactions();
		// FIXME: find a way to remove this vec. https://github.com/paritytech/substrate/issues/1698
		let mut will_send = vec![];
		let mut propagated_to = HashMap::new();
		for (who, ref mut peer) in self.context_data.peers.iter_mut() {
			let (hashes, to_send): (Vec<_>, Vec<_>) = extrinsics
				.iter()
				.filter(|&(ref hash, _)| peer.known_extrinsics.insert(hash.clone()))
				.cloned()
				.unzip();

			if !to_send.is_empty() {
				let (sender, port) = channel::unbounded();
				let _ = self
					.network_chan
					.send(NetworkMsg::GetPeerId(who.clone(), sender));
				let node_id = port.recv().expect("1. We are running 2. Network should be running too.");
				if let Some(id) = node_id {
					for hash in hashes {
						propagated_to
							.entry(hash)
							.or_insert_with(Vec::new)
							.push(id.clone());
					}
				}
				trace!(target: "sync", "Sending {} transactions to {}", to_send.len(), who);
				will_send.push((who.clone(), to_send));
			}
		}
		for (who, to_send) in will_send {
			self.send_message(who, GenericMessage::Transactions(to_send));
		}
		self.transaction_pool.on_broadcasted(propagated_to);
	}

	/// Make sure an important block is propagated to peers.
	///
	/// In chain-based consensus, we often need to make sure non-best forks are
	/// at least temporarily synced.
	pub fn announce_block(&mut self, hash: B::Hash) {
		let header = match self.context_data.chain.header(&BlockId::Hash(hash)) {
			Ok(Some(header)) => header,
			Ok(None) => {
				warn!("Trying to announce unknown block: {}", hash);
				return;
			}
			Err(e) => {
				warn!("Error reading block header {}: {:?}", hash, e);
				return;
			}
		};
		let hash = header.hash();

		// FIXME: find a way to remove this vec. https://github.com/paritytech/substrate/issues/1698
		let mut to_send = vec![];
		for (who, ref mut peer) in self.context_data.peers.iter_mut() {
			trace!(target: "sync", "Reannouncing block {:?} to {}", hash, who);
			peer.known_blocks.insert(hash);
			to_send.push(who.clone());
		}
		for who in to_send {
			self.send_message(who, GenericMessage::BlockAnnounce(message::BlockAnnounce {
				header: header.clone()
			}));
		}
	}

	/// Send Status message
	fn send_status(&mut self, who: NodeIndex) {
		if let Ok(info) = self.context_data.chain.info() {
			let status = message::generic::Status {
				version: CURRENT_VERSION,
				genesis_hash: info.chain.genesis_hash,
				roles: self.config.roles.into(),
				best_number: info.chain.best_number,
				best_hash: info.chain.best_hash,
				chain_status: self.specialization.status(),
			};
			self.send_message(who, GenericMessage::Status(status))
		}
	}

	fn abort(&mut self) {
		self.sync.clear();
		self.specialization.on_abort();
		self.context_data.peers.clear();
		self.handshaking_peers.clear();
		self.consensus_gossip.abort();
	}

	fn stop(&mut self) {
		// stop processing import requests first (without holding a sync lock)
		let import_queue = self.sync.import_queue();
		import_queue.stop();

		// and then clear all the sync data
		self.abort();
	}

	fn on_block_announce(&mut self, who: NodeIndex, announce: message::BlockAnnounce<B::Header>) {
		let header = announce.header;
		let hash = header.hash();
		{
			if let Some(ref mut peer) = self.context_data.peers.get_mut(&who) {
				peer.known_blocks.insert(hash.clone());
			}
		}
		self.on_demand
			.as_ref()
			.map(|s| s.on_block_announce(who, *header.number()));
		self.sync.on_block_announce(
			&mut ProtocolContext::new(&mut self.context_data, &self.network_chan),
			who,
			hash,
			&header,
		);
	}

	fn on_block_imported(&mut self, hash: B::Hash, header: &B::Header) {
		self.sync.update_chain_info(&header);
		self.specialization.on_block_imported(
			&mut ProtocolContext::new(&mut self.context_data, &self.network_chan),
			hash.clone(),
			header,
		);

		// blocks are not announced by light clients
		if self.config.roles & Roles::LIGHT == Roles::LIGHT {
			return;
		}

		// send out block announcements

		// FIXME: find a way to remove this vec. https://github.com/paritytech/substrate/issues/1698
		let mut to_send = vec![];
		for (who, ref mut peer) in self.context_data.peers.iter_mut() {
			if peer.known_blocks.insert(hash.clone()) {
				trace!(target: "sync", "Announcing block {:?} to {}", hash, who);
				to_send.push(who.clone());
			}
		}
		for who in to_send {
			self.send_message(
				who,
				GenericMessage::BlockAnnounce(message::BlockAnnounce {
					header: header.clone(),
				}),
			);
		}
	}

	fn on_block_finalized(&mut self, hash: B::Hash, header: &B::Header) {
		self.sync.block_finalized(&hash, *header.number());
	}

	fn on_remote_call_request(
		&mut self,
		who: NodeIndex,
		request: message::RemoteCallRequest<B::Hash>,
	) {
		trace!(target: "sync", "Remote call request {} from {} ({} at {})", request.id, who, request.method, request.block);
		let proof = match self.context_data.chain.execution_proof(
			&request.block,
			&request.method,
			&request.data,
		) {
			Ok((_, proof)) => proof,
			Err(error) => {
				trace!(target: "sync", "Remote call request {} from {} ({} at {}) failed with: {}",
					request.id, who, request.method, request.block, error);
				Default::default()
			}
		};

		self.send_message(
			who,
			GenericMessage::RemoteCallResponse(message::RemoteCallResponse {
				id: request.id,
				proof,
			}),
		);
	}

	fn on_remote_call_response(&mut self, who: NodeIndex, response: message::RemoteCallResponse) {
		trace!(target: "sync", "Remote call response {} from {}", response.id, who);
		self.on_demand
			.as_ref()
			.map(|s| s.on_remote_call_response(who, response));
	}

	fn on_remote_read_request(
		&mut self,
		who: NodeIndex,
		request: message::RemoteReadRequest<B::Hash>,
	) {
		trace!(target: "sync", "Remote read request {} from {} ({} at {})",
			request.id, who, request.key.to_hex::<String>(), request.block);
		let proof = match self.context_data.chain.read_proof(&request.block, &request.key) {
			Ok(proof) => proof,
			Err(error) => {
				trace!(target: "sync", "Remote read request {} from {} ({} at {}) failed with: {}",
					request.id, who, request.key.to_hex::<String>(), request.block, error);
				Default::default()
			}
		};
		self.send_message(
			who,
			GenericMessage::RemoteReadResponse(message::RemoteReadResponse {
				id: request.id,
				proof,
			}),
		);
	}
	fn on_remote_read_response(&mut self, who: NodeIndex, response: message::RemoteReadResponse) {
		trace!(target: "sync", "Remote read response {} from {}", response.id, who);
		self.on_demand
			.as_ref()
			.map(|s| s.on_remote_read_response(who, response));
	}

	fn on_remote_header_request(
		&mut self,
		who: NodeIndex,
		request: message::RemoteHeaderRequest<NumberFor<B>>,
	) {
		trace!(target: "sync", "Remote header proof request {} from {} ({})",
			request.id, who, request.block);
		let (header, proof) = match self.context_data.chain.header_proof(request.block) {
			Ok((header, proof)) => (Some(header), proof),
			Err(error) => {
				trace!(target: "sync", "Remote header proof request {} from {} ({}) failed with: {}",
					request.id, who, request.block, error);
				(Default::default(), Default::default())
			}
		};
		self.send_message(
			who,
			GenericMessage::RemoteHeaderResponse(message::RemoteHeaderResponse {
				id: request.id,
				header,
				proof,
			}),
		);
	}

	fn on_remote_header_response(
		&mut self,
		who: NodeIndex,
		response: message::RemoteHeaderResponse<B::Header>,
	) {
		trace!(target: "sync", "Remote header proof response {} from {}", response.id, who);
		self.on_demand
			.as_ref()
			.map(|s| s.on_remote_header_response(who, response));
	}

	fn on_remote_changes_request(
		&mut self,
		who: NodeIndex,
		request: message::RemoteChangesRequest<B::Hash>,
	) {
		trace!(target: "sync", "Remote changes proof request {} from {} for key {} ({}..{})",
			request.id, who, request.key.to_hex::<String>(), request.first, request.last);
		let key = StorageKey(request.key);
		let proof = match self.context_data.chain.key_changes_proof(request.first, request.last, request.min, request.max, &key) {
			Ok(proof) => proof,
			Err(error) => {
				trace!(target: "sync", "Remote changes proof request {} from {} for key {} ({}..{}) failed with: {}",
					request.id, who, key.0.to_hex::<String>(), request.first, request.last, error);
				ChangesProof::<B::Header> {
					max_block: Zero::zero(),
					proof: vec![],
					roots: BTreeMap::new(),
					roots_proof: vec![],
				}
			}
		};
		self.send_message(
			who,
			GenericMessage::RemoteChangesResponse(message::RemoteChangesResponse {
				id: request.id,
				max: proof.max_block,
				proof: proof.proof,
				roots: proof.roots.into_iter().collect(),
				roots_proof: proof.roots_proof,
			}),
		);
	}

	fn on_remote_changes_response(
		&mut self,
		who: NodeIndex,
		response: message::RemoteChangesResponse<NumberFor<B>, B::Hash>,
	) {
		trace!(target: "sync", "Remote changes proof response {} from {} (max={})",
			response.id, who, response.max);
		self.on_demand
			.as_ref()
			.map(|s| s.on_remote_changes_response(who, response));
	}
}

fn send_message<B: BlockT, H: ExHashT>(
	peers: &mut HashMap<NodeIndex, Peer<B, H>>,
	network_chan: &NetworkChan,
	who: NodeIndex,
	mut message: Message<B>,
) {
	match message {
		GenericMessage::BlockRequest(ref mut r) => {
			if let Some(ref mut peer) = peers.get_mut(&who) {
				r.id = peer.next_request_id;
				peer.next_request_id = peer.next_request_id + 1;

				if r.fields == message::BlockAttributes::JUSTIFICATION {
					peer.justification_request = Some(r.clone());
					peer.justification_request_timestamp = Some(time::Instant::now());
				} else {
					peer.block_request = Some(r.clone());
					peer.block_request_timestamp = Some(time::Instant::now());
				}
			}
		}
		_ => (),
	}
	network_chan.send(NetworkMsg::Outgoing(who, message.encode()));
}

/// Construct a simple protocol that is composed of several sub protocols.
/// Each "sub protocol" needs to implement `Specialization` and needs to provide a `new()` function.
/// For more fine grained implementations, this macro is not usable.
///
/// # Example
///
/// ```nocompile
/// construct_simple_protocol! {
///     pub struct MyProtocol where Block = MyBlock {
///         consensus_gossip: ConsensusGossip<MyBlock>,
///         other_protocol: MyCoolStuff,
///     }
/// }
/// ```
///
/// You can also provide an optional parameter after `where Block = MyBlock`, so it looks like
/// `where Block = MyBlock, Status = consensus_gossip`. This will instruct the implementation to
/// use the `status()` function from the `ConsensusGossip` protocol. By default, `status()` returns
/// an empty vector.
#[macro_export]
macro_rules! construct_simple_protocol {
	(
		$( #[ $attr:meta ] )*
		pub struct $protocol:ident where
			Block = $block:ident
			$( , Status = $status_protocol_name:ident )*
		{
			$( $sub_protocol_name:ident : $sub_protocol:ident $( <$protocol_block:ty> )*, )*
		}
	) => {
		$( #[$attr] )*
		pub struct $protocol {
			$( $sub_protocol_name: $sub_protocol $( <$protocol_block> )*, )*
		}

		impl $protocol {
			/// Instantiate a node protocol handler.
			pub fn new() -> Self {
				Self {
					$( $sub_protocol_name: $sub_protocol::new(), )*
				}
			}
		}

		impl $crate::specialization::NetworkSpecialization<$block> for $protocol {
			fn status(&self) -> Vec<u8> {
				$(
					let status = self.$status_protocol_name.status();

					if !status.is_empty() {
						return status;
					}
				)*

				Vec::new()
			}

			fn on_connect(
				&mut self,
				_ctx: &mut $crate::Context<$block>,
				_who: $crate::NodeIndex,
				_status: $crate::StatusMessage<$block>
			) {
				$( self.$sub_protocol_name.on_connect(_ctx, _who, _status); )*
			}

			fn on_disconnect(&mut self, _ctx: &mut $crate::Context<$block>, _who: $crate::NodeIndex) {
				$( self.$sub_protocol_name.on_disconnect(_ctx, _who); )*
			}

			fn on_message(
				&mut self,
				_ctx: &mut $crate::Context<$block>,
				_who: $crate::NodeIndex,
				_message: &mut Option<$crate::message::Message<$block>>
			) {
				$( self.$sub_protocol_name.on_message(_ctx, _who, _message); )*
			}

			fn on_abort(&mut self) {
				$( self.$sub_protocol_name.on_abort(); )*
			}

			fn maintain_peers(&mut self, _ctx: &mut $crate::Context<$block>) {
				$( self.$sub_protocol_name.maintain_peers(_ctx); )*
			}

			fn on_block_imported(
				&mut self,
				_ctx: &mut $crate::Context<$block>,
				_hash: <$block as $crate::BlockT>::Hash,
				_header: &<$block as $crate::BlockT>::Header
			) {
				$( self.$sub_protocol_name.on_block_imported(_ctx, _hash, _header); )*
			}
		}
	}
}
