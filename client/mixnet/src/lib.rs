// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

#![warn(unused_extern_crates)]

//!
//! Substrate-specific mixnet usage.
//!
//! Topology specific to substrate and utils to link to network.

use mixnet::{MixPeerId, MixPublicKey, Topology};

pub use mixnet::{WorkerSink, WorkerStream};
use sp_application_crypto::key_types;
use sp_keystore::SyncCryptoStore;

use codec::{Decode, Encode};
use futures::{channel::mpsc::SendError, future, FutureExt, Stream, StreamExt};

use futures::{channel::oneshot, future::OptionFuture};
use log::{debug, error};
use sc_client_api::{BlockchainEvents, FinalityNotification, UsageProvider};
use sp_api::{ApiExt, ProvideRuntimeApi};
use sc_network::MixnetCommand;
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
pub use sp_finality_grandpa::{AuthorityId, AuthorityList, SetId};
use sp_runtime::traits::{Block as BlockT, Header, NumberFor};
use std::{
	collections::{BTreeSet, HashMap, HashSet, VecDeque},
	pin::Pin,
	sync::Arc,
};
use sp_session::SessionKeys;

// TODO could be a ratio with the number of hop
// require.
const LOW_MIXNET_THRESHOLD: usize = 5;

/// A number of block where we are still considered as synched
/// (do not turn mixnet off every time we are a few block late).
const UNSYNCH_FINALIZED_MARGIN: u32 = 10;

/// Mixnet running worker.
pub struct MixnetWorker<B: BlockT, C> {
	worker: mixnet::MixnetWorker<AuthorityStar>,
	// TODO use OnFinalityAction instead and update some shared cache.
	finality_stream: sc_client_api::FinalityNotifications<B>,
	shared_authority_set:
		sc_finality_grandpa::SharedAuthoritySet<<B as BlockT>::Hash, NumberFor<B>>,
	session: Option<u64>,
	client: Arc<C>,
	state: State,
	//	connection_info: ConnectionInfo,
	authority_discovery_service: sc_authority_discovery::Service,
	command_sink: TracingUnboundedSender<MixnetCommand>,
	command_stream: TracingUnboundedReceiver<MixnetCommand>,
	authority_replies: VecDeque<AuthorityRx>,
	authority_queries: VecDeque<AuthorityId>,
}

// TODO consider restoring a command support in mixnet
type WorkerChannels = (
	mixnet::WorkerChannels,
	TracingUnboundedSender<MixnetCommand>,
	TracingUnboundedReceiver<MixnetCommand>,
);

type AuthorityRx = oneshot::Receiver<Option<HashSet<sc_network::Multiaddr>>>;

#[derive(PartialEq, Eq)]
enum State {
	Synching,
	WaitingMorePeers,
	Running,
}

/// Instantiate channels needed to spawn and communicate with the mixnet worker.
pub fn new_channels(
) -> (WorkerChannels, (WorkerSink, WorkerStream, TracingUnboundedSender<MixnetCommand>)) {
	let (to_worker_sink, to_worker_stream) = tracing_unbounded("mpsc_mixnet_in");
	let (from_worker_sink, from_worker_stream) = tracing_unbounded("mpsc_mixnet_out");
	let (command_sink, command_stream) = tracing_unbounded("mpsc_mixnet_commands");
	(
		(
			(Box::pin(from_worker_sink), Box::pin(to_worker_stream)),
			command_sink.clone(),
			command_stream,
		),
		(Box::pin(to_worker_sink), Box::pin(from_worker_stream), command_sink),
	)
}

impl<B, C> MixnetWorker<B, C>
where
	B: BlockT,
	C: UsageProvider<B> + BlockchainEvents<B> + ProvideRuntimeApi<B>,
	C::Api: SessionKeys<B>,
{
	pub fn new(
		inner_channels: WorkerChannels,
		client: Arc<C>,
		shared_authority_set: sc_finality_grandpa::SharedAuthoritySet<
			<B as BlockT>::Hash,
			NumberFor<B>,
		>,
		//		role: sc_network::config::Role,
		local_identity: libp2p::core::identity::Keypair,
		authority_discovery_service: sc_authority_discovery::Service,
		//authority_id: Option<AuthorityId>,
		//key_store: &dyn SyncCryptoStore,
	) -> Option<Self> {
		let finality_stream = client.finality_notification_stream();
		if let libp2p::core::identity::Keypair::Ed25519(kp) = &local_identity {
			let local_public_key = local_identity.public();
			let mixnet_config =
				mixnet::Config::new_with_ed25519_keypair(kp, local_public_key.clone().into());
			// TODO read validator from session
			// TODO is this node part of session (role means nothing).
			let topology = AuthorityStar::new(local_public_key.clone().into());
			/*						let commands =
			crate::mixnet::AuthorityStar::command_stream(&mut event_streams);*/
			let worker = mixnet::MixnetWorker::new(mixnet_config, topology, inner_channels.0);

			/*			let connection_info = if let Some(authority_id) = authority_id {
				use sp_application_crypto::Public;
				// TODO does the key changes between slot?
				if let Ok(Some(signature)) = SyncCryptoStore::sign_with(
					key_store,
					key_types::AUTHORITY_DISCOVERY,
					&authority_id.to_public_crypto_pair(),
					local_public_key.to_protobuf_encoding().as_slice(),
				) {
					ConnectionInfo { authority_id: Some((authority_id, signature)) }
				} else {
					log::error!(target: "mixnet", "Cannot sign handshake, mixnet routing disabled.");
					ConnectionInfo { authority_id: None }
				}
			} else {
				ConnectionInfo { authority_id: None }
			};*/
			//			let encoded_connection_info =
			// AuthorityStar::encoded_connection_info(&connection_info);
			let state = State::Synching;
			Some(
				MixnetWorker {
					worker,
					finality_stream,
					shared_authority_set,
					session: None,
					client,
					state,
					authority_discovery_service,
					command_sink: inner_channels.1,
					command_stream: inner_channels.2,
					authority_queries: VecDeque::new(),
					authority_replies: VecDeque::new(),
					//connection_info,
				},
				//encoded_connection_info,
			)
		} else {
			None
		}
	}

	pub async fn run(mut self) {
		let info = self.client.usage_info().chain;
		if info.finalized_number == 0u32.into() {
			// TODO this can be rather racy (init with genesis set then start synch and break on
			// first notification -> TODO remove, convenient for testing though (no need to way
			// first finality notification)
			let authority_set = self.shared_authority_set.current_authority_list();
			let session = self.shared_authority_set.set_id();
			self.handle_new_authority(authority_set, session, info.finalized_number);
		}
		// TODO change in crate to use directly as a future..
		loop {
			let mut pop_auth_query = false;
			futures::select! {
				auth_address = OptionFuture::from(self.authority_replies.get_mut(0)).fuse() => {
					if let Some(Ok(Some(addresses))) = auth_address {
						let auth_id = self.authority_queries.get(0).unwrap().clone();
						for addr in addresses {
							match sc_network::config::parse_addr(addr) {
								Ok((address, _)) => {
									// TODO MixnetCommand useless?
									self.handle_command(MixnetCommand::AuthorityId(auth_id.clone(), address));
								},
								Err(_) => continue,
							};
						}
						pop_auth_query = true; // TODO same for Ok(None)?
					}
				},
				notif = self.finality_stream.next().fuse() => {
					if let Some(notif) = notif {
						self.handle_new_finalize_block(notif);
					}
				},
				command = self.command_stream.next().fuse() => {
					if let Some(command) = command {
						self.handle_command(command);
					}
				},
				_ = future::poll_fn(|cx| self.worker.poll(cx)).fuse() => (),
				// TODO a Delay that if too long without finalization will put state back to in synch
			}

			if pop_auth_query {
				self.authority_queries.pop_front();
				self.authority_replies.pop_front();
			}
		}
	}

	/// Can mixnet be use?
	/// TODO use it in rpc.
	pub fn is_ready(&self) -> bool {
		self.state == State::Running
	}

	fn handle_new_finalize_block(&mut self, notif: FinalityNotification<B>) {
		let info = self.client.usage_info().chain; // these could be part of finality stream info?
		let best_finalized = info.finalized_number;
		if notif.header.number() < &(best_finalized - UNSYNCH_FINALIZED_MARGIN.into()) {
			self.state = State::Synching;
			return
		} else {
			self.update_state(true);
		}

		// TODO could just look frame sessing new event!!, this is currently inefficient.

		// TODO move the processing out of the stream and into the worker.
		let new_session = self.shared_authority_set.set_id();
		if self.session.map(|session| new_session != session).unwrap_or(true) {
			let authority_set = self.shared_authority_set.current_authority_list();
			self.handle_new_authority(authority_set, new_session, *notif.header.number());
		}
	}

	fn handle_command(&mut self, command: MixnetCommand) {
		match command {
			MixnetCommand::AuthorityId(authority_id, peer_id) => {
				if let Some(topology) = self.worker.topology_mut() {
					topology.add_authority_peer_id(authority_id, peer_id);
					self.update_state(false);
				}
			},
			MixnetCommand::Connected(peer_id, key) => {
				if let Some(topology) = self.worker.topology_mut() {
					topology.add_connected_peer(peer_id, key);
					self.update_state(false);
				}
			},
			MixnetCommand::Disconnected(peer_id) => {
				if let Some(topology) = self.worker.topology_mut() {
					topology.add_disconnected_peer(peer_id);
					self.update_state(false);
				}
			},
		}
	}

	fn handle_new_authority(&mut self, set: AuthorityList, session: SetId, at: NumberFor<B>) {
		self.session = Some(session);
		if let Some(topology) = self.worker.topology_mut() {
			topology.change_authorities::<B>(
				set,
				&mut self.authority_discovery_service,
				&mut self.authority_replies,
				&mut self.authority_queries,
				at,
			);
			self.update_state(false);
		}
	}

	fn update_state(&mut self, synched: bool) {
		match &self.state {
			State::Running => {
				if self.worker.topology().map(|t| !t.has_enough_nodes()).unwrap_or(false) {
					self.state = State::WaitingMorePeers;
				}
			},
			State::WaitingMorePeers => {
				if self.worker.topology().map(|t| t.has_enough_nodes()).unwrap_or(false) {
					debug!(target: "mixnet", "Running.");
					self.state = State::Running;
				}
			},
			State::Synching if synched => {
				if self.worker.topology().map(|t| t.has_enough_nodes()).unwrap_or(false) {
					debug!(target: "mixnet", "Running.");
					self.state = State::Running;
				} else {
					self.state = State::WaitingMorePeers;
				}
			},
			State::Synching => (),
		}
	}
}

/// Topology for mixnet.
/// This restrict the nodes for routing to authorities with stake.
///
/// Other nodes can join the swarm but will not be routing node.
///
/// When sending a message, the message can only reach nodes
/// that are part of the topology.
///
/// TODO allow validator/authorith to gossip/commit to a different
/// node.
/// TODO node with only mix component (proxying transaction and query).
pub struct AuthorityStar {
	node_id: MixPeerId,

	connected_nodes: HashMap<MixPeerId, NodeInfo>,
	connected_authorities: HashMap<AuthorityId, MixPeerId>,
	unconnected_authorities: HashMap<MixPeerId, AuthorityId>,

	routing: bool,
	current_authorities: HashMap<AuthorityId, Option<MixPeerId>>,
	routing_nodes: BTreeSet<MixPeerId>,
}

/// Information related to a peer in the mixnet topology.
#[derive(Clone)]
pub struct NodeInfo {
	id: MixPeerId,
	authority_id: Option<AuthorityId>,
	public_key: MixPublicKey,
}

impl AuthorityStar {
	/// Instantiate a new topology.
	pub fn new(node_id: MixPeerId) -> Self {
		AuthorityStar {
			node_id,
			current_authorities: HashMap::new(),
			connected_nodes: HashMap::new(),
			connected_authorities: HashMap::new(),
			routing_nodes: BTreeSet::new(),
			unconnected_authorities: HashMap::new(),
			routing: false,
		}
	}

	/*
	/// Build the command stream for this topology.
	pub fn command_stream(event_streams: &mut out_events::OutChannels) -> EventsStream {
		let (tx, rx) = out_events::channel("mixnet-handler", Some(event_filter));
		event_streams.push(tx);
		Box::pin(rx)
	}
	*/

	fn change_authorities<B: BlockT>(
		&mut self,
		new_set: AuthorityList,
		authority_discovery_service: &mut sc_authority_discovery::Service,
		authority_replies: &mut VecDeque<AuthorityRx>,
		authority_queries: &mut VecDeque<AuthorityId>,
		at: NumberFor<B>,
	) {
		debug!(target: "mixnet", "Change authorities {:?}", new_set);
		self.current_authorities.clear();
		self.routing_nodes.clear();
		self.unconnected_authorities.clear(); // TODO could keep for a few session
		self.routing = false;
		let mut auth_peer_id = None;
		for (auth, _) in new_set.into_iter() {
			if let Some(node_id) = self.connected_authorities.get(&auth) {
				if &self.node_id == node_id {
					self.routing = true;
				}
				auth_peer_id = Some(node_id.clone());
				if let Some(info @ NodeInfo { authority_id: Some(routing_info), .. }) =
					self.connected_nodes.get(node_id)
				{
					self.routing_nodes.insert(node_id.clone());
				} else {
					/* TODO auth from session cache
//		let at = sp_runtime::generic::BlockId::number(0u32.into());
//		self.client.runtime_api().session_index(&at);
					if let Some(rx) = authority_discovery_service.get_addresses_by_authority_id_callback(auth) {
						authority_queries.push_back(rx);
					}*/
				}
			}
			self.current_authorities.insert(auth, auth_peer_id);
		}
	}

	fn has_enough_nodes(&self) -> bool {
		self.routing_nodes.len() >= LOW_MIXNET_THRESHOLD
	}

	fn add_connected_peer(&mut self, peer_id: MixPeerId, key: MixPublicKey) {
		debug!(target: "mixnet", "Connected to mixnet {:?} {:?}", peer_id, key);
		if let Some(mut infos) = self.connected_nodes.get_mut(&peer_id) {
			infos.public_key = key;
			return
		}

		let authority_id = self.unconnected_authorities.remove(&peer_id);
		if let Some(authority_id) = authority_id.as_ref() {
			if self.current_authorities.contains_key(authority_id) {
				self.routing_nodes.insert(peer_id.clone());
			}
		}

		self.connected_nodes
			.insert(peer_id, NodeInfo { id: peer_id, authority_id, public_key: key });
	}

	fn add_disconnected_peer(&mut self, peer_id: MixPeerId) {
		debug!(target: "mixnet", "Disconnected from mixnet {:?}", peer_id);
		self.routing_nodes.remove(&peer_id);
		if let Some(NodeInfo { authority_id: Some(authority_id), .. }) =
			self.connected_nodes.remove(&peer_id)
		{
			if let Some(_peer_id) = self.connected_authorities.remove(&authority_id) {
				debug_assert!(_peer_id == peer_id);
				self.unconnected_authorities.insert(peer_id, authority_id);
			}
		}
	}

	fn add_authority_peer_id(&mut self, authority_id: AuthorityId, peer_id: MixPeerId) {
		debug!(target: "mixnet", "Add authority {:?} {:?}", authority_id, peer_id);
		let is_routing = match self.current_authorities.get_mut(&authority_id) {
			Some(old_id) => {
				if let Some(old_id) = old_id.as_ref() {
					if old_id != &peer_id {
						if let Some(mut infos) = self.connected_nodes.get_mut(old_id) {
							infos.authority_id = None;
						}
						self.routing_nodes.remove(old_id);
					}
				}
				*old_id = Some(peer_id.clone());
				true
			},
			_ => false,
		};

		if let Some(infos) = self.connected_nodes.get_mut(&peer_id) {
			if is_routing {
				self.routing_nodes.insert(peer_id.clone());
			}
			self.connected_authorities.insert(authority_id.clone(), peer_id);
			infos.authority_id = Some(authority_id);
		} else {
			self.unconnected_authorities.insert(peer_id, authority_id);
		}
	}
}

/*
/// Shared information between peers of the mixnet.
#[derive(Encode, Decode)]
pub struct ConnectionInfo {
	/// As in authority delivery we assert the peer id is owned by the authority id.
	/// If `None`, the node is consumer only (will never route).
	authority_id: Option<(AuthorityId, Vec<u8>)>,
}
*/

impl Topology for AuthorityStar {
	//type ConnectionInfo = ConnectionInfo;
	// TODO consider authority still only when really authority: but signing is awkward.
	// Probably consumer will not stay connected and rely only on auth discovery dht.
	// Gossip can be ok though: may be of use in gossip system (attach the neighbor too).
	// DHT is kind of gossip though.
	type ConnectionInfo = ();

	fn random_recipient(&self) -> Option<MixPeerId> {
		use rand::RngCore;
		if !self.has_enough_nodes() {
			debug!(target: "mixnet", "Not enough routing nodes for path.");
			return None
		}
		// Warning this assume that PeerId is a random value.
		// This is currently the case (sha256 of encoded ed25519 key).
		let mut ix = [0u8; 32];
		rand::thread_rng().fill_bytes(&mut ix[..]); // TODO can less than 32 bytes.
		let ix = match MixPeerId::from_bytes(&ix[..]) {
			Ok(ix) => ix,
			Err(err) => {
				error!(target: "mixnet", "Invalid key for mixnet random selection {:?}", err);
				return None
			},
		};
		if let Some(key) = self.routing_nodes.range(ix..).next() {
			if let Some(info) = self.connected_nodes.get(key) {
				debug!(target: "mixnet", "Random route node");
				Some(info.id.clone())
			} else {
				unreachable!()
			}
		} else {
			self.routing_nodes.range(..ix).rev().next().map(|key| {
				if let Some(info) = self.connected_nodes.get(key) {
					debug!(target: "mixnet", "Random route node");
					info.id.clone()
				} else {
					unreachable!()
				}
			})
		}
	}

	/// For a given peer return a list of peers it is supposed to be connected to.
	/// Return `None` if peer is unknown to the topology.
	/// TODO when `None` allow sending even if not part of topology but in the mixnet:
	/// external hop for latest (see gen_path function). Then last hop will expose
	/// a new connection, so it need to be an additional hop (if possible).
	fn neighbors(&self, id: &MixPeerId) -> Option<Vec<(MixPeerId, MixPublicKey)>> {
		debug!(target: "mixnet", "Neighbors.");

		if self.routing_nodes.contains(id) {
			Some(
				self.routing_nodes
					.iter()
					.map(|id| {
						(id.clone(), self.connected_nodes.get(id).unwrap().public_key.clone())
					})
					.collect(),
			)
		} else {
			None
		}
	}

	fn routing(&self) -> bool {
		self.routing
	}

	fn encoded_connection_info(info: &Self::ConnectionInfo) -> Vec<u8> {
		Vec::new()
		//info.encode()
	}

	fn read_connection_info(encoded: &[u8]) -> Option<Self::ConnectionInfo> {
		if encoded.len() == 0 {
			Some(())
		} else {
			None
		}
		/*		let encoded = &mut &encoded[..];
		let info = Decode::decode(encoded);
		if encoded.len() > 0 {
			return None
		}
		info.ok()*/
	}

	fn connected(&mut self, _: MixPeerId, _: MixPublicKey, _: Self::ConnectionInfo) {
		debug!(target: "mixnet", "Connected from internal");
		//		unimplemented!("TODO");
	}

	fn disconnect(&mut self, _: &MixPeerId) {
		debug!(target: "mixnet", "Disonnected from internal");
		//		unimplemented!("TODO");
	}
}
/*
fn event_filter(event: &Event) -> bool {
	match event {
		Event::NotificationStreamOpened { .. } | Event::NotificationStreamClosed { .. } => true,
		_ => false,
	}
}*/

/// Cache current session key on the chain.
struct SessionCache {
		//fn session_index() -> sp_staking::SessionIndex {
		//fn queued_keys() -> Vec<(Vec<u8>, Vec<sp_core::crypto::CryptoTypePublicPair>)> {
				// node_id: AccountId32
}
