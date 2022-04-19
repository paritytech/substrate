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
use futures::{future, FutureExt, Stream, StreamExt};
use log::error;
use sc_client_api::{BlockchainEvents, FinalityNotification, UsageProvider};
use sc_utils::mpsc::tracing_unbounded;
pub use sp_finality_grandpa::{AuthorityId, AuthorityList, SetId};
use sp_runtime::traits::{Block as BlockT, Header, NumberFor};
use std::{
	collections::{BTreeMap, HashMap, HashSet},
	pin::Pin,
	sync::Arc,
};

// TODO could be a ratio with the number of hop
// require.
const LOW_MIXNET_THRESHOLD: usize = 5;

/// A number of block where we are still considered as synched
/// (do not turn mixnet off every time we are a few block late).
const UNSYNCH_FINALIZED_MARGIN: u32 = 10;

/// Mixnet running worker.
pub struct MixnetWorker<B: BlockT, C> {
	worker: mixnet::MixnetWorker<AuthorityStar>,
	finality_stream: sc_client_api::FinalityNotifications<B>,
	shared_authority_set:
		sc_finality_grandpa::SharedAuthoritySet<<B as BlockT>::Hash, NumberFor<B>>,
	session: Option<u64>,
	client: Arc<C>,
	state: State,
	connection_info: ConnectionInfo,
}

#[derive(PartialEq, Eq)]
enum State {
	Synching,
	WaitingMorePeers,
	Running,
}

struct NodeInfo {
	// This could be fetch from 'authority-discovery' but
	// an additional discovery is used to avoid the need
	// for non authority consimer to join the authority discovery.
	authority: Option<RoutingPeerInfo>,
}

impl<B, C> MixnetWorker<B, C>
where
	B: BlockT,
	C: UsageProvider<B> + BlockchainEvents<B>,
{
	pub fn new(
		client: Arc<C>,
		shared_authority_set: sc_finality_grandpa::SharedAuthoritySet<
			<B as BlockT>::Hash,
			NumberFor<B>,
		>,
		//		role: sc_network::config::Role,
		local_identity: libp2p::core::identity::Keypair,
		authority_id: Option<AuthorityId>,
		key_store: &dyn SyncCryptoStore,
	) -> Option<(Self, WorkerSink, WorkerStream, Vec<u8>)> {
		let finality_stream = client.finality_notification_stream();
		if let libp2p::core::identity::Keypair::Ed25519(kp) = &local_identity {
			let local_public_key = local_identity.public();
			let mixnet_config =
				mixnet::Config::new_with_ed25519_keypair(kp, local_public_key.clone().into());
			// TODO read validator from session
			// TODO is this node part of session (role means nothing).
			let topology = AuthorityStar::new(local_public_key.clone().into());
			let (to_worker_sink, to_worker_stream) = tracing_unbounded("mpsc_mixnet_in");
			let (from_worker_sink, from_worker_stream) = tracing_unbounded("mpsc_mixnet_out");
			/*						let commands =
			crate::mixnet::AuthorityStar::command_stream(&mut event_streams);*/
			let worker = mixnet::MixnetWorker::new(
				mixnet_config,
				topology,
				Box::pin(to_worker_stream),
				Box::pin(from_worker_sink),
			);

			let connection_info = if let Some(authority_id) = authority_id {
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
			};
			let encoded_connection_info = AuthorityStar::encoded_connection_info(&connection_info);
			let state = State::Synching;
			Some((
				MixnetWorker {
					worker,
					finality_stream,
					shared_authority_set,
					session: None,
					client,
					state,
					connection_info,
				},
				Box::pin(to_worker_sink),
				Box::pin(from_worker_stream),
				encoded_connection_info,
			))
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
			self.handle_new_authority(authority_set, session);
		}
		// TODO change in crate to use directly as a future..
		loop {
			futures::select! {
				notif = self.finality_stream.next().fuse() => {
					if let Some(notif) = notif {
						self.handle_new_finalize_block(notif);
					}
				},
				_ = future::poll_fn(|cx| self.worker.poll(cx)).fuse() => (),
				// TODO a Delay that if too long without finalization will put state back to in synch
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
		}

		// TODO move the processing out of the stream and into the worker.
		let new_session = self.shared_authority_set.set_id();
		if self.session.map(|session| new_session != session).unwrap_or(true) {
			let authority_set = self.shared_authority_set.current_authority_list();
			self.handle_new_authority(authority_set, new_session);
		}
	}

	fn handle_new_authority(&mut self, set: AuthorityList, session: SetId) {
		self.session = Some(session);
		if let Some(topology) = self.worker.topology_mut() {
			topology.change_authorities(set);
			if topology.as_enough_nodes() {
				self.state = State::Running
			} else {
				self.state = State::WaitingMorePeers;
			}
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
	current_authorities: HashMap<AuthorityId, Option<MixPeerId>>,
	connected_nodes: HashMap<MixPeerId, NodeInfo>,
	connected_authorities: HashMap<AuthorityId, MixPeerId>,
	routing_nodes: BTreeMap<MixPeerId, RoutingPeerInfo>,
	node_id: MixPeerId,
	// Is this node part of the topology and routing message.
	routing: bool,
}

/// Information related to a peer in the mixnet topology.
#[derive(Clone)]
pub struct RoutingPeerInfo {
	id: MixPeerId,
	authority_id: AuthorityId,
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
			routing_nodes: BTreeMap::new(),
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

	fn change_authorities(&mut self, new_set: AuthorityList) {
		self.current_authorities.clear();
		self.routing_nodes.clear();
		self.routing = false;
		let mut auth_peer_id = None;
		for (auth, _) in new_set.into_iter() {
			if let Some(node_id) = self.connected_authorities.get(&auth) {
				if &self.node_id == node_id {
					self.routing = true;
				}
				auth_peer_id = Some(node_id.clone());
				if let Some(NodeInfo { authority: Some(routing_info) }) =
					self.connected_nodes.get(node_id)
				{
					self.routing_nodes.insert(node_id.clone(), routing_info.clone());
				}
			}
			self.current_authorities.insert(auth, auth_peer_id);
		}
	}

	fn as_enough_nodes(&self) -> bool {
		self.routing_nodes.len() >= LOW_MIXNET_THRESHOLD
	}
}

/// Shared information between peers of the mixnet.
#[derive(Encode, Decode)]
pub struct ConnectionInfo {
	/// As in authority delivery we assert the peer id is owned by the authority id.
	/// If `None`, the node is consumer only (will never route).
	authority_id: Option<(AuthorityId, Vec<u8>)>,
}

impl Topology for AuthorityStar {
	type ConnectionInfo = ConnectionInfo;

	fn random_recipient(&self) -> Option<MixPeerId> {
		use rand::RngCore;
		if !self.as_enough_nodes() {
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
			Some(key.1.id.clone())
		} else {
			self.routing_nodes.range(..ix).rev().next().map(|key| key.1.id.clone())
		}
	}

	/// For a given peer return a list of peers it is supposed to be connected to.
	/// Return `None` if peer is unknown to the topology.
	/// TODO when `None` allow sending even if not part of topology but in the mixnet:
	/// external hop for latest (see gen_path function). Then last hop will expose
	/// a new connection, so it need to be an additional hop (if possible).
	fn neighbors(&self, id: &MixPeerId) -> Option<Vec<(MixPeerId, MixPublicKey)>> {
		// TODO check maintaining neighbor table
		None
	}

	fn routing(&self) -> bool {
		self.routing
	}

	fn encoded_connection_info(info: &Self::ConnectionInfo) -> Vec<u8> {
		info.encode()
	}

	fn read_connection_info(encoded: &[u8]) -> Option<Self::ConnectionInfo> {
		let encoded = &mut &encoded[..];
		let info = Decode::decode(encoded);
		if encoded.len() > 0 {
			return None
		}
		info.ok()
	}

	fn connected(&mut self, _: MixPeerId, _: MixPublicKey, _: Self::ConnectionInfo) {
		unimplemented!("TODO");
	}

	fn disconnect(&mut self, _: &MixPeerId) {
		unimplemented!("TODO");
	}
}
/*
fn event_filter(event: &Event) -> bool {
	match event {
		Event::NotificationStreamOpened { .. } | Event::NotificationStreamClosed { .. } => true,
		_ => false,
	}
}*/
