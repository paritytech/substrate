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

use mixnet::{Error, MixPeerId, MixPublicKey, Topology};

pub use mixnet::{WorkerSink, WorkerStream};
use sp_application_crypto::key_types;
use sp_keystore::SyncCryptoStore;

use codec::{Decode, Encode};
use futures::{
	channel::{mpsc::SendError, oneshot},
	future,
	future::OptionFuture,
	FutureExt, Stream, StreamExt,
};
use futures_timer::Delay;
use log::{debug, error, warn};
use sc_client_api::{BlockchainEvents, FinalityNotification, UsageProvider};
use sc_network::MixnetCommand;
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use sp_api::{ApiExt, ProvideRuntimeApi};
use sp_core::crypto::CryptoTypePublicPair;
pub use sp_finality_grandpa::{AuthorityId, AuthorityList, SetId};
use sp_runtime::traits::{Block as BlockT, Header, NumberFor};
use sp_session::SessionKeys;
use std::{
	collections::{BTreeSet, HashMap, HashSet, VecDeque},
	pin::Pin,
	sync::Arc,
	time::Duration,
};

// TODO could be a ratio with the number of hop
// require.
const LOW_MIXNET_THRESHOLD: usize = 5;

/// A number of block where we are still considered as synched
/// (do not turn mixnet off every time we are a few block late).
const UNSYNCH_FINALIZED_MARGIN: u32 = 10;

const DELAY_CHECK_AUTHORITY_MS: u64 = 5_000;

// If delay pass without finalization, just go back to synching state.
// TODO need to be configurable (chain specific).
const DELAY_NO_FINALISATION_S: u64 = 60;

/// Mixnet running worker.
pub struct MixnetWorker<B: BlockT, C> {
	// current node authority_id
	authority_id: Option<AuthorityId>,
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
	authority_replies: VecDeque<Option<AuthorityRx>>,
	authority_queries: VecDeque<AuthorityInfo>,
	key_store: Arc<dyn SyncCryptoStore>,
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
		key_store: Arc<dyn SyncCryptoStore>,
		//authority-discovery which is slow).
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
					authority_id: None,
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
					key_store,
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
			// TODO this need to run when genesis built: on block import 1 or 0
		}
		let mut delay_poll_auth = Delay::new(Duration::from_millis(DELAY_CHECK_AUTHORITY_MS));
		let mut delay_finalized = Delay::new(Duration::from_secs(DELAY_NO_FINALISATION_S));
		let delay_poll_auth = &mut delay_poll_auth;
		let delay_finalized = &mut delay_finalized;
		// TODO change in crate to use directly as a future..
		loop {
			let mut pop_auth_query = false;
			let mut err_auth_query = false;
			let auth_poll = self.authority_replies.get_mut(0).map(Option::as_mut).flatten();
			let auth_poll = OptionFuture2(auth_poll);
			//future::poll_fn(|cx| auth_poll.map(|a|
			// Pin::new(a).poll(cx)).unwrap_or(futures::task::Poll::Pending)); TODO consider
			// stream_select
			futures::select! {
				// TODO poll more than first??
				auth_address = auth_poll.fuse() => {
					debug!(target: "mixnet", "Received auth reply {:?}.", auth_address);
					match auth_address {
						Ok(Some(addresses)) => {
						let auth_id = self.authority_queries.get(0).unwrap().clone();
						for addr in addresses {
							match sc_network::config::parse_addr(addr) {
								Ok((address, _)) => {
									// TODO MixnetCommand useless?
									self.handle_command(MixnetCommand::AuthorityId(auth_id.grandpa_id.clone(), auth_id.authority_discovery_id.clone(), address));
								},
								Err(_) => continue,
							};
						}
						pop_auth_query = true; // TODO same for Ok(None)?
					},
					Ok(None) => {
						pop_auth_query = true; // TODO same for Ok(None)?
					},
					Err(e) => {
						// TODO trace
						err_auth_query = true;
					},
					}
				},
				notif = self.finality_stream.next() => {
					if let Some(notif) = notif {
						delay_finalized.reset(Duration::from_secs(DELAY_NO_FINALISATION_S));
						self.handle_new_finalize_block(notif);
					} else {
						// This point is reached if the other component did shutdown.
						// Shutdown as well.
						debug!(target: "mixnet", "Mixnet, shutdown.");
						return;
					}
				},
				command = self.command_stream.next() => {
					if let Some(command) = command {
						self.handle_command(command);
					} else {
						// This point is reached if the other component did shutdown.
						// Shutdown as well.
						// TODO actually having an instance of sink it will never happen.
						debug!(target: "mixnet", "Mixnet, shutdown.");
						return;
					}
				},
				success = future::poll_fn(|cx| self.worker.poll(cx)).fuse() => {
					if !success {
						debug!(target: "mixnet", "Mixnet, shutdown.");
						return;
					}
				},
				_ = delay_poll_auth.fuse() => {
					self.fetch_auth_peer_id();
					delay_poll_auth.reset(Duration::from_millis(DELAY_CHECK_AUTHORITY_MS)); // TODO tokio interval instead?
				},
				_ = delay_finalized.fuse() => {
					self.state = State::Synching;
					delay_finalized.reset(Duration::from_secs(DELAY_NO_FINALISATION_S));
				},
			}

			if pop_auth_query {
				self.authority_queries.pop_front();
				self.authority_replies.pop_front();
			} else if err_auth_query {
				if let Some(a) = self.authority_queries.pop_front() {
					self.authority_queries.push_back(a);
				}
				if let Some(a) = self.authority_replies.pop_front() {
					self.authority_replies.push_back(None);
				}
			}
			if self.authority_replies.get_mut(0).map(Option::as_mut).flatten().is_none() {
				if let Some(info) = self.authority_queries.get_mut(0) {
					if let Ok(auth_public) = info.authority_discovery_id.1.as_slice().try_into() {
						if let Some(rx) = self
							.authority_discovery_service
							.get_addresses_by_authority_id_callback(auth_public)
						{
							self.authority_replies[0] = Some(rx);
						} else {
							debug!(target: "mixnet", "Query authority full channel.");
						}
					}
				}
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
		let basis = if best_finalized > UNSYNCH_FINALIZED_MARGIN.into() {
			best_finalized - UNSYNCH_FINALIZED_MARGIN.into()
		} else {
			0u32.into()
		};
		if notif.header.number() < &basis {
			debug!(target: "mixnet", "Synching, mixnet suspended {:?}.", (notif.header.number(), &basis));
			self.state = State::Synching;
			return
		} else {
			self.update_state(true);
		}

		// TODO could just look frame sessing new event!!, this is currently inefficient.
		// Also looking at finalized is discutable.

		let new_session = self.shared_authority_set.set_id();
		if self.session.map(|session| new_session != session).unwrap_or(true) {
			let authority_set = self.shared_authority_set.current_authority_list();
			self.handle_new_authority(authority_set, new_session, *notif.header.number());
		}
	}

	fn handle_command(&mut self, command: MixnetCommand) {
		match command {
			MixnetCommand::AuthorityId(authority_id, authority_discovery_id, peer_id) => {
				if &peer_id == self.worker.local_id() {
					self.authority_id = Some(authority_id.clone());
					self.worker.topology_mut().map(|t| {
						if t.current_authorities.contains_key(&authority_id) {
							debug!(target: "mixnet", "Routing active.");
							t.routing = true;
							t.current_authorities.insert(authority_id, Some(peer_id));
						}
					});
				} else if let Some(topology) = self.worker.topology_mut() {
					topology.add_authority_peer_id(authority_id, authority_discovery_id, peer_id);
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
		let local_id = self.worker.local_id().clone();
		let new_session = self.fetch_new_session_keys(at, session);
		self.update_own_public_key_within_authority_set(&set);
		if let Some(topology) = self.worker.topology_mut() {
			// TODO not at topology level, code here
			topology.change_authorities::<B, C>(
				local_id,
				&*self.client,
				set,
				self.authority_id.as_ref(),
				&mut self.authority_discovery_service,
				&mut self.authority_replies,
				&mut self.authority_queries,
				at,
				session,
			);
			self.update_state(false);
		}
	}

	fn fetch_new_session_keys(&mut self, mut at: NumberFor<B>, session: SetId) {
		let mut block_id = sp_runtime::generic::BlockId::number(at); // TODO may need at + 1?
															 // find first block with previous session id
		let runtime_api = self.client.runtime_api();
		if session == 0 {
			at = 0u32.into();
			block_id = sp_runtime::generic::BlockId::number(at);
		} else {
			let mut nb = 0;
			let target = match runtime_api.session_index(&block_id) {
				Ok(at) => at - 1,
				Err(e) => {
					// TODO util meth returning error and handling outside
					error!(target: "mixnet", "Could not fetch session index {:?}, no peer id fetching.", e);
					return
				},
			};
			loop {
				at -= 1u32.into();
				nb += 1;
				block_id = sp_runtime::generic::BlockId::number(at);
				let session_at = match runtime_api.session_index(&block_id) {
					Ok(at) => at,
					Err(e) => {
						error!(target: "mixnet", "Could not fetch session index {:?}, no peer id fetching.", e);
						return
					},
				};
				if session_at == target {
					break
				} else if session_at < target {
					error!(target: "mixnet", "Could not fetch previous session index, no peer id fetching.");
					return
				}
			}

			if nb > 3 {
				warn!(target: "mixnet", "{:?} query to fetch previous session index.", nb);
			}
		}
		// TODO could use queued change to avoid one fetch when updating
		let sessions = match runtime_api.queued_keys(&block_id) {
			Ok(at) => at,
			Err(e) => {
				error!(target: "mixnet", "Could not fetch queued session keys {:?}, no peer id fetching.", e);
				return
			},
		};
		debug!(target: "mixnet", "Fetched session keys {:?}, at {:?}", sessions, block_id);
		if let Some(t) = self.worker.topology_mut() {
			t.sessions = sessions
				.into_iter()
				.flat_map(|(_, keys)| {
					let mut grandpa = None;
					let mut auth_disc = None;
					for pair in keys {
						if pair.0 == sp_application_crypto::key_types::GRANDPA {
							grandpa = Some(pair.1);
						} else if pair.0 == sp_application_crypto::key_types::AUTHORITY_DISCOVERY {
							auth_disc = Some(pair.1);
						}
					}
					if let (Some(g), Some(a)) = (grandpa, auth_disc) {
						Some((g, a))
					} else {
						None
					}
				})
				.collect();
		}
	}

	// authority disco do not return our key: using keystore
	// and use first one.
	// TODO code will not wokr for a validator with two authority
	// session keys.
	fn update_own_public_key_within_authority_set(&mut self, set: &AuthorityList) {
		// TODO can filter to skip it when we are not a validator role
		self.authority_id = None;
		let local_pub_keys =
			&SyncCryptoStore::ed25519_public_keys(&*self.key_store, key_types::GRANDPA)
				.into_iter()
				.collect::<HashSet<_>>();

		for authority in set.iter() {
			let auth_id: AuthorityId = authority.0.clone().into();
			if local_pub_keys.contains(&auth_id.clone().into()) {
				debug!("found self in authority set, will route");
				self.authority_id = Some(auth_id);
				return
			}
		}
	}

	fn fetch_auth_peer_id(&mut self) {
		let mut to_fetch = Vec::new();
		let mut nb_fetched = 0;
		if let Some(t) = self.worker.topology() {
			for (auth, id) in t.current_authorities.iter() {
				if id.is_none() {
					if !self.authority_queries.iter().any(|a| &a.grandpa_id == auth) {
						to_fetch.push(auth.clone());
					}
				}
			}
			for auth in to_fetch.iter() {
				use sp_application_crypto::Public;
				if let Some(authority_discovery_id) =
					t.sessions.get(&auth.to_public_crypto_pair()).cloned()
				{
					if let Ok(auth_public) = authority_discovery_id.1.as_slice().try_into() {
						nb_fetched += 1;
						self.authority_queries.push_back(AuthorityInfo {
							grandpa_id: auth.clone(),
							authority_discovery_id,
						});

						if let Some(rx) = self
							.authority_discovery_service
							.get_addresses_by_authority_id_callback(auth_public)
						{
							self.authority_replies.push_back(Some(rx));
						} else {
							debug!(target: "mixnet", "Query authority full channel.");
							self.authority_replies.push_back(None);
						}
					}
				}
			}
		}
		debug!(target: "mixnet", "refetched queried {:?} authorities out of {:?}", nb_fetched, to_fetch.len());
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
	unconnected_authorities: HashMap<MixPeerId, AuthorityInfo>,
	sessions: HashMap<CryptoTypePublicPair, CryptoTypePublicPair>,

	routing: bool,
	current_authorities: HashMap<AuthorityId, Option<MixPeerId>>,
	routing_nodes: BTreeSet<MixPeerId>,
}

#[derive(Clone)]
pub struct AuthorityInfo {
	pub grandpa_id: AuthorityId,
	pub authority_discovery_id: CryptoTypePublicPair,
}

/// Information related to a peer in the mixnet topology.
#[derive(Clone)]
pub struct NodeInfo {
	id: MixPeerId,
	// associated public pair is the authority discovery one.
	authority_id: Option<AuthorityInfo>,
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
			sessions: HashMap::new(),
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

	fn change_authorities<B, C>(
		&mut self,
		local_id: MixPeerId,
		client: &C,
		new_set: AuthorityList,
		current_authority_id: Option<&AuthorityId>,
		authority_discovery_service: &mut sc_authority_discovery::Service,
		authority_replies: &mut VecDeque<Option<AuthorityRx>>,
		authority_queries: &mut VecDeque<AuthorityInfo>,
		mut at: NumberFor<B>,
		session: SetId,
	) where
		B: BlockT,
		C: UsageProvider<B> + BlockchainEvents<B> + ProvideRuntimeApi<B>,
		C::Api: SessionKeys<B>,
	{
		debug!(target: "mixnet", "Change authorities {:?}", new_set);
		self.current_authorities.clear();
		self.routing_nodes.clear();
		self.unconnected_authorities.clear(); // TODO could keep for a few session
									  // TODO also remove authorty disocvery query??

		while let Some(i) = authority_replies.iter().rev().position(|v| v.is_none()) {
			authority_replies.remove(i);
			authority_queries.remove(i);
		}

		self.routing = false;

		for (auth, _) in new_set.into_iter() {
			if current_authority_id == Some(&auth) {
				debug!(target: "mixnet", "In new authority set, routing.");
				self.routing = true;
				self.current_authorities.insert(auth, Some(local_id));
				continue
			}

			use sp_application_crypto::Public;
			let authority_discovery_id =
				if let Some(id) = self.sessions.get(&auth.clone().to_public_crypto_pair()) {
					id.clone()
				} else {
					warn!(target: "mixnet", "Skipped authority {:?}, no session key", auth);
					continue
				};
			let mut auth_peer_id = None;
			if let Some(node_id) = self.connected_authorities.get(&auth) {
				if let Some(NodeInfo { authority_id, .. }) = self.connected_nodes.get_mut(node_id) {
					*authority_id =
						Some(AuthorityInfo { grandpa_id: auth.clone(), authority_discovery_id });
					self.routing_nodes.insert(node_id.clone());
					auth_peer_id = Some(node_id.clone());
				} else {
					unreachable!();
				}
			} else {
				if let Ok(auth_public) = authority_discovery_id.1.as_slice().try_into() {
					authority_queries.push_back(AuthorityInfo {
						grandpa_id: auth.clone(),
						authority_discovery_id,
					});

					if let Some(rx) = authority_discovery_service
						.get_addresses_by_authority_id_callback(auth_public)
					{
						authority_replies.push_back(Some(rx));
					} else {
						debug!(target: "mixnet", "Query authority full channel.");
						authority_replies.push_back(None);
					}
				} else {
					error!(target: "mixnet", "Invalid authority discovery key {:?}", authority_discovery_id);
					continue
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
			if self.current_authorities.contains_key(&authority_id.grandpa_id) {
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
			if let Some(_peer_id) = self.connected_authorities.remove(&authority_id.grandpa_id) {
				debug_assert!(_peer_id == peer_id);
				self.unconnected_authorities.insert(peer_id, authority_id);
			}
		}
	}

	fn add_authority_peer_id(
		&mut self,
		authority_id: AuthorityId,
		authority_discovery_id: CryptoTypePublicPair,
		peer_id: MixPeerId,
	) {
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
			infos.authority_id =
				Some(AuthorityInfo { grandpa_id: authority_id, authority_discovery_id });
		} else {
			self.unconnected_authorities.insert(
				peer_id,
				AuthorityInfo { grandpa_id: authority_id, authority_discovery_id },
			);
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
impl AuthorityStar {
	fn random_connected(&self, skip: impl Fn(&MixPeerId) -> bool) -> Option<MixPeerId> {
		use rand::RngCore;
		if !self.has_enough_nodes() {
			debug!(target: "mixnet", "Not enough routing nodes for path.");
			return None
		}
		// Warning this assume that PeerId is a random value.
		// This is currently the case (sha256 of encoded ed25519 key).
		let mut ix = [0u8; 32 + PEER_ID_PREFIX.len()];
		rand::thread_rng().fill_bytes(&mut ix[PEER_ID_PREFIX.len()..]); // TODO can less than 32 bytes.
		ix[..PEER_ID_PREFIX.len()].copy_from_slice(&PEER_ID_PREFIX[..]);

		let ix = match MixPeerId::from_bytes(&ix[..]) {
			Ok(ix) => ix,
			Err(err) => {
				error!(target: "mixnet", "Invalid key for mixnet random selection {:?}", err);
				// TODO error here is "InvalidSize(1320524)"
				return None
			},
		};
		debug!(target: "mixnet", "routing {:?}, ix {:?}", self.routing_nodes, ix);
		for key in self.routing_nodes.range(ix..) {
			if !skip(key) {
				debug!(target: "mixnet", "Random route node");
				return Some(key.clone())
			}
			/*			if let Some(info) = self.connected_nodes.get(key) {
				debug!(target: "mixnet", "Random route node");
				return Some(info.id.clone())
			} else {
				unreachable!()
			}*/
		}
		for key in self.routing_nodes.range(..ix).rev() {
			if !skip(key) {
				debug!(target: "mixnet", "Random route node");
				return Some(key.clone())
			}
		}
		None
	}
}

impl Topology for AuthorityStar {
	//type ConnectionInfo = ConnectionInfo;
	// TODO consider authority still only when really authority: but signing is awkward.
	// Probably consumer will not stay connected and rely only on auth discovery dht.
	// Gossip can be ok though: may be of use in gossip system (attach the neighbor too).
	// DHT is kind of gossip though.
	type ConnectionInfo = ();

	fn random_recipient(&self) -> Option<MixPeerId> {
		self.random_connected(|_| false)
	}

	/// For a given peer return a list of peers it is supposed to be connected to.
	/// Return `None` if peer is unknown to the topology.
	/// TODO when `None` allow sending even if not part of topology but in the mixnet:
	/// external hop for latest (see gen_path function). Then last hop will expose
	/// a new connection, so it need to be an additional hop (if possible).
	fn neighbors(&self, from: &MixPeerId) -> Option<Vec<(MixPeerId, MixPublicKey)>> {
		if self.routing_nodes.contains(from) || (&self.node_id == from && self.routing) {
			Some(
				self.routing_nodes
					.iter()
					.filter_map(|id| {
						if id == from {
							None
						} else {
							Some((
								id.clone(),
								self.connected_nodes.get(id).unwrap().public_key.clone(),
							))
						}
					})
					.collect(),
			)
		} else {
			None
		}
	}

	fn random_path(
		&self,
		start: &MixPeerId,
		recipient: &MixPeerId,
		count: usize,
		num_hops: usize,
	) -> Result<Vec<Vec<(MixPeerId, MixPublicKey)>>, Error> {
		// Diverging from default implementation (random from all possible paths) as `neighbor`
		// return same result for all routing peer (minus self).

		let num_hops = if !(self.routing_nodes.contains(start) ||
			(self.routing() && &self.node_id == start))
		{
			// num hops is between routing, last one is not receiving covers.
			num_hops + 1
		} else {
			num_hops
		};
		let num_hops = if !(self.routing_nodes.contains(recipient) ||
			(self.routing() && &self.node_id == recipient))
		{
			// num hops is between routing, last one is not receiving covers.
			num_hops + 1
		} else {
			num_hops
		};

		debug!(target: "mixnet", "nb_hop: {:?}", num_hops);
		let mut result = Vec::with_capacity(count);
		while result.len() < count {
			let mut ids = BTreeSet::new();
			ids.insert(start.clone());
			ids.insert(recipient.clone());
			while ids.len() - 2 < num_hops - 1 {
				if let Some(key) = self.random_connected(|k| ids.contains(k)) {
					debug!(target: "mixnet", "Add hop {:?}.", key);
					ids.insert(key);
				} else {
					debug!(target: "mixnet", "No random connected {:?}.", ids.len() - 2);
					return Err(Error::NotEnoughRoutingPeers)
				}
			}

			let mut path = Vec::with_capacity(num_hops);
			ids.remove(start);
			ids.remove(recipient);
			for peer_id in ids.into_iter() {
				if let Some(info) = self.connected_nodes.get(&peer_id) {
					path.push((peer_id, info.public_key.clone()));
				} else {
					error!(target: "mixnet", "node in routing_nodes must also be in connected_nodes");
					unreachable!("node in routing_nodes must also be in connected_nodes");
				}
			}
			if let Some(info) = self.connected_nodes.get(recipient) {
				path.push((recipient.clone(), info.public_key.clone()));
			} else {
				error!(target: "mixnet", "unknown recipient");
				return Err(Error::NotEnoughRoutingPeers)
			}

			result.push(path);
		}
		debug!(target: "mixnet", "Path: {:?}", result);
		Ok(result)
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
/// TODO could be useful, here we just query again at each session.
struct SessionCache {
	//fn session_index() -> sp_staking::SessionIndex {
	//fn queued_keys() -> Vec<(Vec<u8>, Vec<sp_core::crypto::CryptoTypePublicPair>)> {
	// node_id: AccountId32
}

struct OptionFuture2<F>(Option<F>);
// TODO find something doing it
impl<F: futures::Future + Unpin> futures::Future for OptionFuture2<F> {
	type Output = F::Output;

	fn poll(
		self: Pin<&mut Self>,
		cx: &mut futures::task::Context<'_>,
	) -> futures::task::Poll<Self::Output> {
		match self.get_mut().0.as_mut() {
			Some(x) => x.poll_unpin(cx),
			// Do not try to wakeup cx: in a select and handled by a Delay.
			None => futures::task::Poll::Pending,
		}
	}
}
const PEER_ID_PREFIX: [u8; 6] = [0, 36, 8, 1, 18, 32];
#[test]
fn test_random_route() {
	let mut routing_nodes: BTreeSet<MixPeerId> = Default::default();
	for _ in 0..6 {
		let config = sc_network::config::Secret::New;
		let config = sc_network::config::NodeKeyConfig::Ed25519(config);
		let key_pair = config.into_keypair().unwrap();
		let public = key_pair.public();
		let peer_id = public.to_peer_id();
		assert!(peer_id.to_bytes().len() == 32 + PEER_ID_PREFIX.len());
		assert!(&peer_id.to_bytes()[..PEER_ID_PREFIX.len()] == &PEER_ID_PREFIX[..]);
		routing_nodes.insert(peer_id);
	}
	use rand::RngCore;
	let mut ix = [0u8; 32 + PEER_ID_PREFIX.len()];
	rand::thread_rng().fill_bytes(&mut ix[PEER_ID_PREFIX.len()..]); // TODO can less than 32 bytes.
	ix[..PEER_ID_PREFIX.len()].copy_from_slice(&PEER_ID_PREFIX[..]);
	let ix = MixPeerId::from_bytes(&ix[..]).unwrap();
	routing_nodes.range(ix..).next();
}
