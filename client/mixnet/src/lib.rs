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

//! Substrate-specific mixnet usage.
//!
//! Topology specific to substrate and utils to link to network.

use mixnet::{Error, MixPeerId, MixPublicKey, Topology};

pub use mixnet::{Config, SinkToWorker, StreamFromWorker};
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
use sc_network::{MixnetCommand, PeerId};
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use sp_api::{ApiExt, ProvideRuntimeApi};
use sp_core::crypto::CryptoTypePublicPair;
pub use sp_finality_grandpa::{AuthorityId, AuthorityList, SetId};
use sp_runtime::traits::{Block as BlockT, Header, NumberFor};
use sp_session::SessionKeys;
use std::{
	collections::{BTreeMap, BTreeSet, HashMap, HashSet},
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
	command_sink: TracingUnboundedSender<MixnetCommand>,
	command_stream: TracingUnboundedReceiver<MixnetCommand>,
	key_store: Arc<dyn SyncCryptoStore>,
	default_limit_config: Option<u32>,
}

// TODO consider restoring a command support in mixnet
type WorkerChannels = (
	mixnet::WorkerChannels,
	TracingUnboundedSender<MixnetCommand>,
	TracingUnboundedReceiver<MixnetCommand>,
);

#[derive(PartialEq, Eq)]
enum State {
	Synching,
	WaitingMorePeers,
	Running,
}

/// Instantiate channels needed to spawn and communicate with the mixnet worker.
pub fn new_channels(
) -> (WorkerChannels, (SinkToWorker, StreamFromWorker, TracingUnboundedSender<MixnetCommand>)) {
	let (to_worker_sink, to_worker_stream) = tracing_unbounded("mpsc_mixnet_in");
	let (from_worker_sink, from_worker_stream) = tracing_unbounded("mpsc_mixnet_out");
	let (command_sink, command_stream) = tracing_unbounded("mpsc_mixnet_commands");
	(
		(
			(Box::new(from_worker_sink), Box::new(to_worker_stream)),
			command_sink.clone(),
			command_stream,
		),
		(Box::new(to_worker_sink), Box::new(from_worker_stream), command_sink),
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
		network_identity: &libp2p::core::identity::Keypair,
		client: Arc<C>,
		shared_authority_set: sc_finality_grandpa::SharedAuthoritySet<
			<B as BlockT>::Hash,
			NumberFor<B>,
		>,
		//		role: sc_network::config::Role,
		//authority_id: Option<AuthorityId>,
		key_store: Arc<dyn SyncCryptoStore>,
		//authority-discovery which is slow).
		//key_store: &dyn SyncCryptoStore,
	) -> Option<Self> {
		let mut local_public_key = None;
		// get the peer id
		for key in SyncCryptoStore::sr25519_public_keys(&*key_store, key_types::IM_ONLINE)
			.into_iter()
			.rev()
		{
			log::error!(target: "mixnet", "A imonline key");
			if SyncCryptoStore::has_keys(&*key_store, &[(key.0.into(), key_types::IM_ONLINE)]) {
				local_public_key = Some(key);
				break
			} else {
				log::error!(target: "mixnet", "No private key for imonline key");
			}
		}

		let local_public_key: [u8; 32] = if let Some(key) = local_public_key {
			key.0
		} else {
			// TODO switch to trace
			log::error!(target: "mixnet", "Generating new ImOnline key.");
			SyncCryptoStore::sr25519_generate_new(&*key_store, key_types::IM_ONLINE, None)
				.ok()?
				.0
		};

		let mixnet_config = if let Some((pub_key, priv_key)) = Self::get_mixnet_keys(&*key_store) {
			mixnet::Config::new_with_keys(local_public_key, pub_key, priv_key)
		} else {
			log::error!(target: "mixnet", "Not using grandpa key");
			mixnet::Config::new(local_public_key)
		};

		let finality_stream = client.finality_notification_stream();

		// TODO read validator from session
		// TODO is this node part of session (role means nothing).
		let topology = AuthorityStar::new(
			mixnet_config.local_id.clone(),
			network_identity.public().into(),
			mixnet_config.public_key.clone(),
			key_store.clone(),
		);
		let default_limit_config = mixnet_config.limit_per_window.clone();

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
		Some(MixnetWorker {
			authority_id: None,
			worker,
			finality_stream,
			shared_authority_set,
			session: None,
			client,
			state,
			command_sink: inner_channels.1,
			command_stream: inner_channels.2,
			key_store,
			default_limit_config,
			//connection_info,
		})
		//encoded_connection_info,
	}

	fn get_mixnet_keys(
		key_store: &dyn SyncCryptoStore,
	) -> Option<(MixPublicKey, mixnet::MixSecretKey)> {
		let mut grandpa_key = None;
		for key in SyncCryptoStore::ed25519_public_keys(&*key_store, key_types::GRANDPA)
			.into_iter()
			.rev()
		{
			log::error!(target: "mixnet", "A grandpa key");
			if SyncCryptoStore::has_keys(&*key_store, &[(key.0.into(), key_types::GRANDPA)]) {
				grandpa_key = Some(key);
				break
			} else {
				log::error!(target: "mixnet", "No private key for grandpa key");
			}
		}

		if let Some(grandpa_key) = grandpa_key {
			let mut p = [0u8; 32];
			p.copy_from_slice(grandpa_key.as_ref());
			let pub_key = mixnet::public_from_ed25519(p);

			log::error!(target: "mixnet", "Gr pub"); // TODO rem
			let priv_key = SyncCryptoStore::mixnet_secret_from_ed25519(
				&*key_store,
				key_types::GRANDPA,
				&grandpa_key,
			)
			.ok()?;
			log::error!(target: "mixnet", "Gr pri"); // TODO rem
			Some((pub_key, priv_key))
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
		let mut delay_finalized = Delay::new(Duration::from_secs(DELAY_NO_FINALISATION_S));
		let delay_finalized = &mut delay_finalized;
		let mut nb_poll = 0u128;
		// TODO change in crate to use directly as a future..
		loop {
			//future::poll_fn(|cx| auth_poll.map(|a|
			// Pin::new(a).poll(cx)).unwrap_or(futures::task::Poll::Pending)); TODO consider
			// stream_select
			futures::select! {
				// TODO poll more than first??
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
					nb_poll += 1;
					if nb_poll % 10 == 0 {
						debug!(target: "mixnet", "Polling ok");
					}
					if !success {
						debug!(target: "mixnet", "Mixnet, shutdown.");
						return;
					}
				},
				_ = delay_finalized.fuse() => {
					self.state = State::Synching;
					delay_finalized.reset(Duration::from_secs(DELAY_NO_FINALISATION_S));
				},
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
			MixnetCommand::TransactionImportResult(surb, result) => {
				debug!(target: "mixnet", "Mixnet, received transaction import result.");
				if let Err(e) = self.worker.mixnet_mut().register_surb(result.encode(), surb) {
					error!(target: "mixnet", "Could not register surb {:?}", e);
				}
			},
		}
	}

	fn handle_new_authority(&mut self, set: AuthorityList, session: SetId, at: NumberFor<B>) {
		self.session = Some(session);
		self.fetch_new_session_keys(at, session);
		self.update_own_public_key_within_authority_set(&set);
		let mut remove_limit = Vec::new();
		let current_local_id = self.worker.local_id().clone();
		let current_public_key = self.worker.public_key().clone();
		let topology = &mut self.worker.mixnet_mut().topology;
		debug!(target: "mixnet", "Change authorities {:?}", set);
		let mut old_authority2 = std::mem::take(&mut topology.authorities);

		topology.routing = false;

		let mut restart = None;
		for (auth, _) in set.into_iter() {
			use sp_application_crypto::Public;
			let auth_pub_pair = auth.clone().to_public_crypto_pair(); // TODO change key type in map?
			if let Some(key) = topology.sessions2.get(&auth_pub_pair) {
				let mut peer_id = [0u8; 32];
				peer_id.copy_from_slice(&key.1[..]);
				if old_authority2.remove(&peer_id).is_some() {
					remove_limit.push(peer_id.clone());
				}
				// derive from grandpa one
				let mut p = [0u8; 32];
				p.copy_from_slice(auth.as_ref());
				let public_key = mixnet::public_from_ed25519(p);

				if self.authority_id.as_ref() == Some(&auth) {
					debug!(target: "mixnet", "In new authority set, routing.");
					topology.routing = true;
					let new_id = (current_local_id != peer_id).then(|| {
						topology.node_id = peer_id.clone();
						peer_id.clone()
					});
					let new_key = (current_public_key != public_key).then(|| {
						let secret_key = SyncCryptoStore::mixnet_secret_from_ed25519(
							&*self.key_store,
							key_types::GRANDPA,
							&auth.into(),
						)
						.ok()?;
						topology.node_public_key = public_key.clone();

						Some((public_key.clone(), secret_key))
					}).flatten();
					if new_id.is_some() || new_key.is_some() {
						restart = Some((new_id, new_key));
					}
				} else {
					error!(target: "mixnet", "Insert auth {:?}", peer_id);
					topology.authorities.insert(peer_id, public_key);
				}
			} else {
				error!(target: "mixnet", "Missing imonline key for authority {:?}, not adding it to topology.", auth);
			}
		}
		if let Some((id, key)) = restart {
			self.worker.restart(id, key);
		}
		self.update_state(false);
		for peer in remove_limit.into_iter() {
			debug!(target: "mixnet", "Remove limit for {:?}.", peer);
			self.worker.change_peer_limit_window(&peer, None);
		}
		for (peer, _) in old_authority2.into_iter() {
			debug!(target: "mixnet", "Restore limit for {:?}.", peer);
			self.worker.change_peer_limit_window(&peer, self.default_limit_config.clone());
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
		self.worker.mixnet_mut().topology.sessions2 = sessions
			.into_iter()
			.flat_map(|(_, keys)| {
				let mut grandpa = None;
				let mut imonline = None;
				for pair in keys {
					if pair.0 == sp_application_crypto::key_types::GRANDPA {
						grandpa = Some(pair.1);
					} else if pair.0 == sp_application_crypto::key_types::IM_ONLINE {
						imonline = Some(pair.1);
					}
				}
				if let (Some(g), Some(a)) = (grandpa, imonline) {
					Some((g, a))
				} else {
					None
				}
			})
			.collect();
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

	fn update_state(&mut self, synched: bool) {
		match &self.state {
			State::Running =>
				if !self.worker.mixnet().topology.has_enough_nodes() {
					self.state = State::WaitingMorePeers;
				},
			State::WaitingMorePeers =>
				if self.worker.mixnet().topology.has_enough_nodes() {
					debug!(target: "mixnet", "Running.");
					self.state = State::Running;
				},
			State::Synching if synched =>
				if self.worker.mixnet().topology.has_enough_nodes() {
					debug!(target: "mixnet", "Running.");
					self.state = State::Running;
				} else {
					self.state = State::WaitingMorePeers;
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
	network_id: PeerId,
	node_public_key: MixPublicKey,
	key_store: Arc<dyn SyncCryptoStore>,
	// true when we are in authorities set.
	routing: bool,
	// All authorities are considered connected (when building message except first hop).
	authorities: BTreeMap<MixPeerId, MixPublicKey>,
	// The connected nodes (for first hop use `authorities` joined `connected_nodes`).
	connected_nodes: HashMap<MixPeerId, MixPublicKey>,
	// Grandpa -> IMonline TODO rename session after removing session3 and authdisc
	// TODO this is what is a bit redundant with authorities
	sessions2: HashMap<CryptoTypePublicPair, CryptoTypePublicPair>,
}

#[derive(Clone)]
pub struct AuthorityInfo {
	pub grandpa_id: AuthorityId,
	pub authority_discovery_id: CryptoTypePublicPair,
}

impl AuthorityStar {
	/// Instantiate a new topology.
	pub fn new(
		node_id: MixPeerId,
		network_id: PeerId,
		node_public_key: MixPublicKey,
		key_store: Arc<dyn SyncCryptoStore>,
	) -> Self {
		AuthorityStar {
			node_id,
			network_id,
			node_public_key,
			authorities: BTreeMap::new(),
			connected_nodes: HashMap::new(),
			sessions2: HashMap::new(),
			routing: false,
			key_store,
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

	fn has_enough_nodes(&self) -> bool {
		self.authorities.len() >= LOW_MIXNET_THRESHOLD
	}

	fn add_connected_peer(&mut self, peer_id: MixPeerId, key: MixPublicKey) {
		debug!(target: "mixnet", "Connected to mixnet {:?} {:?}", peer_id, key);
		if let Some(public_key) = self.connected_nodes.get_mut(&peer_id) {
			*public_key = key;
			return
		}

		self.connected_nodes.insert(peer_id, key);
	}

	fn add_disconnected_peer(&mut self, peer_id: &MixPeerId) {
		debug!(target: "mixnet", "Disconnected from mixnet {:?}", peer_id);
		let _ = self.connected_nodes.remove(peer_id);
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
	fn random_connected(
		&self,
		skip: impl Fn(&MixPeerId) -> bool,
	) -> Option<(MixPeerId, MixPublicKey)> {
		use rand::RngCore;
		if !self.has_enough_nodes() {
			debug!(target: "mixnet", "Not enough routing nodes for path.");
			return None
		}
		// Warning this assume that PeerId is a random value.
		// TODO switched to session public key which should be?? TODO check it is public byte of sr
		let mut ix = [0u8; 32 + PEER_ID_PREFIX.len()];
		rand::thread_rng().fill_bytes(&mut ix[PEER_ID_PREFIX.len()..]); // TODO can less than 32 bytes.
		ix[..PEER_ID_PREFIX.len()].copy_from_slice(&PEER_ID_PREFIX[..]);

		/*		let ix = match MixPeerId::from_bytes(&ix[..]) {
			Ok(ix) => ix,
			Err(err) => {
				error!(target: "mixnet", "Invalid key for mixnet random selection {:?}", err);
				// TODO error here is "InvalidSize(1320524)"
				return None
			},
		};*/
		debug!(target: "mixnet", "routing {:?}, ix {:?}", self.authorities, ix);
		for key in self.authorities.range(ix..) {
			if !skip(&key.0) {
				debug!(target: "mixnet", "Random route node");
				return Some((key.0.clone(), key.1.clone()))
			}
			/*			if let Some(info) = self.connected_nodes.get(key) {
				debug!(target: "mixnet", "Random route node");
				return Some(info.id.clone())
			} else {
				unreachable!()
			}*/
		}
		for key in self.authorities.range(..ix).rev() {
			if !skip(&key.0) {
				debug!(target: "mixnet", "Random route node");
				return Some((key.0.clone(), key.1.clone()))
			}
		}
		None
	}
}

impl Topology for AuthorityStar {
	fn first_hop_nodes(&self) -> Vec<(MixPeerId, MixPublicKey)> {
		self.authorities.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
	}
	fn first_hop_nodes_external(&self, _from: &MixPeerId) -> Vec<(MixPeerId, MixPublicKey)> {
		// allow for all
		self.first_hop_nodes()
			.into_iter()
			.filter(|(id, _key)| self.connected_nodes.contains_key(id))
			.collect()
	}
	fn is_first_node(&self, id: &MixPeerId) -> bool {
		// allow for all
		self.is_routing(id)
	}
	//type ConnectionInfo = ConnectionInfo;
	// TODO consider authority still only when really authority: but signing is awkward.
	// Probably consumer will not stay connected and rely only on auth discovery dht.
	// Gossip can be ok though: may be of use in gossip system (attach the neighbor too).
	// DHT is kind of gossip though.

	fn random_recipient(&self, _from: &MixPeerId) -> Option<(MixPeerId, MixPublicKey)> {
		self.random_connected(|_| false)
	}

	/// For a given peer return a list of peers it is supposed to be connected to.
	/// Return `None` if peer is unknown to the topology.
	/// TODO when `None` allow sending even if not part of topology but in the mixnet:
	/// external hop for latest (see gen_path function). Then last hop will expose
	/// a new connection, so it need to be an additional hop (if possible).
	fn neighbors(&self, from: &MixPeerId) -> Option<Vec<(MixPeerId, MixPublicKey)>> {
		if self.authorities.contains_key(from) || (&self.node_id == from && self.routing) {
			Some(
				self.authorities
					.iter()
					.filter_map(|id| {
						if id.0 == from {
							None
						} else {
							Some((
								id.0.clone(),
								id.1.clone(),
								//								self.connected_nodes.get(&id.0).unwrap().public_key.clone(),
							))
						}
					})
					.collect(),
			)
		} else {
			None
		}
	}

	fn routing_to(&self, from: &MixPeerId, to: &MixPeerId) -> bool {
		(self.authorities.contains_key(from) || (&self.node_id == from && self.routing)) &&
			(self.authorities.contains_key(to) || (&self.node_id == to && self.routing))
	}

	fn random_path(
		&self,
		start_node: (&MixPeerId, Option<&MixPublicKey>),
		recipient_node: (&MixPeerId, Option<&MixPublicKey>),
		count: usize,
		num_hops: usize,
		max_hops: usize,
		last_query_if_surb: Option<&Vec<(MixPeerId, MixPublicKey)>>,
	) -> Result<Vec<Vec<(MixPeerId, MixPublicKey)>>, Error> {
		// Diverging from default implementation (random from all possible paths) as `neighbor`
		// return same result for all routing peer (minus self).

		let mut add_start = None;
		let mut add_end = None;
		let start = if self.is_first_node(start_node.0) {
			start_node.0.clone()
		} else {
			if num_hops + 1 > max_hops {
				return Err(Error::TooManyHops)
			}

			let firsts = self.first_hop_nodes_external(start_node.0);
			if firsts.len() == 0 {
				return Err(Error::NoPath(Some(recipient_node.0.clone())))
			}
			let mut rng = rand::thread_rng();
			use rand::Rng;
			let n: usize = rng.gen_range(0, firsts.len());
			add_start = Some(firsts[n].clone());
			firsts[n].0.clone()
		};

		let recipient = if self.is_routing(recipient_node.0) {
			recipient_node.0.clone()
		} else {
			if num_hops + 1 > max_hops {
				return Err(Error::TooManyHops)
			}

			if let Some(query) = last_query_if_surb {
				// reuse a node that was recently connected.
				if let Some(rec) = query.get(0) {
					add_end = Some(recipient_node);
					rec.0.clone()
				} else {
					return Err(Error::NoPath(Some(recipient_node.0.clone())))
				}
			} else {
				return Err(Error::NoPath(Some(recipient_node.0.clone())))
			}
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
					ids.insert(key.0);
				} else {
					debug!(target: "mixnet", "No random connected {:?}.", ids.len() - 2);
					return Err(Error::NotEnoughRoutingPeers)
				}
			}

			let mut path = Vec::with_capacity(num_hops + 1);
			if let Some((peer, key)) = add_start {
				path.push((peer.clone(), key.clone()));
			}

			ids.remove(&start);
			ids.remove(&recipient);
			for peer_id in ids.into_iter() {
				if let Some(public_key) = self.authorities.get(&peer_id) {
					path.push((peer_id, public_key.clone()));
				} else {
					error!(target: "mixnet", "node in routing_nodes must also be in connected_nodes");
					unreachable!("node in routing_nodes must also be in connected_nodes");
				}
			}
			if let Some(public_key) = self.connected_nodes.get(&recipient) {
				path.push((recipient.clone(), public_key.clone()));
			} else {
				if self.node_id == recipient {
					// surb reply
					path.push((self.node_id.clone(), self.node_public_key.clone()));
				} else {
					error!(target: "mixnet", "Unknown recipient");
					return Err(Error::NotEnoughRoutingPeers)
				}
			}

			if let Some((peer, key)) = add_end {
				if let Some(key) = key {
					path.push((peer.clone(), key.clone()));
				} else {
					return Err(Error::NoPath(Some(recipient_node.0.clone())))
				}
			}
			result.push(path);
		}
		debug!(target: "mixnet", "Path: {:?}", result);
		Ok(result)
	}

	fn is_routing(&self, id: &MixPeerId) -> bool {
		if id == &self.node_id {
			self.routing
		} else {
			self.authorities.contains_key(id)
		}
	}

	fn connected(&mut self, peer_id: MixPeerId, key: MixPublicKey) {
		debug!(target: "mixnet", "Connected from internal");
		self.add_connected_peer(peer_id, key)
	}

	fn disconnect(&mut self, peer_id: &MixPeerId) {
		debug!(target: "mixnet", "Disconnected from internal");
		self.add_disconnected_peer(&peer_id);
	}

	fn allowed_external(&self, _id: &MixPeerId) -> Option<(usize, usize)> {
		// 10% TODO limit nb connection
		Some((1, 10))
	}

	fn allow_external(&mut self, _id: &MixPeerId) -> Option<(usize, usize)> {
		// 10% TODO limit nb connection (in handshake)
		Some((1, 10))
	}

	fn handshake_size(&self) -> usize {
		32 + 32 + 64
	}
	fn check_handshake(
		&mut self,
		payload: &[u8],
		_from: &PeerId,
	) -> Option<(MixPeerId, MixPublicKey)> {
		let mut peer_id = [0u8; 32];
		peer_id.copy_from_slice(&payload[0..32]);
		//		let peer_id = mixnet::to_sphinx_id(&payload[0..32]).ok()?;
		let mut pk = [0u8; 32];
		pk.copy_from_slice(&payload[32..64]);
		let mut signature = [0u8; 64];
		signature.copy_from_slice(&payload[64..]);
		let signature = sp_application_crypto::sr25519::Signature(signature);
		let mut message = self.network_id.to_bytes().to_vec();
		message.extend_from_slice(&pk[..]);
		let key = sp_application_crypto::sr25519::Public(peer_id.clone());
		error!(target: "mixnet", "check handshake: {:?}, {:?}, {:?} from {:?}", peer_id, message, signature, _from);
		use sp_application_crypto::RuntimePublic;
		if key.verify(&message, &signature) {
			let pk = MixPublicKey::from(pk);
			Some((peer_id, pk))
		} else {
			None
		}
	}

	fn handshake(&mut self, with: &PeerId, public_key: &MixPublicKey) -> Option<Vec<u8>> {
		let mut result = self.node_id.to_vec();
		// TODO need to sign public key with local id
		result.extend_from_slice(&public_key.as_bytes()[..]);
		// TODO force the session one if existing TODO store the public key !!!! in topo
		let mut message = with.to_bytes().to_vec();
		message.extend_from_slice(&public_key.as_bytes()[..]);
		match SyncCryptoStore::sign_with(
			&*self.key_store,
			key_types::IM_ONLINE,
			&CryptoTypePublicPair(sp_core::sr25519::CRYPTO_ID, self.node_id.to_vec()),
			&message[..],
		) {
			Ok(Some(signature)) => {
				result.extend_from_slice(&signature[..]);
				error!(target: "mixnet", "create handshake: {:?}, {:?}, {:?} with {:?}", self.node_id, message, signature, with);
				log::error!(target: "mixnet", "hanshake size: {:?}", result.len());
				return Some(result)
			},
			Err(e) => {
				log::error!(target: "mixnet", "hanshake signing error: {:?}", e);
			},
			_ => (),
		}
		log::error!(target: "mixnet", "No imonline key error"); // TODO rem
		None
	}
}

//const PEER_ID_PREFIX: [u8; 6] = [0, 36, 8, 1, 18, 32];
const PEER_ID_PREFIX: [u8; 0] = [];
/*#[test]
fn test_random_route() {
	let mut routing_nodes: BTreeMap<MixPeerId> = Default::default();
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
}*/
