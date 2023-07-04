// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Statement handling to plug on top of the network service.
//!
//! Usage:
//!
//! - Use [`StatementHandlerPrototype::new`] to create a prototype.
//! - Pass the return value of [`StatementHandlerPrototype::set_config`] to the network
//! configuration as an extra peers set.
//! - Use [`StatementHandlerPrototype::build`] then [`StatementHandler::run`] to obtain a
//! `Future` that processes statements.

use crate::config::*;
use codec::{Decode, Encode};
use futures::{channel::oneshot, prelude::*, stream::FuturesUnordered, FutureExt};
use libp2p::{multiaddr, PeerId};
use prometheus_endpoint::{register, Counter, PrometheusError, Registry, U64};
use sc_network::{
	config::{NonDefaultSetConfig, NonReservedPeerMode, SetConfig},
	error,
	event::Event,
	types::ProtocolName,
	utils::{interval, LruHashSet},
	NetworkEventStream, NetworkNotification, NetworkPeers,
};
use sc_network_common::{
	role::ObservedRole,
	sync::{SyncEvent, SyncEventStream},
};
use sp_statement_store::{
	Hash, NetworkPriority, Statement, StatementSource, StatementStore, SubmitResult,
};
use std::{
	collections::{hash_map::Entry, HashMap, HashSet},
	iter,
	num::NonZeroUsize,
	pin::Pin,
	sync::Arc,
};

pub mod config;

/// A set of statements.
pub type Statements = Vec<Statement>;
/// Future resolving to statement import result.
pub type StatementImportFuture = oneshot::Receiver<SubmitResult>;

mod rep {
	use sc_network::ReputationChange as Rep;
	/// Reputation change when a peer sends us any statement.
	///
	/// This forces node to verify it, thus the negative value here. Once statement is verified,
	/// reputation change should be refunded with `ANY_STATEMENT_REFUND`
	pub const ANY_STATEMENT: Rep = Rep::new(-(1 << 4), "Any statement");
	/// Reputation change when a peer sends us any statement that is not invalid.
	pub const ANY_STATEMENT_REFUND: Rep = Rep::new(1 << 4, "Any statement (refund)");
	/// Reputation change when a peer sends us an statement that we didn't know about.
	pub const GOOD_STATEMENT: Rep = Rep::new(1 << 7, "Good statement");
	/// Reputation change when a peer sends us a bad statement.
	pub const BAD_STATEMENT: Rep = Rep::new(-(1 << 12), "Bad statement");
	/// Reputation change when a peer sends us a duplicate statement.
	pub const DUPLICATE_STATEMENT: Rep = Rep::new(-(1 << 7), "Duplicate statement");
	/// Reputation change when a peer sends us particularly useful statement
	pub const EXCELLENT_STATEMENT: Rep = Rep::new(1 << 8, "High priority statement");
}

const LOG_TARGET: &str = "statement-gossip";

struct Metrics {
	propagated_statements: Counter<U64>,
}

impl Metrics {
	fn register(r: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			propagated_statements: register(
				Counter::new(
					"substrate_sync_propagated_statements",
					"Number of statements propagated to at least one peer",
				)?,
				r,
			)?,
		})
	}
}

/// Prototype for a [`StatementHandler`].
pub struct StatementHandlerPrototype {
	protocol_name: ProtocolName,
}

impl StatementHandlerPrototype {
	/// Create a new instance.
	pub fn new<Hash: AsRef<[u8]>>(genesis_hash: Hash, fork_id: Option<&str>) -> Self {
		let genesis_hash = genesis_hash.as_ref();
		let protocol_name = if let Some(fork_id) = fork_id {
			format!("/{}/{}/statement/1", array_bytes::bytes2hex("", genesis_hash), fork_id)
		} else {
			format!("/{}/statement/1", array_bytes::bytes2hex("", genesis_hash))
		};

		Self { protocol_name: protocol_name.into() }
	}

	/// Returns the configuration of the set to put in the network configuration.
	pub fn set_config(&self) -> NonDefaultSetConfig {
		NonDefaultSetConfig {
			notifications_protocol: self.protocol_name.clone(),
			fallback_names: Vec::new(),
			max_notification_size: MAX_STATEMENT_SIZE,
			handshake: None,
			set_config: SetConfig {
				in_peers: 0,
				out_peers: 0,
				reserved_nodes: Vec::new(),
				non_reserved_mode: NonReservedPeerMode::Deny,
			},
		}
	}

	/// Turns the prototype into the actual handler.
	///
	/// Important: the statements handler is initially disabled and doesn't gossip statements.
	/// Gossiping is enabled when major syncing is done.
	pub fn build<
		N: NetworkPeers + NetworkEventStream + NetworkNotification,
		S: SyncEventStream + sp_consensus::SyncOracle,
	>(
		self,
		network: N,
		sync: S,
		statement_store: Arc<dyn StatementStore>,
		metrics_registry: Option<&Registry>,
		executor: impl Fn(Pin<Box<dyn Future<Output = ()> + Send>>) + Send,
	) -> error::Result<StatementHandler<N, S>> {
		let net_event_stream = network.event_stream("statement-handler-net");
		let sync_event_stream = sync.event_stream("statement-handler-sync");
		let (queue_sender, mut queue_receiver) = async_channel::bounded(100_000);

		let store = statement_store.clone();
		executor(
			async move {
				loop {
					let task: Option<(Statement, oneshot::Sender<SubmitResult>)> =
						queue_receiver.next().await;
					match task {
						None => return,
						Some((statement, completion)) => {
							let result = store.submit(statement, StatementSource::Network);
							if completion.send(result).is_err() {
								log::debug!(
									target: LOG_TARGET,
									"Error sending validation completion"
								);
							}
						},
					}
				}
			}
			.boxed(),
		);

		let handler = StatementHandler {
			protocol_name: self.protocol_name,
			propagate_timeout: (Box::pin(interval(PROPAGATE_TIMEOUT))
				as Pin<Box<dyn Stream<Item = ()> + Send>>)
				.fuse(),
			pending_statements: FuturesUnordered::new(),
			pending_statements_peers: HashMap::new(),
			network,
			sync,
			net_event_stream: net_event_stream.fuse(),
			sync_event_stream: sync_event_stream.fuse(),
			peers: HashMap::new(),
			statement_store,
			queue_sender,
			metrics: if let Some(r) = metrics_registry {
				Some(Metrics::register(r)?)
			} else {
				None
			},
		};

		Ok(handler)
	}
}

/// Handler for statements. Call [`StatementHandler::run`] to start the processing.
pub struct StatementHandler<
	N: NetworkPeers + NetworkEventStream + NetworkNotification,
	S: SyncEventStream + sp_consensus::SyncOracle,
> {
	protocol_name: ProtocolName,
	/// Interval at which we call `propagate_statements`.
	propagate_timeout: stream::Fuse<Pin<Box<dyn Stream<Item = ()> + Send>>>,
	/// Pending statements verification tasks.
	pending_statements:
		FuturesUnordered<Pin<Box<dyn Future<Output = (Hash, Option<SubmitResult>)> + Send>>>,
	/// As multiple peers can send us the same statement, we group
	/// these peers using the statement hash while the statement is
	/// imported. This prevents that we import the same statement
	/// multiple times concurrently.
	pending_statements_peers: HashMap<Hash, HashSet<PeerId>>,
	/// Network service to use to send messages and manage peers.
	network: N,
	/// Syncing service.
	sync: S,
	/// Stream of networking events.
	net_event_stream: stream::Fuse<Pin<Box<dyn Stream<Item = Event> + Send>>>,
	/// Receiver for syncing-related events.
	sync_event_stream: stream::Fuse<Pin<Box<dyn Stream<Item = SyncEvent> + Send>>>,
	// All connected peers
	peers: HashMap<PeerId, Peer>,
	statement_store: Arc<dyn StatementStore>,
	queue_sender: async_channel::Sender<(Statement, oneshot::Sender<SubmitResult>)>,
	/// Prometheus metrics.
	metrics: Option<Metrics>,
}

/// Peer information
#[derive(Debug)]
struct Peer {
	/// Holds a set of statements known to this peer.
	known_statements: LruHashSet<Hash>,
	role: ObservedRole,
}

impl<N, S> StatementHandler<N, S>
where
	N: NetworkPeers + NetworkEventStream + NetworkNotification,
	S: SyncEventStream + sp_consensus::SyncOracle,
{
	/// Turns the [`StatementHandler`] into a future that should run forever and not be
	/// interrupted.
	pub async fn run(mut self) {
		loop {
			futures::select! {
				_ = self.propagate_timeout.next() => {
					self.propagate_statements();
				},
				(hash, result) = self.pending_statements.select_next_some() => {
					if let Some(peers) = self.pending_statements_peers.remove(&hash) {
						if let Some(result) = result {
							peers.into_iter().for_each(|p| self.on_handle_statement_import(p, &result));
						}
					} else {
						log::warn!(target: LOG_TARGET, "Inconsistent state, no peers for pending statement!");
					}
				},
				network_event = self.net_event_stream.next() => {
					if let Some(network_event) = network_event {
						self.handle_network_event(network_event).await;
					} else {
						// Networking has seemingly closed. Closing as well.
						return;
					}
				},
				sync_event = self.sync_event_stream.next() => {
					if let Some(sync_event) = sync_event {
						self.handle_sync_event(sync_event);
					} else {
						// Syncing has seemingly closed. Closing as well.
						return;
					}
				}
			}
		}
	}

	fn handle_sync_event(&mut self, event: SyncEvent) {
		match event {
			SyncEvent::PeerConnected(remote) => {
				let addr =
					iter::once(multiaddr::Protocol::P2p(remote)).collect::<multiaddr::Multiaddr>();
				let result = self.network.add_peers_to_reserved_set(
					self.protocol_name.clone(),
					iter::once(addr).collect(),
				);
				if let Err(err) = result {
					log::error!(target: LOG_TARGET, "Add reserved peer failed: {}", err);
				}
			},
			SyncEvent::PeerDisconnected(remote) => {
				self.network.remove_peers_from_reserved_set(
					self.protocol_name.clone(),
					iter::once(remote).collect(),
				);
			},
		}
	}

	async fn handle_network_event(&mut self, event: Event) {
		match event {
			Event::Dht(_) => {},
			Event::NotificationStreamOpened { remote, protocol, role, .. }
				if protocol == self.protocol_name =>
			{
				let _was_in = self.peers.insert(
					remote,
					Peer {
						known_statements: LruHashSet::new(
							NonZeroUsize::new(MAX_KNOWN_STATEMENTS).expect("Constant is nonzero"),
						),
						role,
					},
				);
				debug_assert!(_was_in.is_none());
			},
			Event::NotificationStreamClosed { remote, protocol }
				if protocol == self.protocol_name =>
			{
				let _peer = self.peers.remove(&remote);
				debug_assert!(_peer.is_some());
			},

			Event::NotificationsReceived { remote, messages } => {
				for (protocol, message) in messages {
					if protocol != self.protocol_name {
						continue
					}
					// Accept statements only when node is not major syncing
					if self.sync.is_major_syncing() {
						log::trace!(
							target: LOG_TARGET,
							"{remote}: Ignoring statements while major syncing or offline"
						);
						continue
					}
					if let Ok(statements) = <Statements as Decode>::decode(&mut message.as_ref()) {
						self.on_statements(remote, statements);
					} else {
						log::debug!(
							target: LOG_TARGET,
							"Failed to decode statement list from {remote}"
						);
					}
				}
			},

			// Not our concern.
			Event::NotificationStreamOpened { .. } | Event::NotificationStreamClosed { .. } => {},
		}
	}

	/// Called when peer sends us new statements
	fn on_statements(&mut self, who: PeerId, statements: Statements) {
		log::trace!(target: LOG_TARGET, "Received {} statements from {}", statements.len(), who);
		if let Some(ref mut peer) = self.peers.get_mut(&who) {
			for s in statements {
				if self.pending_statements.len() > MAX_PENDING_STATEMENTS {
					log::debug!(
						target: LOG_TARGET,
						"Ignoring any further statements that exceed `MAX_PENDING_STATEMENTS`({}) limit",
						MAX_PENDING_STATEMENTS,
					);
					break
				}

				let hash = s.hash();
				peer.known_statements.insert(hash);

				self.network.report_peer(who, rep::ANY_STATEMENT);

				match self.pending_statements_peers.entry(hash) {
					Entry::Vacant(entry) => {
						let (completion_sender, completion_receiver) = oneshot::channel();
						match self.queue_sender.try_send((s, completion_sender)) {
							Ok(()) => {
								self.pending_statements.push(
									async move {
										let res = completion_receiver.await;
										(hash, res.ok())
									}
									.boxed(),
								);
								entry.insert(HashSet::from_iter([who]));
							},
							Err(async_channel::TrySendError::Full(_)) => {
								log::debug!(
									target: LOG_TARGET,
									"Dropped statement because validation channel is full",
								);
							},
							Err(async_channel::TrySendError::Closed(_)) => {
								log::trace!(
									target: LOG_TARGET,
									"Dropped statement because validation channel is closed",
								);
							},
						}
					},
					Entry::Occupied(mut entry) => {
						if !entry.get_mut().insert(who) {
							// Already received this from the same peer.
							self.network.report_peer(who, rep::DUPLICATE_STATEMENT);
						}
					},
				}
			}
		}
	}

	fn on_handle_statement_import(&mut self, who: PeerId, import: &SubmitResult) {
		match import {
			SubmitResult::New(NetworkPriority::High) =>
				self.network.report_peer(who, rep::EXCELLENT_STATEMENT),
			SubmitResult::New(NetworkPriority::Low) =>
				self.network.report_peer(who, rep::GOOD_STATEMENT),
			SubmitResult::Known => self.network.report_peer(who, rep::ANY_STATEMENT_REFUND),
			SubmitResult::KnownExpired => {},
			SubmitResult::Ignored => {},
			SubmitResult::Bad(_) => self.network.report_peer(who, rep::BAD_STATEMENT),
			SubmitResult::InternalError(_) => {},
		}
	}

	/// Propagate one statement.
	pub fn propagate_statement(&mut self, hash: &Hash) {
		// Accept statements only when node is not major syncing
		if self.sync.is_major_syncing() {
			return
		}

		log::debug!(target: LOG_TARGET, "Propagating statement [{:?}]", hash);
		if let Ok(Some(statement)) = self.statement_store.statement(hash) {
			self.do_propagate_statements(&[(*hash, statement)]);
		}
	}

	fn do_propagate_statements(&mut self, statements: &[(Hash, Statement)]) {
		let mut propagated_statements = 0;

		for (who, peer) in self.peers.iter_mut() {
			// never send statements to light nodes
			if matches!(peer.role, ObservedRole::Light) {
				continue
			}

			let to_send = statements
				.iter()
				.filter_map(|(hash, stmt)| peer.known_statements.insert(*hash).then(|| stmt))
				.collect::<Vec<_>>();

			propagated_statements += to_send.len();

			if !to_send.is_empty() {
				log::trace!(target: LOG_TARGET, "Sending {} statements to {}", to_send.len(), who);
				self.network
					.write_notification(*who, self.protocol_name.clone(), to_send.encode());
			}
		}

		if let Some(ref metrics) = self.metrics {
			metrics.propagated_statements.inc_by(propagated_statements as _)
		}
	}

	/// Call when we must propagate ready statements to peers.
	fn propagate_statements(&mut self) {
		// Send out statements only when node is not major syncing
		if self.sync.is_major_syncing() {
			return
		}

		log::debug!(target: LOG_TARGET, "Propagating statements");
		if let Ok(statements) = self.statement_store.statements() {
			self.do_propagate_statements(&statements);
		}
	}
}
