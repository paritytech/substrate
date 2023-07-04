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

//! Transactions handling to plug on top of the network service.
//!
//! Usage:
//!
//! - Use [`TransactionsHandlerPrototype::new`] to create a prototype.
//! - Pass the return value of [`TransactionsHandlerPrototype::set_config`] to the network
//! configuration as an extra peers set.
//! - Use [`TransactionsHandlerPrototype::build`] then [`TransactionsHandler::run`] to obtain a
//! `Future` that processes transactions.

use crate::config::*;

use codec::{Decode, Encode};
use futures::{prelude::*, stream::FuturesUnordered};
use libp2p::{multiaddr, PeerId};
use log::{debug, trace, warn};

use prometheus_endpoint::{register, Counter, PrometheusError, Registry, U64};
use sc_network::{
	config::{NonDefaultSetConfig, NonReservedPeerMode, ProtocolId, SetConfig},
	error,
	event::Event,
	types::ProtocolName,
	utils::{interval, LruHashSet},
	NetworkEventStream, NetworkNotification, NetworkPeers,
};
use sc_network_common::{
	role::ObservedRole,
	sync::{SyncEvent, SyncEventStream},
	ExHashT,
};
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use sp_runtime::traits::Block as BlockT;

use std::{
	collections::{hash_map::Entry, HashMap},
	iter,
	num::NonZeroUsize,
	pin::Pin,
	sync::Arc,
	task::Poll,
};

pub mod config;

/// A set of transactions.
pub type Transactions<E> = Vec<E>;

mod rep {
	use sc_network::ReputationChange as Rep;
	/// Reputation change when a peer sends us any transaction.
	///
	/// This forces node to verify it, thus the negative value here. Once transaction is verified,
	/// reputation change should be refunded with `ANY_TRANSACTION_REFUND`
	pub const ANY_TRANSACTION: Rep = Rep::new(-(1 << 4), "Any transaction");
	/// Reputation change when a peer sends us any transaction that is not invalid.
	pub const ANY_TRANSACTION_REFUND: Rep = Rep::new(1 << 4, "Any transaction (refund)");
	/// Reputation change when a peer sends us an transaction that we didn't know about.
	pub const GOOD_TRANSACTION: Rep = Rep::new(1 << 7, "Good transaction");
	/// Reputation change when a peer sends us a bad transaction.
	pub const BAD_TRANSACTION: Rep = Rep::new(-(1 << 12), "Bad transaction");
}

struct Metrics {
	propagated_transactions: Counter<U64>,
}

impl Metrics {
	fn register(r: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			propagated_transactions: register(
				Counter::new(
					"substrate_sync_propagated_transactions",
					"Number of transactions propagated to at least one peer",
				)?,
				r,
			)?,
		})
	}
}

struct PendingTransaction<H> {
	validation: TransactionImportFuture,
	tx_hash: H,
}

impl<H> Unpin for PendingTransaction<H> {}

impl<H: ExHashT> Future for PendingTransaction<H> {
	type Output = (H, TransactionImport);

	fn poll(mut self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
		if let Poll::Ready(import_result) = self.validation.poll_unpin(cx) {
			return Poll::Ready((self.tx_hash.clone(), import_result))
		}

		Poll::Pending
	}
}

/// Prototype for a [`TransactionsHandler`].
pub struct TransactionsHandlerPrototype {
	protocol_name: ProtocolName,
	fallback_protocol_names: Vec<ProtocolName>,
}

impl TransactionsHandlerPrototype {
	/// Create a new instance.
	pub fn new<Hash: AsRef<[u8]>>(
		protocol_id: ProtocolId,
		genesis_hash: Hash,
		fork_id: Option<&str>,
	) -> Self {
		let genesis_hash = genesis_hash.as_ref();
		let protocol_name = if let Some(fork_id) = fork_id {
			format!("/{}/{}/transactions/1", array_bytes::bytes2hex("", genesis_hash), fork_id)
		} else {
			format!("/{}/transactions/1", array_bytes::bytes2hex("", genesis_hash))
		};
		let legacy_protocol_name = format!("/{}/transactions/1", protocol_id.as_ref());

		Self {
			protocol_name: protocol_name.into(),
			fallback_protocol_names: iter::once(legacy_protocol_name.into()).collect(),
		}
	}

	/// Returns the configuration of the set to put in the network configuration.
	pub fn set_config(&self) -> NonDefaultSetConfig {
		NonDefaultSetConfig {
			notifications_protocol: self.protocol_name.clone(),
			fallback_names: self.fallback_protocol_names.clone(),
			max_notification_size: MAX_TRANSACTIONS_SIZE,
			handshake: None,
			set_config: SetConfig {
				in_peers: 0,
				out_peers: 0,
				reserved_nodes: Vec::new(),
				non_reserved_mode: NonReservedPeerMode::Deny,
			},
		}
	}

	/// Turns the prototype into the actual handler. Returns a controller that allows controlling
	/// the behaviour of the handler while it's running.
	///
	/// Important: the transactions handler is initially disabled and doesn't gossip transactions.
	/// Gossiping is enabled when major syncing is done.
	pub fn build<
		B: BlockT + 'static,
		H: ExHashT,
		N: NetworkPeers + NetworkEventStream + NetworkNotification,
		S: SyncEventStream + sp_consensus::SyncOracle,
	>(
		self,
		network: N,
		sync: S,
		transaction_pool: Arc<dyn TransactionPool<H, B>>,
		metrics_registry: Option<&Registry>,
	) -> error::Result<(TransactionsHandler<B, H, N, S>, TransactionsHandlerController<H>)> {
		let net_event_stream = network.event_stream("transactions-handler-net");
		let sync_event_stream = sync.event_stream("transactions-handler-sync");
		let (to_handler, from_controller) = tracing_unbounded("mpsc_transactions_handler", 100_000);

		let handler = TransactionsHandler {
			protocol_name: self.protocol_name,
			propagate_timeout: (Box::pin(interval(PROPAGATE_TIMEOUT))
				as Pin<Box<dyn Stream<Item = ()> + Send>>)
				.fuse(),
			pending_transactions: FuturesUnordered::new(),
			pending_transactions_peers: HashMap::new(),
			network,
			sync,
			net_event_stream: net_event_stream.fuse(),
			sync_event_stream: sync_event_stream.fuse(),
			peers: HashMap::new(),
			transaction_pool,
			from_controller,
			metrics: if let Some(r) = metrics_registry {
				Some(Metrics::register(r)?)
			} else {
				None
			},
		};

		let controller = TransactionsHandlerController { to_handler };

		Ok((handler, controller))
	}
}

/// Controls the behaviour of a [`TransactionsHandler`] it is connected to.
pub struct TransactionsHandlerController<H: ExHashT> {
	to_handler: TracingUnboundedSender<ToHandler<H>>,
}

impl<H: ExHashT> TransactionsHandlerController<H> {
	/// You may call this when new transactions are imported by the transaction pool.
	///
	/// All transactions will be fetched from the `TransactionPool` that was passed at
	/// initialization as part of the configuration and propagated to peers.
	pub fn propagate_transactions(&self) {
		let _ = self.to_handler.unbounded_send(ToHandler::PropagateTransactions);
	}

	/// You must call when new a transaction is imported by the transaction pool.
	///
	/// This transaction will be fetched from the `TransactionPool` that was passed at
	/// initialization as part of the configuration and propagated to peers.
	pub fn propagate_transaction(&self, hash: H) {
		let _ = self.to_handler.unbounded_send(ToHandler::PropagateTransaction(hash));
	}
}

enum ToHandler<H: ExHashT> {
	PropagateTransactions,
	PropagateTransaction(H),
}

/// Handler for transactions. Call [`TransactionsHandler::run`] to start the processing.
pub struct TransactionsHandler<
	B: BlockT + 'static,
	H: ExHashT,
	N: NetworkPeers + NetworkEventStream + NetworkNotification,
	S: SyncEventStream + sp_consensus::SyncOracle,
> {
	protocol_name: ProtocolName,
	/// Interval at which we call `propagate_transactions`.
	propagate_timeout: stream::Fuse<Pin<Box<dyn Stream<Item = ()> + Send>>>,
	/// Pending transactions verification tasks.
	pending_transactions: FuturesUnordered<PendingTransaction<H>>,
	/// As multiple peers can send us the same transaction, we group
	/// these peers using the transaction hash while the transaction is
	/// imported. This prevents that we import the same transaction
	/// multiple times concurrently.
	pending_transactions_peers: HashMap<H, Vec<PeerId>>,
	/// Network service to use to send messages and manage peers.
	network: N,
	/// Syncing service.
	sync: S,
	/// Stream of networking events.
	net_event_stream: stream::Fuse<Pin<Box<dyn Stream<Item = Event> + Send>>>,
	/// Receiver for syncing-related events.
	sync_event_stream: stream::Fuse<Pin<Box<dyn Stream<Item = SyncEvent> + Send>>>,
	// All connected peers
	peers: HashMap<PeerId, Peer<H>>,
	transaction_pool: Arc<dyn TransactionPool<H, B>>,
	from_controller: TracingUnboundedReceiver<ToHandler<H>>,
	/// Prometheus metrics.
	metrics: Option<Metrics>,
}

/// Peer information
#[derive(Debug)]
struct Peer<H: ExHashT> {
	/// Holds a set of transactions known to this peer.
	known_transactions: LruHashSet<H>,
	role: ObservedRole,
}

impl<B, H, N, S> TransactionsHandler<B, H, N, S>
where
	B: BlockT + 'static,
	H: ExHashT,
	N: NetworkPeers + NetworkEventStream + NetworkNotification,
	S: SyncEventStream + sp_consensus::SyncOracle,
{
	/// Turns the [`TransactionsHandler`] into a future that should run forever and not be
	/// interrupted.
	pub async fn run(mut self) {
		loop {
			futures::select! {
				_ = self.propagate_timeout.next() => {
					self.propagate_transactions();
				},
				(tx_hash, result) = self.pending_transactions.select_next_some() => {
					if let Some(peers) = self.pending_transactions_peers.remove(&tx_hash) {
						peers.into_iter().for_each(|p| self.on_handle_transaction_import(p, result));
					} else {
						warn!(target: "sub-libp2p", "Inconsistent state, no peers for pending transaction!");
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
				message = self.from_controller.select_next_some() => {
					match message {
						ToHandler::PropagateTransaction(hash) => self.propagate_transaction(&hash),
						ToHandler::PropagateTransactions => self.propagate_transactions(),
					}
				},
			}
		}
	}

	fn handle_sync_event(&mut self, event: SyncEvent) {
		match event {
			SyncEvent::PeerConnected(remote) => {
				let addr = iter::once(multiaddr::Protocol::P2p(remote.into()))
					.collect::<multiaddr::Multiaddr>();
				let result = self.network.add_peers_to_reserved_set(
					self.protocol_name.clone(),
					iter::once(addr).collect(),
				);
				if let Err(err) = result {
					log::error!(target: "sync", "Add reserved peer failed: {}", err);
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
						known_transactions: LruHashSet::new(
							NonZeroUsize::new(MAX_KNOWN_TRANSACTIONS).expect("Constant is nonzero"),
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

					if let Ok(m) =
						<Transactions<B::Extrinsic> as Decode>::decode(&mut message.as_ref())
					{
						self.on_transactions(remote, m);
					} else {
						warn!(target: "sub-libp2p", "Failed to decode transactions list");
					}
				}
			},

			// Not our concern.
			Event::NotificationStreamOpened { .. } | Event::NotificationStreamClosed { .. } => {},
		}
	}

	/// Called when peer sends us new transactions
	fn on_transactions(&mut self, who: PeerId, transactions: Transactions<B::Extrinsic>) {
		// Accept transactions only when node is not major syncing
		if self.sync.is_major_syncing() {
			trace!(target: "sync", "{} Ignoring transactions while major syncing", who);
			return
		}

		trace!(target: "sync", "Received {} transactions from {}", transactions.len(), who);
		if let Some(ref mut peer) = self.peers.get_mut(&who) {
			for t in transactions {
				if self.pending_transactions.len() > MAX_PENDING_TRANSACTIONS {
					debug!(
						target: "sync",
						"Ignoring any further transactions that exceed `MAX_PENDING_TRANSACTIONS`({}) limit",
						MAX_PENDING_TRANSACTIONS,
					);
					break
				}

				let hash = self.transaction_pool.hash_of(&t);
				peer.known_transactions.insert(hash.clone());

				self.network.report_peer(who, rep::ANY_TRANSACTION);

				match self.pending_transactions_peers.entry(hash.clone()) {
					Entry::Vacant(entry) => {
						self.pending_transactions.push(PendingTransaction {
							validation: self.transaction_pool.import(t),
							tx_hash: hash,
						});
						entry.insert(vec![who]);
					},
					Entry::Occupied(mut entry) => {
						entry.get_mut().push(who);
					},
				}
			}
		}
	}

	fn on_handle_transaction_import(&mut self, who: PeerId, import: TransactionImport) {
		match import {
			TransactionImport::KnownGood =>
				self.network.report_peer(who, rep::ANY_TRANSACTION_REFUND),
			TransactionImport::NewGood => self.network.report_peer(who, rep::GOOD_TRANSACTION),
			TransactionImport::Bad => self.network.report_peer(who, rep::BAD_TRANSACTION),
			TransactionImport::None => {},
		}
	}

	/// Propagate one transaction.
	pub fn propagate_transaction(&mut self, hash: &H) {
		// Accept transactions only when node is not major syncing
		if self.sync.is_major_syncing() {
			return
		}

		debug!(target: "sync", "Propagating transaction [{:?}]", hash);
		if let Some(transaction) = self.transaction_pool.transaction(hash) {
			let propagated_to = self.do_propagate_transactions(&[(hash.clone(), transaction)]);
			self.transaction_pool.on_broadcasted(propagated_to);
		}
	}

	fn do_propagate_transactions(
		&mut self,
		transactions: &[(H, B::Extrinsic)],
	) -> HashMap<H, Vec<String>> {
		let mut propagated_to = HashMap::<_, Vec<_>>::new();
		let mut propagated_transactions = 0;

		for (who, peer) in self.peers.iter_mut() {
			// never send transactions to the light node
			if matches!(peer.role, ObservedRole::Light) {
				continue
			}

			let (hashes, to_send): (Vec<_>, Vec<_>) = transactions
				.iter()
				.filter(|(hash, _)| peer.known_transactions.insert(hash.clone()))
				.cloned()
				.unzip();

			propagated_transactions += hashes.len();

			if !to_send.is_empty() {
				for hash in hashes {
					propagated_to.entry(hash).or_default().push(who.to_base58());
				}
				trace!(target: "sync", "Sending {} transactions to {}", to_send.len(), who);
				self.network
					.write_notification(*who, self.protocol_name.clone(), to_send.encode());
			}
		}

		if let Some(ref metrics) = self.metrics {
			metrics.propagated_transactions.inc_by(propagated_transactions as _)
		}

		propagated_to
	}

	/// Call when we must propagate ready transactions to peers.
	fn propagate_transactions(&mut self) {
		// Accept transactions only when node is not major syncing
		if self.sync.is_major_syncing() {
			return
		}

		debug!(target: "sync", "Propagating transactions");
		let transactions = self.transaction_pool.transactions();
		let propagated_to = self.do_propagate_transactions(&transactions);
		self.transaction_pool.on_broadcasted(propagated_to);
	}
}
