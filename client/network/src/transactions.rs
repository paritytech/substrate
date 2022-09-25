// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use crate::{
	config::{self, TransactionImport, TransactionImportFuture, TransactionPool},
	error,
	protocol::message,
	service::NetworkService,
	utils::{interval, LruHashSet},
	ExHashT,
};

use codec::{Decode, Encode};
use futures::{channel::mpsc, prelude::*, stream::FuturesUnordered};
use libp2p::{multiaddr, PeerId};
use log::{debug, trace, warn};
use prometheus_endpoint::{register, Counter, PrometheusError, Registry, U64};
use sc_network_common::{
	config::ProtocolId,
	protocol::{
		event::{Event, ObservedRole},
		ProtocolName,
	},
	service::{NetworkEventStream, NetworkNotification, NetworkPeers},
};
use sp_runtime::traits::Block as BlockT;
use std::{
	collections::{hash_map::Entry, HashMap},
	iter,
	num::NonZeroUsize,
	pin::Pin,
	sync::{
		atomic::{AtomicBool, Ordering},
		Arc,
	},
	task::Poll,
	time,
};

/// Interval at which we propagate transactions;
const PROPAGATE_TIMEOUT: time::Duration = time::Duration::from_millis(2900);

/// Maximum number of known transaction hashes to keep for a peer.
///
/// This should be approx. 2 blocks full of transactions for the network to function properly.
const MAX_KNOWN_TRANSACTIONS: usize = 10240; // ~300kb per peer + overhead.

/// Maximum allowed size for a transactions notification.
const MAX_TRANSACTIONS_SIZE: u64 = 16 * 1024 * 1024;

/// Maximum number of transaction validation request we keep at any moment.
const MAX_PENDING_TRANSACTIONS: usize = 8192;

mod rep {
	use sc_peerset::ReputationChange as Rep;
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

#[pin_project::pin_project]
struct PendingTransaction<H> {
	#[pin]
	validation: TransactionImportFuture,
	tx_hash: H,
}

impl<H: ExHashT> Future for PendingTransaction<H> {
	type Output = (H, TransactionImport);

	fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
		let mut this = self.project();

		if let Poll::Ready(import_result) = Pin::new(&mut this.validation).poll_unpin(cx) {
			return Poll::Ready((this.tx_hash.clone(), import_result))
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
		fork_id: Option<String>,
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
	pub fn set_config(&self) -> config::NonDefaultSetConfig {
		config::NonDefaultSetConfig {
			notifications_protocol: self.protocol_name.clone(),
			fallback_names: self.fallback_protocol_names.clone(),
			max_notification_size: MAX_TRANSACTIONS_SIZE,
			set_config: config::SetConfig {
				in_peers: 0,
				out_peers: 0,
				reserved_nodes: Vec::new(),
				non_reserved_mode: config::NonReservedPeerMode::Deny,
			},
		}
	}

	/// Turns the prototype into the actual handler. Returns a controller that allows controlling
	/// the behaviour of the handler while it's running.
	///
	/// Important: the transactions handler is initially disabled and doesn't gossip transactions.
	/// You must call [`TransactionsHandlerController::set_gossip_enabled`] to enable it.
	pub fn build<B: BlockT + 'static, H: ExHashT>(
		self,
		service: Arc<NetworkService<B, H>>,
		transaction_pool: Arc<dyn TransactionPool<H, B>>,
		metrics_registry: Option<&Registry>,
	) -> error::Result<(TransactionsHandler<B, H>, TransactionsHandlerController<H>)> {
		let event_stream = service.event_stream("transactions-handler");
		let (to_handler, from_controller) = mpsc::unbounded();
		let gossip_enabled = Arc::new(AtomicBool::new(false));

		let handler = TransactionsHandler {
			protocol_name: self.protocol_name,
			propagate_timeout: Box::pin(interval(PROPAGATE_TIMEOUT)),
			pending_transactions: FuturesUnordered::new(),
			pending_transactions_peers: HashMap::new(),
			gossip_enabled: gossip_enabled.clone(),
			service,
			event_stream,
			peers: HashMap::new(),
			transaction_pool,
			from_controller,
			metrics: if let Some(r) = metrics_registry {
				Some(Metrics::register(r)?)
			} else {
				None
			},
		};

		let controller = TransactionsHandlerController { to_handler, gossip_enabled };

		Ok((handler, controller))
	}
}

/// Controls the behaviour of a [`TransactionsHandler`] it is connected to.
pub struct TransactionsHandlerController<H: ExHashT> {
	to_handler: mpsc::UnboundedSender<ToHandler<H>>,
	gossip_enabled: Arc<AtomicBool>,
}

impl<H: ExHashT> TransactionsHandlerController<H> {
	/// Controls whether transactions are being gossiped on the network.
	pub fn set_gossip_enabled(&mut self, enabled: bool) {
		self.gossip_enabled.store(enabled, Ordering::Relaxed);
	}

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
pub struct TransactionsHandler<B: BlockT + 'static, H: ExHashT> {
	protocol_name: ProtocolName,
	/// Interval at which we call `propagate_transactions`.
	propagate_timeout: Pin<Box<dyn Stream<Item = ()> + Send>>,
	/// Pending transactions verification tasks.
	pending_transactions: FuturesUnordered<PendingTransaction<H>>,
	/// As multiple peers can send us the same transaction, we group
	/// these peers using the transaction hash while the transaction is
	/// imported. This prevents that we import the same transaction
	/// multiple times concurrently.
	pending_transactions_peers: HashMap<H, Vec<PeerId>>,
	/// Network service to use to send messages and manage peers.
	service: Arc<NetworkService<B, H>>,
	/// Stream of networking events.
	event_stream: Pin<Box<dyn Stream<Item = Event> + Send>>,
	// All connected peers
	peers: HashMap<PeerId, Peer<H>>,
	transaction_pool: Arc<dyn TransactionPool<H, B>>,
	gossip_enabled: Arc<AtomicBool>,
	from_controller: mpsc::UnboundedReceiver<ToHandler<H>>,
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

impl<B: BlockT + 'static, H: ExHashT> TransactionsHandler<B, H> {
	/// Turns the [`TransactionsHandler`] into a future that should run forever and not be
	/// interrupted.
	pub async fn run(mut self) {
		loop {
			futures::select! {
				_ = self.propagate_timeout.next().fuse() => {
					self.propagate_transactions();
				},
				(tx_hash, result) = self.pending_transactions.select_next_some() => {
					if let Some(peers) = self.pending_transactions_peers.remove(&tx_hash) {
						peers.into_iter().for_each(|p| self.on_handle_transaction_import(p, result));
					} else {
						warn!(target: "sub-libp2p", "Inconsistent state, no peers for pending transaction!");
					}
				},
				network_event = self.event_stream.next().fuse() => {
					if let Some(network_event) = network_event {
						self.handle_network_event(network_event).await;
					} else {
						// Networking has seemingly closed. Closing as well.
						return;
					}
				},
				message = self.from_controller.select_next_some().fuse() => {
					match message {
						ToHandler::PropagateTransaction(hash) => self.propagate_transaction(&hash),
						ToHandler::PropagateTransactions => self.propagate_transactions(),
					}
				},
			}
		}
	}

	async fn handle_network_event(&mut self, event: Event) {
		match event {
			Event::Dht(_) => {},
			Event::SyncConnected { remote } => {
				let addr = iter::once(multiaddr::Protocol::P2p(remote.into()))
					.collect::<multiaddr::Multiaddr>();
				let result = self.service.add_peers_to_reserved_set(
					self.protocol_name.clone(),
					iter::once(addr).collect(),
				);
				if let Err(err) = result {
					log::error!(target: "sync", "Add reserved peer failed: {}", err);
				}
			},
			Event::SyncDisconnected { remote } => {
				self.service.remove_peers_from_reserved_set(
					self.protocol_name.clone(),
					iter::once(remote).collect(),
				);
			},

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

					if let Ok(m) = <message::Transactions<B::Extrinsic> as Decode>::decode(
						&mut message.as_ref(),
					) {
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
	fn on_transactions(&mut self, who: PeerId, transactions: message::Transactions<B::Extrinsic>) {
		// Accept transactions only when enabled
		if !self.gossip_enabled.load(Ordering::Relaxed) {
			trace!(target: "sync", "{} Ignoring transactions while disabled", who);
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

				self.service.report_peer(who, rep::ANY_TRANSACTION);

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
				self.service.report_peer(who, rep::ANY_TRANSACTION_REFUND),
			TransactionImport::NewGood => self.service.report_peer(who, rep::GOOD_TRANSACTION),
			TransactionImport::Bad => self.service.report_peer(who, rep::BAD_TRANSACTION),
			TransactionImport::None => {},
		}
	}

	/// Propagate one transaction.
	pub fn propagate_transaction(&mut self, hash: &H) {
		// Accept transactions only when enabled
		if !self.gossip_enabled.load(Ordering::Relaxed) {
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
				.filter(|&(ref hash, _)| peer.known_transactions.insert(hash.clone()))
				.cloned()
				.unzip();

			propagated_transactions += hashes.len();

			if !to_send.is_empty() {
				for hash in hashes {
					propagated_to.entry(hash).or_default().push(who.to_base58());
				}
				trace!(target: "sync", "Sending {} transactions to {}", to_send.len(), who);
				self.service
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
		// Accept transactions only when enabled
		if !self.gossip_enabled.load(Ordering::Relaxed) {
			return
		}
		debug!(target: "sync", "Propagating transactions");
		let transactions = self.transaction_pool.transactions();
		let propagated_to = self.do_propagate_transactions(&transactions);
		self.transaction_pool.on_broadcasted(propagated_to);
	}
}
