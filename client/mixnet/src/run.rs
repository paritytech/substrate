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

//! Top-level mixnet service function.

use super::{
	api::ApiBackend,
	config::{Config, SubstrateConfig},
	error::RemoteErr,
	extrinsic_queue::ExtrinsicQueue,
	maybe_inf_delay::MaybeInfDelay,
	packet_dispatcher::PacketDispatcher,
	peer_id::to_core_peer_id,
	request::{extrinsic_delay, Request, SUBMIT_EXTRINSIC},
	sync_with_runtime::sync_with_runtime,
};
use codec::{Decode, DecodeAll, Encode};
use futures::{
	future::{pending, Either},
	stream::FuturesUnordered,
	StreamExt,
};
use log::{debug, error, warn};
use mixnet::{
	core::{Events, Message, Mixnet, Packet},
	reply_manager::{ReplyContext, ReplyManager},
	request_manager::RequestManager,
};
use sc_client_api::{BlockchainEvents, HeaderBackend};
use sc_network::{
	Event::{NotificationStreamClosed, NotificationStreamOpened, NotificationsReceived},
	NetworkEventStream, NetworkNotification, NetworkPeers, NetworkStateInfo, ProtocolName,
};
use sc_transaction_pool_api::{
	LocalTransactionPool, OffchainTransactionPoolFactory, TransactionPool,
};
use sp_api::{ApiExt, ProvideRuntimeApi};
use sp_consensus::SyncOracle;
use sp_keystore::{KeystoreExt, KeystorePtr};
use sp_mixnet::{runtime_api::MixnetApi, types::Mixnode};
use sp_runtime::{
	generic::BlockId,
	traits::{Block, Header},
	transaction_validity::TransactionSource,
	Saturating,
};
use std::{
	sync::Arc,
	time::{Duration, Instant},
};

const LOG_TARGET: &str = "mixnet";

const MIN_BLOCKS_BETWEEN_REGISTRATION_ATTEMPTS: u32 = 3;

fn complete_submit_extrinsic(
	reply_manager: &mut ReplyManager,
	reply_context: ReplyContext,
	data: Result<(), RemoteErr>,
	mixnet: &mut Mixnet,
) {
	reply_manager.complete(reply_context, data.encode(), mixnet);
}

fn handle_packet<E: Decode>(
	packet: &Packet,
	mixnet: &mut Mixnet,
	request_manager: &mut RequestManager<Request>,
	reply_manager: &mut ReplyManager,
	extrinsic_queue: &mut ExtrinsicQueue<E>,
	config: &SubstrateConfig,
) {
	match mixnet.handle_packet(packet) {
		Some(Message::Request(message)) => {
			let Some((reply_context, data)) = reply_manager.insert(message, mixnet) else { return };

			match data.as_slice() {
				[SUBMIT_EXTRINSIC, encoded_extrinsic @ ..] => {
					if !extrinsic_queue.has_space() {
						warn!(target: LOG_TARGET, "No space in extrinsic queue; dropping request");
						// We don't send a reply in this case; we want the requester to retry
						reply_manager.abandon(reply_context);
						return
					}

					// Decode the extrinsic
					let mut encoded_extrinsic = encoded_extrinsic;
					let extrinsic = match E::decode_all(&mut encoded_extrinsic) {
						Ok(extrinsic) => extrinsic,
						Err(err) => {
							complete_submit_extrinsic(
								reply_manager,
								reply_context,
								Err(RemoteErr::Decode(format!("Bad extrinsic: {}", err))),
								mixnet,
							);
							return
						},
					};

					let deadline =
						Instant::now() + extrinsic_delay(reply_context.message_id(), config);
					extrinsic_queue.insert(deadline, extrinsic, reply_context);
				},
				_ => {
					error!(target: LOG_TARGET, "Unrecognised request; discarding");
					// To keep things simple we don't bother sending a reply in this case. The
					// requester will give up and try another mixnode eventually.
					reply_manager.abandon(reply_context);
				},
			}
		},
		Some(Message::Reply(message)) => {
			let Some(request) = request_manager.remove(&message.request_id) else {
				debug!(
					target: LOG_TARGET,
					"Received reply to already-completed request with message ID {:x?}",
					message.request_id
				);
				return
			};
			request.send_reply(&message.data);
		},
		None => (),
	}
}

fn time_until(instant: Instant) -> Duration {
	instant.saturating_duration_since(Instant::now())
}

/// Run the mixnet service. If `keystore` is `None`, the service will not attempt to register the
/// local node as a mixnode, even if `config.register` is `true`.
pub async fn run<B, C, S, N, P>(
	config: Config,
	mut api_backend: ApiBackend,
	client: Arc<C>,
	sync: Arc<S>,
	network: Arc<N>,
	protocol_name: ProtocolName,
	transaction_pool: Arc<P>,
	keystore: Option<KeystorePtr>,
) where
	B: Block,
	C: BlockchainEvents<B> + ProvideRuntimeApi<B> + HeaderBackend<B>,
	C::Api: MixnetApi<B>,
	S: SyncOracle,
	N: NetworkStateInfo + NetworkEventStream + NetworkNotification + NetworkPeers,
	P: TransactionPool<Block = B> + LocalTransactionPool<Block = B> + 'static,
{
	let local_peer_id = network.local_peer_id();
	let Some(local_peer_id) = to_core_peer_id(&local_peer_id) else {
		error!(target: LOG_TARGET,
			"Failed to convert libp2p local peer ID {local_peer_id} to mixnet peer ID; \
			mixnet not running");
		return
	};

	let offchain_transaction_pool_factory =
		OffchainTransactionPoolFactory::new(transaction_pool.clone());

	let mut mixnet = Mixnet::new(config.core);
	// It would make sense to reset this to 0 when the session changes, but registrations aren't
	// allowed at the start of a session anyway, so it doesn't really matter
	let mut min_register_block = 0u32.into();
	let mut packet_dispatcher = PacketDispatcher::new(&local_peer_id);
	let mut request_manager = RequestManager::new(config.request_manager);
	let mut reply_manager = ReplyManager::new(config.reply_manager);
	let mut extrinsic_queue = ExtrinsicQueue::new(config.substrate.extrinsic_queue_capacity);

	let mut finality_notifications = client.finality_notification_stream();
	// Import notifications only used for triggering registration attempts
	let mut import_notifications = if config.substrate.register && keystore.is_some() {
		Some(client.import_notification_stream())
	} else {
		None
	};
	let mut network_events = network.event_stream("mixnet").fuse();
	let mut next_forward_packet_delay = MaybeInfDelay::new(None);
	let mut next_authored_packet_delay = MaybeInfDelay::new(None);
	let mut ready_peers = FuturesUnordered::new();
	let mut next_retry_delay = MaybeInfDelay::new(None);
	let mut next_extrinsic_delay = MaybeInfDelay::new(None);
	let mut submit_extrinsic_results = FuturesUnordered::new();

	loop {
		let mut next_request = if request_manager.has_space() {
			Either::Left(api_backend.request_receiver.select_next_some())
		} else {
			Either::Right(pending())
		};

		let mut next_import_notification = import_notifications.as_mut().map_or_else(
			|| Either::Right(pending()),
			|notifications| Either::Left(notifications.select_next_some()),
		);

		futures::select! {
			request = next_request =>
				request_manager.insert(request, &mut mixnet, &packet_dispatcher, &config.substrate),

			notification = finality_notifications.select_next_some() => {
				// To avoid trying to connect to old mixnodes, ignore finality notifications while
				// offline or major syncing. This is a bit racy but should be good enough.
				if !sync.is_offline() && !sync.is_major_syncing() {
					let api = client.runtime_api();
					sync_with_runtime(&mut mixnet, api, notification.hash);
					request_manager.update_session_status(
						&mut mixnet, &packet_dispatcher, &config.substrate);
				}
			}

			notification = next_import_notification => {
				if notification.is_new_best && (*notification.header.number() >= min_register_block) {
					let mut api = client.runtime_api();
					api.register_extension(KeystoreExt(keystore.clone().expect(
						"Import notification stream only setup if we have a keystore")));
					api.register_extension(offchain_transaction_pool_factory
						.offchain_transaction_pool(notification.hash));
					let session_index = mixnet.session_status().current_index;
					let mixnode = Mixnode {
						kx_public: *mixnet.next_kx_public(),
						peer_id: local_peer_id,
						external_addresses: network.external_addresses().into_iter()
							.map(|addr| addr.to_string().into_bytes()).collect(),
					};
					match api.maybe_register(notification.hash, session_index, mixnode) {
						Ok(true) => min_register_block = notification.header.number().saturating_add(
							MIN_BLOCKS_BETWEEN_REGISTRATION_ATTEMPTS.into()),
						Ok(false) => (),
						Err(err) => error!(target: LOG_TARGET,
							"Error trying to register for the next session: {err}"),
					}
				}
			}

			event = network_events.select_next_some() => match event {
				NotificationStreamOpened { remote, protocol, .. }
					if protocol == protocol_name => packet_dispatcher.add_peer(&remote),
				NotificationStreamClosed { remote, protocol }
					if protocol == protocol_name => packet_dispatcher.remove_peer(&remote),
				NotificationsReceived { remote, messages } => {
					for message in messages {
						if message.0 == protocol_name {
							match message.1.as_ref().try_into() {
								Ok(packet) => handle_packet(packet,
									&mut mixnet, &mut request_manager, &mut reply_manager,
									&mut extrinsic_queue, &config.substrate),
								Err(_) => error!(target: LOG_TARGET,
									"Dropped incorrectly sized packet ({} bytes) from {remote}",
									message.1.len(),
								),
							}
						}
					}
				}
				_ => ()
			},

			_ = next_forward_packet_delay => {
				if let Some(packet) = mixnet.pop_next_forward_packet() {
					if let Some(ready_peer) = packet_dispatcher.dispatch(packet) {
						if let Some(fut) = ready_peer.send_packet(&*network, protocol_name.clone()) {
							ready_peers.push(fut);
						}
					}
				} else {
					error!(target: LOG_TARGET,
						"Next forward packet deadline reached, but no packet in queue");
				}
			}

			_ = next_authored_packet_delay => {
				if let Some(packet) = mixnet.pop_next_authored_packet(&packet_dispatcher) {
					if let Some(ready_peer) = packet_dispatcher.dispatch(packet) {
						if let Some(fut) = ready_peer.send_packet(&*network, protocol_name.clone()) {
							ready_peers.push(fut);
						}
					}
				}
			}

			ready_peer = ready_peers.select_next_some() => {
				if let Some(ready_peer) = ready_peer {
					if let Some(fut) = ready_peer.send_packet(&*network, protocol_name.clone()) {
						ready_peers.push(fut);
					}
				}
			}

			_ = next_retry_delay => {
				if !request_manager.pop_next_retry(&mut mixnet, &packet_dispatcher, &config.substrate) {
					error!(target: LOG_TARGET,
						"Next retry deadline reached, but no request in retry queue");
				}
			}

			_ = next_extrinsic_delay => {
				if let Some((extrinsic, reply_context)) = extrinsic_queue.pop() {
					if submit_extrinsic_results.len() < config.substrate.max_pending_extrinsics {
						let fut = transaction_pool.submit_one(
							&BlockId::hash(client.info().best_hash),
							TransactionSource::External,
							extrinsic);
						submit_extrinsic_results.push(async move {
							(fut.await, reply_context)
						});
					} else {
						// There are already too many pending extrinsics, just drop this one. We
						// don't send a reply; we want the requester to retry.
						warn!(target: LOG_TARGET,
							"Too many pending extrinsics; dropped submit extrinsic request");
						reply_manager.abandon(reply_context);
					}
				} else {
					error!(target: LOG_TARGET,
						"Next extrinsic deadline reached, but no extrinsic in queue");
				}
			}

			res_reply_context = submit_extrinsic_results.select_next_some() => {
				let (res, reply_context) = res_reply_context;
				let res = match res {
					Ok(_) => Ok(()),
					Err(err) => Err(RemoteErr::Other(err.to_string())),
				};
				complete_submit_extrinsic(&mut reply_manager, reply_context, res, &mut mixnet);
			}
		}

		let events = mixnet.take_events();
		if !events.is_empty() {
			if events.contains(Events::RESERVED_PEERS_CHANGED) {
				if let Err(err) = network
					.set_reserved_peers(protocol_name.clone(), mixnet.reserved_peer_addresses())
				{
					error!(target: LOG_TARGET, "Setting reserved peers failed: {err}");
				}
			}
			if events.contains(Events::NEXT_FORWARD_PACKET_DEADLINE_CHANGED) {
				next_forward_packet_delay
					.reset(mixnet.next_forward_packet_deadline().map(time_until));
			}
			if events.contains(Events::NEXT_AUTHORED_PACKET_DEADLINE_CHANGED) {
				next_authored_packet_delay.reset(mixnet.next_authored_packet_delay());
			}
			if events.contains(Events::SPACE_IN_AUTHORED_PACKET_QUEUE) {
				// Note this may cause the next retry deadline to change, but should not trigger
				// any mixnet events
				request_manager.process_post_queues(
					&mut mixnet,
					&packet_dispatcher,
					&config.substrate,
				);
			}
		}

		if request_manager.next_retry_deadline_changed() {
			next_retry_delay.reset(request_manager.next_retry_deadline().map(time_until));
		}

		if extrinsic_queue.next_deadline_changed() {
			next_extrinsic_delay.reset(extrinsic_queue.next_deadline().map(time_until));
		}
	}
}
