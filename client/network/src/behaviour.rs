// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

use crate::{
	config::{ProtocolId, Role}, block_requests, light_client_handler,
	peer_info, request_responses, discovery::{DiscoveryBehaviour, DiscoveryConfig, DiscoveryOut},
	protocol::{message::Roles, CustomMessageOutcome, NotificationsSink, Protocol},
	ObservedRole, DhtEvent, ExHashT,
};

use bytes::Bytes;
use codec::Encode as _;
use libp2p::NetworkBehaviour;
use libp2p::core::{Multiaddr, PeerId, PublicKey};
use libp2p::identify::IdentifyInfo;
use libp2p::kad::record;
use libp2p::swarm::{NetworkBehaviourAction, NetworkBehaviourEventProcess, PollParameters};
use log::debug;
use sp_consensus::{BlockOrigin, import_queue::{IncomingBlock, Origin}};
use sp_runtime::{traits::{Block as BlockT, NumberFor}, Justification};
use std::{
	borrow::Cow,
	collections::{HashSet, VecDeque},
	iter,
	task::{Context, Poll},
	time::Duration,
};

pub use crate::request_responses::{
	ResponseFailure, InboundFailure, RequestFailure, OutboundFailure, RequestId, SendRequestError
};

/// General behaviour of the network. Combines all protocols together.
#[derive(NetworkBehaviour)]
#[behaviour(out_event = "BehaviourOut<B>", poll_method = "poll")]
pub struct Behaviour<B: BlockT, H: ExHashT> {
	/// All the substrate-specific protocols.
	substrate: Protocol<B, H>,
	/// Periodically pings and identifies the nodes we are connected to, and store information in a
	/// cache.
	peer_info: peer_info::PeerInfoBehaviour,
	/// Discovers nodes of the network.
	discovery: DiscoveryBehaviour,
	/// Generic request-reponse protocols.
	request_responses: request_responses::RequestResponsesBehaviour,
	/// Block request handling.
	block_requests: block_requests::BlockRequests<B>,
	/// Light client request handling.
	light_client_handler: light_client_handler::LightClientHandler<B>,

	/// Queue of events to produce for the outside.
	#[behaviour(ignore)]
	events: VecDeque<BehaviourOut<B>>,

	/// Role of our local node, as originally passed from the configuration.
	#[behaviour(ignore)]
	role: Role,
}

/// Event generated by `Behaviour`.
pub enum BehaviourOut<B: BlockT> {
	BlockImport(BlockOrigin, Vec<IncomingBlock<B>>),
	JustificationImport(Origin, B::Hash, NumberFor<B>, Justification),

	/// Started a random iterative Kademlia discovery query.
	RandomKademliaStarted(ProtocolId),

	/// We have received a request from a peer and answered it.
	///
	/// This event is generated for statistics purposes.
	InboundRequest {
		/// Peer which sent us a request.
		peer: PeerId,
		/// Protocol name of the request.
		protocol: Cow<'static, str>,
		/// If `Ok`, contains the time elapsed between when we received the request and when we
		/// sent back the response. If `Err`, the error that happened.
		result: Result<Duration, ResponseFailure>,
	},

	/// A request initiated using [`Behaviour::send_request`] has succeeded or failed.
	RequestFinished {
		/// Request that has succeeded.
		request_id: RequestId,
		/// Response sent by the remote or reason for failure.
		result: Result<Vec<u8>, RequestFailure>,
	},

	/// Started a new request with the given node.
	///
	/// This event is for statistics purposes only. The request and response handling are entirely
	/// internal to the behaviour.
	OpaqueRequestStarted {
		peer: PeerId,
		/// Protocol name of the request.
		protocol: String,
	},
	/// Finished, successfully or not, a previously-started request.
	///
	/// This event is for statistics purposes only. The request and response handling are entirely
	/// internal to the behaviour.
	OpaqueRequestFinished {
		/// Who we were requesting.
		peer: PeerId,
		/// Protocol name of the request.
		protocol: String,
		/// How long before the response came or the request got cancelled.
		request_duration: Duration,
	},

	/// Opened a substream with the given node with the given notifications protocol.
	///
	/// The protocol is always one of the notification protocols that have been registered.
	NotificationStreamOpened {
		/// Node we opened the substream with.
		remote: PeerId,
		/// The concerned protocol. Each protocol uses a different substream.
		protocol: Cow<'static, str>,
		/// Object that permits sending notifications to the peer.
		notifications_sink: NotificationsSink,
		/// Role of the remote.
		role: ObservedRole,
	},

	/// The [`NotificationsSink`] object used to send notifications with the given peer must be
	/// replaced with a new one.
	///
	/// This event is typically emitted when a transport-level connection is closed and we fall
	/// back to a secondary connection.
	NotificationStreamReplaced {
		/// Id of the peer we are connected to.
		remote: PeerId,
		/// The concerned protocol. Each protocol uses a different substream.
		protocol: Cow<'static, str>,
		/// Replacement for the previous [`NotificationsSink`].
		notifications_sink: NotificationsSink,
	},

	/// Closed a substream with the given node. Always matches a corresponding previous
	/// `NotificationStreamOpened` message.
	NotificationStreamClosed {
		/// Node we closed the substream with.
		remote: PeerId,
		/// The concerned protocol. Each protocol uses a different substream.
		protocol: Cow<'static, str>,
	},

	/// Received one or more messages from the given node using the given protocol.
	NotificationsReceived {
		/// Node we received the message from.
		remote: PeerId,
		/// Concerned protocol and associated message.
		messages: Vec<(Cow<'static, str>, Bytes)>,
	},

	/// Now connected to a new peer for syncing purposes.
	SyncConnected(PeerId),

	/// No longer connected to a peer for syncing purposes.
	SyncDisconnected(PeerId),

	/// Events generated by a DHT as a response to get_value or put_value requests as well as the
	/// request duration.
	Dht(DhtEvent, Duration),
}

impl<B: BlockT, H: ExHashT> Behaviour<B, H> {
	/// Builds a new `Behaviour`.
	pub fn new(
		substrate: Protocol<B, H>,
		role: Role,
		user_agent: String,
		local_public_key: PublicKey,
		block_requests: block_requests::BlockRequests<B>,
		light_client_handler: light_client_handler::LightClientHandler<B>,
		disco_config: DiscoveryConfig,
		request_response_protocols: Vec<request_responses::ProtocolConfig>,
	) -> Result<Self, request_responses::RegisterError> {
		Ok(Behaviour {
			substrate,
			peer_info: peer_info::PeerInfoBehaviour::new(user_agent, local_public_key),
			discovery: disco_config.finish(),
			request_responses:
				request_responses::RequestResponsesBehaviour::new(request_response_protocols.into_iter())?,
			block_requests,
			light_client_handler,
			events: VecDeque::new(),
			role,
		})
	}

	/// Returns the list of nodes that we know exist in the network.
	pub fn known_peers(&mut self) -> HashSet<PeerId> {
		self.discovery.known_peers()
	}

	/// Adds a hard-coded address for the given peer, that never expires.
	pub fn add_known_address(&mut self, peer_id: PeerId, addr: Multiaddr) {
		self.discovery.add_known_address(peer_id, addr)
	}

	/// Returns the number of nodes in each Kademlia kbucket for each Kademlia instance.
	///
	/// Identifies Kademlia instances by their [`ProtocolId`] and kbuckets by the base 2 logarithm
	/// of their lower bound.
	pub fn num_entries_per_kbucket(&mut self) -> impl ExactSizeIterator<Item = (&ProtocolId, Vec<(u32, usize)>)> {
		self.discovery.num_entries_per_kbucket()
	}

	/// Returns the number of records in the Kademlia record stores.
	pub fn num_kademlia_records(&mut self) -> impl ExactSizeIterator<Item = (&ProtocolId, usize)> {
		self.discovery.num_kademlia_records()
	}

	/// Returns the total size in bytes of all the records in the Kademlia record stores.
	pub fn kademlia_records_total_size(&mut self) -> impl ExactSizeIterator<Item = (&ProtocolId, usize)> {
		self.discovery.kademlia_records_total_size()
	}

	/// Borrows `self` and returns a struct giving access to the information about a node.
	///
	/// Returns `None` if we don't know anything about this node. Always returns `Some` for nodes
	/// we're connected to, meaning that if `None` is returned then we're not connected to that
	/// node.
	pub fn node(&self, peer_id: &PeerId) -> Option<peer_info::Node> {
		self.peer_info.node(peer_id)
	}

	/// Initiates sending a request.
	///
	/// An error is returned if we are not connected to the target peer of if the protocol doesn't
	/// match one that has been registered.
	pub fn send_request(&mut self, target: &PeerId, protocol: &str, request: Vec<u8>)
		-> Result<RequestId, SendRequestError>
	{
		self.request_responses.send_request(target, protocol, request)
	}

	/// Returns a shared reference to the user protocol.
	pub fn user_protocol(&self) -> &Protocol<B, H> {
		&self.substrate
	}

	/// Returns a mutable reference to the user protocol.
	pub fn user_protocol_mut(&mut self) -> &mut Protocol<B, H> {
		&mut self.substrate
	}

	/// Start querying a record from the DHT. Will later produce either a `ValueFound` or a `ValueNotFound` event.
	pub fn get_value(&mut self, key: &record::Key) {
		self.discovery.get_value(key);
	}

	/// Starts putting a record into DHT. Will later produce either a `ValuePut` or a `ValuePutFailed` event.
	pub fn put_value(&mut self, key: record::Key, value: Vec<u8>) {
		self.discovery.put_value(key, value);
	}

	/// Issue a light client request.
	pub fn light_client_request(&mut self, r: light_client_handler::Request<B>) -> Result<(), light_client_handler::Error> {
		self.light_client_handler.request(r)
	}
}

fn reported_roles_to_observed_role(local_role: &Role, remote: &PeerId, roles: Roles) -> ObservedRole {
	if roles.is_authority() {
		match local_role {
			Role::Authority { sentry_nodes }
				if sentry_nodes.iter().any(|s| s.peer_id == *remote) => ObservedRole::OurSentry,
			Role::Sentry { validators }
				if validators.iter().any(|s| s.peer_id == *remote) => ObservedRole::OurGuardedAuthority,
			_ => ObservedRole::Authority
		}
	} else if roles.is_full() {
		ObservedRole::Full
	} else {
		ObservedRole::Light
	}
}

impl<B: BlockT, H: ExHashT> NetworkBehaviourEventProcess<void::Void> for
Behaviour<B, H> {
	fn inject_event(&mut self, event: void::Void) {
		void::unreachable(event)
	}
}

impl<B: BlockT, H: ExHashT> NetworkBehaviourEventProcess<CustomMessageOutcome<B>> for
Behaviour<B, H> {
	fn inject_event(&mut self, event: CustomMessageOutcome<B>) {
		match event {
			CustomMessageOutcome::BlockImport(origin, blocks) =>
				self.events.push_back(BehaviourOut::BlockImport(origin, blocks)),
			CustomMessageOutcome::JustificationImport(origin, hash, nb, justification) =>
				self.events.push_back(BehaviourOut::JustificationImport(origin, hash, nb, justification)),
			CustomMessageOutcome::BlockRequest { target, request } => {
				match self.block_requests.send_request(&target, request) {
					block_requests::SendRequestOutcome::Ok => {
						self.events.push_back(BehaviourOut::OpaqueRequestStarted {
							peer: target,
							protocol: self.block_requests.protocol_name().to_owned(),
						});
					},
					block_requests::SendRequestOutcome::Replaced { request_duration, .. } => {
						self.events.push_back(BehaviourOut::OpaqueRequestFinished {
							peer: target.clone(),
							protocol: self.block_requests.protocol_name().to_owned(),
							request_duration,
						});
						self.events.push_back(BehaviourOut::OpaqueRequestStarted {
							peer: target,
							protocol: self.block_requests.protocol_name().to_owned(),
						});
					}
					block_requests::SendRequestOutcome::NotConnected |
					block_requests::SendRequestOutcome::EncodeError(_) => {},
				}
			},
			CustomMessageOutcome::NotificationStreamOpened { remote, protocol, roles, notifications_sink } => {
				let role = reported_roles_to_observed_role(&self.role, &remote, roles);
				self.events.push_back(BehaviourOut::NotificationStreamOpened {
					remote,
					protocol,
					role: role.clone(),
					notifications_sink: notifications_sink.clone(),
				});
			},
			CustomMessageOutcome::NotificationStreamReplaced { remote, protocol, notifications_sink } =>
				self.events.push_back(BehaviourOut::NotificationStreamReplaced {
					remote,
					protocol,
					notifications_sink: notifications_sink.clone(),
				}),
			CustomMessageOutcome::NotificationStreamClosed { remote, protocol } =>
				self.events.push_back(BehaviourOut::NotificationStreamClosed {
					remote,
					protocol,
				}),
			CustomMessageOutcome::NotificationsReceived { remote, messages } => {
				self.events.push_back(BehaviourOut::NotificationsReceived { remote, messages });
			},
			CustomMessageOutcome::PeerNewBest(peer_id, number) => {
				self.light_client_handler.update_best_block(&peer_id, number);
			}
			CustomMessageOutcome::SyncConnected(peer_id) =>
				self.events.push_back(BehaviourOut::SyncConnected(peer_id)),
			CustomMessageOutcome::SyncDisconnected(peer_id) =>
				self.events.push_back(BehaviourOut::SyncDisconnected(peer_id)),
			CustomMessageOutcome::None => {}
		}
	}
}

impl<B: BlockT, H: ExHashT> NetworkBehaviourEventProcess<request_responses::Event> for Behaviour<B, H> {
	fn inject_event(&mut self, event: request_responses::Event) {
		match event {
			request_responses::Event::InboundRequest { peer, protocol, result } => {
				self.events.push_back(BehaviourOut::InboundRequest {
					peer,
					protocol,
					result,
				});
			}

			request_responses::Event::RequestFinished { request_id, result } => {
				self.events.push_back(BehaviourOut::RequestFinished {
					request_id,
					result,
				});
			},
		}
	}
}

impl<B: BlockT, H: ExHashT> NetworkBehaviourEventProcess<block_requests::Event<B>> for Behaviour<B, H> {
	fn inject_event(&mut self, event: block_requests::Event<B>) {
		match event {
			block_requests::Event::AnsweredRequest { peer, total_handling_time } => {
				self.events.push_back(BehaviourOut::InboundRequest {
					peer,
					protocol: self.block_requests.protocol_name().to_owned().into(),
					result: Ok(total_handling_time),
				});
			},
			block_requests::Event::Response { peer, response, request_duration } => {
				self.events.push_back(BehaviourOut::OpaqueRequestFinished {
					peer: peer.clone(),
					protocol: self.block_requests.protocol_name().to_owned(),
					request_duration,
				});
				let ev = self.substrate.on_block_response(peer, response);
				self.inject_event(ev);
			}
			block_requests::Event::RequestCancelled { peer, request_duration, .. } |
			block_requests::Event::RequestTimeout { peer, request_duration, .. } => {
				// There doesn't exist any mechanism to report cancellations or timeouts yet, so
				// we process them by disconnecting the node.
				self.events.push_back(BehaviourOut::OpaqueRequestFinished {
					peer: peer.clone(),
					protocol: self.block_requests.protocol_name().to_owned(),
					request_duration,
				});
				self.substrate.on_block_request_failed(&peer);
			}
		}
	}
}

impl<B: BlockT, H: ExHashT> NetworkBehaviourEventProcess<peer_info::PeerInfoEvent>
	for Behaviour<B, H> {
	fn inject_event(&mut self, event: peer_info::PeerInfoEvent) {
		let peer_info::PeerInfoEvent::Identified {
			peer_id,
			info: IdentifyInfo {
				protocol_version,
				agent_version,
				mut listen_addrs,
				protocols,
				..
			},
		} = event;

		if listen_addrs.len() > 30 {
			debug!(
				target: "sub-libp2p",
				"Node {:?} has reported more than 30 addresses; it is identified by {:?} and {:?}",
				peer_id, protocol_version, agent_version
			);
			listen_addrs.truncate(30);
		}

		for addr in listen_addrs {
			self.discovery.add_self_reported_address(&peer_id, protocols.iter(), addr);
		}
		self.substrate.add_default_set_discovered_nodes(iter::once(peer_id));
	}
}

impl<B: BlockT, H: ExHashT> NetworkBehaviourEventProcess<DiscoveryOut>
	for Behaviour<B, H> {
	fn inject_event(&mut self, out: DiscoveryOut) {
		match out {
			DiscoveryOut::UnroutablePeer(_peer_id) => {
				// Obtaining and reporting listen addresses for unroutable peers back
				// to Kademlia is handled by the `Identify` protocol, part of the
				// `PeerInfoBehaviour`. See the `NetworkBehaviourEventProcess`
				// implementation for `PeerInfoEvent`.
			}
			DiscoveryOut::Discovered(peer_id) => {
				self.substrate.add_default_set_discovered_nodes(iter::once(peer_id));
			}
			DiscoveryOut::ValueFound(results, duration) => {
				self.events.push_back(BehaviourOut::Dht(DhtEvent::ValueFound(results), duration));
			}
			DiscoveryOut::ValueNotFound(key, duration) => {
				self.events.push_back(BehaviourOut::Dht(DhtEvent::ValueNotFound(key), duration));
			}
			DiscoveryOut::ValuePut(key, duration) => {
				self.events.push_back(BehaviourOut::Dht(DhtEvent::ValuePut(key), duration));
			}
			DiscoveryOut::ValuePutFailed(key, duration) => {
				self.events.push_back(BehaviourOut::Dht(DhtEvent::ValuePutFailed(key), duration));
			}
			DiscoveryOut::RandomKademliaStarted(protocols) => {
				for protocol in protocols {
					self.events.push_back(BehaviourOut::RandomKademliaStarted(protocol));
				}
			}
		}
	}
}

impl<B: BlockT, H: ExHashT> Behaviour<B, H> {
	fn poll<TEv>(&mut self, _: &mut Context, _: &mut impl PollParameters) -> Poll<NetworkBehaviourAction<TEv, BehaviourOut<B>>> {
		if let Some(event) = self.events.pop_front() {
			return Poll::Ready(NetworkBehaviourAction::GenerateEvent(event))
		}

		Poll::Pending
	}
}
