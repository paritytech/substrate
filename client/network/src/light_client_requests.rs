// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Helpers for outgoing and incoming light client requests.

/// For outgoing light client requests.
pub mod sender;
/// For incoming light client requests.
pub mod handler;

use crate::config::ProtocolId;

/// Generate the light client protocol name from chain specific protocol identifier.
fn generate_protocol_name(protocol_id: ProtocolId) -> String {
	let mut s = String::new();
	s.push_str("/");
	s.push_str(protocol_id.as_ref());
	s.push_str("/light/2");
	s
}

#[cfg(test)]
mod tests {
	use super::*;
	use super::{Event, LightClientRequestClient, OutboundProtocol, PeerStatus, Request, Response};
	use crate::{chain::Client, config::ProtocolId, schema};
	use assert_matches::assert_matches;
	use async_std::task;
	use codec::Encode;
	use futures::{channel::oneshot, prelude::*};
	use libp2p::{
		core::{
			connection::ConnectionId,
			identity,
			muxing::{StreamMuxerBox, SubstreamRef},
			transport::{memory::MemoryTransport, Boxed, Transport},
			upgrade, ConnectedPoint,
		},
		noise::{self, Keypair, NoiseConfig, X25519},
		swarm::{NetworkBehaviour, NetworkBehaviourAction, PollParameters},
		yamux, Multiaddr, PeerId,
	};
	use sc_client_api::{FetchChecker, RemoteReadChildRequest, StorageProof};
	use sp_blockchain::Error as ClientError;
	use sp_core::storage::ChildInfo;
	use sp_runtime::{
		generic::Header,
		traits::{BlakeTwo256, Block as BlockT, NumberFor},
	};
	use std::{
		collections::{HashMap, HashSet},
		io,
		iter::{self, FromIterator},
		pin::Pin,
		sync::Arc,
		task::{Context, Poll},
	};
	use void::Void;

	type Block =
		sp_runtime::generic::Block<Header<u64, BlakeTwo256>, substrate_test_runtime::Extrinsic>;
	type Handler = LightClientRequestClient<Block>;
	type Swarm = libp2p::swarm::Swarm<Handler>;

	fn empty_proof() -> Vec<u8> {
		StorageProof::empty().encode()
	}

	fn make_swarm(ok: bool, ps: sc_peerset::PeersetHandle, cf: super::Config) -> Swarm {
		let client = Arc::new(substrate_test_runtime_client::new());
		let checker = Arc::new(DummyFetchChecker {
			ok,
			_mark: std::marker::PhantomData,
		});
		let id_key = identity::Keypair::generate_ed25519();
		let dh_key = Keypair::<X25519>::new().into_authentic(&id_key).unwrap();
		let local_peer = id_key.public().into_peer_id();
		let transport = MemoryTransport::default()
			.upgrade(upgrade::Version::V1)
			.authenticate(NoiseConfig::xx(dh_key).into_authenticated())
			.multiplex(yamux::YamuxConfig::default())
			.boxed();
		Swarm::new(
			transport,
			LightClientRequestClient::new(cf, client, checker, ps),
			local_peer,
		)
	}

	struct DummyFetchChecker<B> {
		ok: bool,
		_mark: std::marker::PhantomData<B>,
	}

	impl<B: BlockT> light::FetchChecker<B> for DummyFetchChecker<B> {
		fn check_header_proof(
			&self,
			_request: &RemoteHeaderRequest<B::Header>,
			header: Option<B::Header>,
			_remote_proof: StorageProof,
		) -> Result<B::Header, ClientError> {
			match self.ok {
				true if header.is_some() => Ok(header.unwrap()),
				_ => Err(ClientError::Backend("Test error".into())),
			}
		}

		fn check_read_proof(
			&self,
			request: &RemoteReadRequest<B::Header>,
			_: StorageProof,
		) -> Result<HashMap<Vec<u8>, Option<Vec<u8>>>, ClientError> {
			match self.ok {
				true => Ok(request
					.keys
					.iter()
					.cloned()
					.map(|k| (k, Some(vec![42])))
					.collect()),
				false => Err(ClientError::Backend("Test error".into())),
			}
		}

		fn check_read_child_proof(
			&self,
			request: &RemoteReadChildRequest<B::Header>,
			_: StorageProof,
		) -> Result<HashMap<Vec<u8>, Option<Vec<u8>>>, ClientError> {
			match self.ok {
				true => Ok(request
					.keys
					.iter()
					.cloned()
					.map(|k| (k, Some(vec![42])))
					.collect()),
				false => Err(ClientError::Backend("Test error".into())),
			}
		}

		fn check_execution_proof(
			&self,
			_: &RemoteCallRequest<B::Header>,
			_: StorageProof,
		) -> Result<Vec<u8>, ClientError> {
			match self.ok {
				true => Ok(vec![42]),
				false => Err(ClientError::Backend("Test error".into())),
			}
		}

		fn check_changes_proof(
			&self,
			_: &RemoteChangesRequest<B::Header>,
			_: ChangesProof<B::Header>,
		) -> Result<Vec<(NumberFor<B>, u32)>, ClientError> {
			match self.ok {
				true => Ok(vec![(100u32.into(), 2)]),
				false => Err(ClientError::Backend("Test error".into())),
			}
		}

		fn check_body_proof(
			&self,
			_: &RemoteBodyRequest<B::Header>,
			body: Vec<B::Extrinsic>,
		) -> Result<Vec<B::Extrinsic>, ClientError> {
			match self.ok {
				true => Ok(body),
				false => Err(ClientError::Backend("Test error".into())),
			}
		}
	}

	fn make_config() -> super::Config {
		super::Config::new(&ProtocolId::from("foo"))
	}

	fn dummy_header() -> sp_test_primitives::Header {
		sp_test_primitives::Header {
			parent_hash: Default::default(),
			number: 0,
			state_root: Default::default(),
			extrinsics_root: Default::default(),
			digest: Default::default(),
		}
	}

	struct EmptyPollParams(PeerId);

	impl PollParameters for EmptyPollParams {
		type SupportedProtocolsIter = iter::Empty<Vec<u8>>;
		type ListenedAddressesIter = iter::Empty<Multiaddr>;
		type ExternalAddressesIter = iter::Empty<AddressRecord>;

		fn supported_protocols(&self) -> Self::SupportedProtocolsIter {
			iter::empty()
		}

		fn listened_addresses(&self) -> Self::ListenedAddressesIter {
			iter::empty()
		}

		fn external_addresses(&self) -> Self::ExternalAddressesIter {
			iter::empty()
		}

		fn local_peer_id(&self) -> &PeerId {
			&self.0
		}
	}

	fn peerset() -> (sc_peerset::Peerset, sc_peerset::PeersetHandle) {
		let cfg = sc_peerset::SetConfig {
			in_peers: 128,
			out_peers: 128,
			bootnodes: Default::default(),
			reserved_only: false,
			reserved_nodes: Default::default(),
		};
		sc_peerset::Peerset::from_config(sc_peerset::PeersetConfig { sets: vec![cfg] })
	}

	fn make_behaviour(
		ok: bool,
		ps: sc_peerset::PeersetHandle,
		cf: super::Config,
	) -> LightClientRequestClient<Block> {
		let client = Arc::new(substrate_test_runtime_client::new());
		let checker = Arc::new(DummyFetchChecker {
			ok,
			_mark: std::marker::PhantomData,
		});
		LightClientRequestClient::new(cf, client, checker, ps)
	}

	fn empty_dialer() -> ConnectedPoint {
		ConnectedPoint::Dialer {
			address: Multiaddr::empty(),
		}
	}

	fn poll(
		mut b: &mut LightClientRequestClient<Block>,
	) -> Poll<NetworkBehaviourAction<OutboundProtocol, Void>> {
		let mut p = EmptyPollParams(PeerId::random());
		match future::poll_fn(|cx| Pin::new(&mut b).poll(cx, &mut p)).now_or_never() {
			Some(a) => Poll::Ready(a),
			None => Poll::Pending,
		}
	}

	#[test]
	fn disconnects_from_peer_if_told() {
		let peer = PeerId::random();
		let pset = peerset();
		let mut behaviour = make_behaviour(true, pset.1, make_config());

		behaviour.inject_connection_established(&peer, &ConnectionId::new(1), &empty_dialer());
		behaviour.inject_connected(&peer);
		assert_eq!(1, behaviour.peers.len());

		behaviour.inject_connection_closed(&peer, &ConnectionId::new(1), &empty_dialer());
		behaviour.inject_disconnected(&peer);
		assert_eq!(0, behaviour.peers.len())
	}

	#[test]
	fn disconnects_from_peer_if_request_times_out() {
		let peer0 = PeerId::random();
		let peer1 = PeerId::random();
		let pset = peerset();
		let mut behaviour = make_behaviour(true, pset.1, make_config());

		behaviour.inject_connection_established(&peer0, &ConnectionId::new(1), &empty_dialer());
		behaviour.inject_connected(&peer0);
		behaviour.inject_connection_established(&peer1, &ConnectionId::new(2), &empty_dialer());
		behaviour.inject_connected(&peer1);

		// We now know about two peers.
		assert_eq!(
			HashSet::from_iter(&[peer0.clone(), peer1.clone()]),
			behaviour.peers.keys().collect::<HashSet<_>>()
		);

		// No requests have been made yet.
		assert!(behaviour.pending_requests.is_empty());
		assert!(behaviour.outstanding.is_empty());

		// Issue our first request!
		let chan = oneshot::channel();
		let request = light::RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: Some(1),
		};
		behaviour
			.request(Request::Call {
				request,
				sender: chan.0,
			})
			.unwrap();
		assert_eq!(1, behaviour.pending_requests.len());

		// The behaviour should now attempt to send the request.
		assert_matches!(poll(&mut behaviour), Poll::Ready(NetworkBehaviourAction::NotifyHandler { peer_id, .. }) => {
			assert!(peer_id == peer0 || peer_id == peer1)
		});

		// And we should have one busy peer.
		assert!({
			let (idle, busy): (Vec<_>, Vec<_>) = behaviour
				.peers
				.iter()
				.partition(|(_, info)| info.status == PeerStatus::Idle);

			idle.len() == 1
				&& busy.len() == 1
				&& (idle[0].0 == &peer0 || busy[0].0 == &peer0)
				&& (idle[0].0 == &peer1 || busy[0].0 == &peer1)
		});

		// No more pending requests, but one should be outstanding.
		assert_eq!(0, behaviour.pending_requests.len());
		assert_eq!(1, behaviour.outstanding.len());

		// We now set back the timestamp of the outstanding request to make it expire.
		let request = behaviour.outstanding.values_mut().next().unwrap();
		request.timestamp -= make_config().request_timeout;

		// Make progress, but do not expect some action.
		assert_matches!(poll(&mut behaviour), Poll::Pending);

		// The request should have timed out by now and the corresponding peer be removed.
		assert_eq!(1, behaviour.peers.len());
		// Since we asked for one retry, the request should be back in the pending queue.
		assert_eq!(1, behaviour.pending_requests.len());
		// No other request should be ongoing.
		assert_eq!(0, behaviour.outstanding.len());
	}

	#[test]
	fn disconnects_from_peer_on_incorrect_response() {
		let peer = PeerId::random();
		let pset = peerset();
		let mut behaviour = make_behaviour(false, pset.1, make_config());
		//                                 ^--- Making sure the response data check fails.

		let conn = ConnectionId::new(1);
		behaviour.inject_connection_established(&peer, &conn, &empty_dialer());
		behaviour.inject_connected(&peer);
		assert_eq!(1, behaviour.peers.len());

		let chan = oneshot::channel();
		let request = light::RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: Some(1),
		};
		behaviour
			.request(Request::Call {
				request,
				sender: chan.0,
			})
			.unwrap();

		assert_eq!(1, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len());
		poll(&mut behaviour); // Make progress
		assert_eq!(0, behaviour.pending_requests.len());
		assert_eq!(1, behaviour.outstanding.len());

		let request_id = *behaviour.outstanding.keys().next().unwrap();

		let response = {
			let r = schema::v1::light::RemoteCallResponse {
				proof: empty_proof(),
			};
			schema::v1::light::Response {
				response: Some(schema::v1::light::response::Response::RemoteCallResponse(r)),
			}
		};

		behaviour.inject_event(
			peer.clone(),
			conn,
			Event::Response(request_id, Response::Light(response)),
		);
		assert!(behaviour.peers.is_empty());

		poll(&mut behaviour); // More progress

		// The request should be back in the pending queue
		assert_eq!(1, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len());
	}

	#[test]
	fn disconnects_from_peer_on_unexpected_response() {
		let peer = PeerId::random();
		let pset = peerset();
		let mut behaviour = make_behaviour(true, pset.1, make_config());

		let conn = ConnectionId::new(1);
		behaviour.inject_connection_established(&peer, &conn, &empty_dialer());
		behaviour.inject_connected(&peer);
		assert_eq!(1, behaviour.peers.len());
		assert_eq!(0, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len());

		// Some unsolicited response
		let response = {
			let r = schema::v1::light::RemoteCallResponse {
				proof: empty_proof(),
			};
			schema::v1::light::Response {
				response: Some(schema::v1::light::response::Response::RemoteCallResponse(r)),
			}
		};

		behaviour.inject_event(
			peer.clone(),
			conn,
			Event::Response(2347895932, Response::Light(response)),
		);

		assert!(behaviour.peers.is_empty());
		poll(&mut behaviour);
		assert_eq!(0, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len());
	}

	#[test]
	fn disconnects_from_peer_on_wrong_response_type() {
		let peer = PeerId::random();
		let pset = peerset();
		let mut behaviour = make_behaviour(true, pset.1, make_config());

		let conn = ConnectionId::new(1);
		behaviour.inject_connection_established(&peer, &conn, &empty_dialer());
		behaviour.inject_connected(&peer);
		assert_eq!(1, behaviour.peers.len());

		let chan = oneshot::channel();
		let request = light::RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: Some(1),
		};
		behaviour
			.request(Request::Call {
				request,
				sender: chan.0,
			})
			.unwrap();

		assert_eq!(1, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len());
		poll(&mut behaviour); // Make progress
		assert_eq!(0, behaviour.pending_requests.len());
		assert_eq!(1, behaviour.outstanding.len());

		let request_id = *behaviour.outstanding.keys().next().unwrap();

		let response = {
			let r = schema::v1::light::RemoteReadResponse {
				proof: empty_proof(),
			}; // Not a RemoteCallResponse!
			schema::v1::light::Response {
				response: Some(schema::v1::light::response::Response::RemoteReadResponse(r)),
			}
		};

		behaviour.inject_event(
			peer.clone(),
			conn,
			Event::Response(request_id, Response::Light(response)),
		);
		assert!(behaviour.peers.is_empty());

		poll(&mut behaviour); // More progress

		// The request should be back in the pending queue
		assert_eq!(1, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len());
	}

	#[test]
	fn receives_remote_failure_after_retry_count_failures() {
		let peer1 = PeerId::random();
		let peer2 = PeerId::random();
		let peer3 = PeerId::random();
		let peer4 = PeerId::random();
		let pset = peerset();
		let mut behaviour = make_behaviour(false, pset.1, make_config());
		//                                 ^--- Making sure the response data check fails.

		let conn1 = ConnectionId::new(1);
		behaviour.inject_connection_established(&peer1, &conn1, &empty_dialer());
		behaviour.inject_connected(&peer1);
		let conn2 = ConnectionId::new(2);
		behaviour.inject_connection_established(&peer2, &conn2, &empty_dialer());
		behaviour.inject_connected(&peer2);
		let conn3 = ConnectionId::new(3);
		behaviour.inject_connection_established(&peer3, &conn3, &empty_dialer());
		behaviour.inject_connected(&peer3);
		let conn4 = ConnectionId::new(3);
		behaviour.inject_connection_established(&peer4, &conn4, &empty_dialer());
		behaviour.inject_connected(&peer4);
		assert_eq!(4, behaviour.peers.len());

		let mut chan = oneshot::channel();
		let request = light::RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: Some(3), // Attempt up to three retries.
		};
		behaviour
			.request(Request::Call {
				request,
				sender: chan.0,
			})
			.unwrap();

		assert_eq!(1, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len());
		assert_matches!(
			poll(&mut behaviour),
			Poll::Ready(NetworkBehaviourAction::NotifyHandler { .. })
		);
		assert_eq!(0, behaviour.pending_requests.len());
		assert_eq!(1, behaviour.outstanding.len());

		for i in 1..=3 {
			// Construct an invalid response
			let request_id = *behaviour.outstanding.keys().next().unwrap();
			let responding_peer = behaviour.outstanding.values().next().unwrap().peer.clone();
			let response = {
				let r = schema::v1::light::RemoteCallResponse {
					proof: empty_proof(),
				};
				schema::v1::light::Response {
					response: Some(schema::v1::light::response::Response::RemoteCallResponse(r)),
				}
			};
			let conn = ConnectionId::new(i);
			behaviour.inject_event(
				responding_peer,
				conn,
				Event::Response(request_id, Response::Light(response.clone())),
			);
			assert_matches!(
				poll(&mut behaviour),
				Poll::Ready(NetworkBehaviourAction::NotifyHandler { .. })
			);
			assert_matches!(chan.1.try_recv(), Ok(None))
		}
		// Final invalid response
		let request_id = *behaviour.outstanding.keys().next().unwrap();
		let responding_peer = behaviour.outstanding.values().next().unwrap().peer.clone();
		let response = {
			let r = schema::v1::light::RemoteCallResponse {
				proof: empty_proof(),
			};
			schema::v1::light::Response {
				response: Some(schema::v1::light::response::Response::RemoteCallResponse(r)),
			}
		};
		behaviour.inject_event(
			responding_peer,
			conn4,
			Event::Response(request_id, Response::Light(response)),
		);
		assert_matches!(poll(&mut behaviour), Poll::Pending);
		assert_matches!(
			chan.1.try_recv(),
			Ok(Some(Err(ClientError::RemoteFetchFailed)))
		)
	}

	fn issue_request(request: Request<Block>) {
		let peer = PeerId::random();
		let pset = peerset();
		let mut behaviour = make_behaviour(true, pset.1, make_config());

		let conn = ConnectionId::new(1);
		behaviour.inject_connection_established(&peer, &conn, &empty_dialer());
		behaviour.inject_connected(&peer);
		assert_eq!(1, behaviour.peers.len());

		let response = match request {
			Request::Body { .. } => unimplemented!(),
			Request::Header { .. } => {
				let r = schema::v1::light::RemoteHeaderResponse {
					header: dummy_header().encode(),
					proof: empty_proof(),
				};
				schema::v1::light::Response {
					response: Some(schema::v1::light::response::Response::RemoteHeaderResponse(
						r,
					)),
				}
			}
			Request::Read { .. } => {
				let r = schema::v1::light::RemoteReadResponse {
					proof: empty_proof(),
				};
				schema::v1::light::Response {
					response: Some(schema::v1::light::response::Response::RemoteReadResponse(r)),
				}
			}
			Request::ReadChild { .. } => {
				let r = schema::v1::light::RemoteReadResponse {
					proof: empty_proof(),
				};
				schema::v1::light::Response {
					response: Some(schema::v1::light::response::Response::RemoteReadResponse(r)),
				}
			}
			Request::Call { .. } => {
				let r = schema::v1::light::RemoteCallResponse {
					proof: empty_proof(),
				};
				schema::v1::light::Response {
					response: Some(schema::v1::light::response::Response::RemoteCallResponse(r)),
				}
			}
			Request::Changes { .. } => {
				let r = schema::v1::light::RemoteChangesResponse {
					max: iter::repeat(1).take(32).collect(),
					proof: Vec::new(),
					roots: Vec::new(),
					roots_proof: empty_proof(),
				};
				schema::v1::light::Response {
					response: Some(schema::v1::light::response::Response::RemoteChangesResponse(r)),
				}
			}
		};

		behaviour.request(request).unwrap();

		assert_eq!(1, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len());
		assert_matches!(
			poll(&mut behaviour),
			Poll::Ready(NetworkBehaviourAction::NotifyHandler { .. })
		);
		assert_eq!(0, behaviour.pending_requests.len());
		assert_eq!(1, behaviour.outstanding.len());
		assert_eq!(1, *behaviour.outstanding.keys().next().unwrap());

		behaviour.inject_event(
			peer.clone(),
			conn,
			Event::Response(1, Response::Light(response)),
		);

		poll(&mut behaviour);

		assert_eq!(0, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len())
	}

	#[test]
	fn receives_remote_call_response() {
		let mut chan = oneshot::channel();
		let request = light::RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: None,
		};
		issue_request(Request::Call {
			request,
			sender: chan.0,
		});
		assert_matches!(chan.1.try_recv(), Ok(Some(Ok(_))))
	}

	#[test]
	fn receives_remote_read_response() {
		let mut chan = oneshot::channel();
		let request = light::RemoteReadRequest {
			header: dummy_header(),
			block: Default::default(),
			keys: vec![b":key".to_vec()],
			retry_count: None,
		};
		issue_request(Request::Read {
			request,
			sender: chan.0,
		});
		assert_matches!(chan.1.try_recv(), Ok(Some(Ok(_))))
	}

	#[test]
	fn receives_remote_read_child_response() {
		let mut chan = oneshot::channel();
		let child_info = ChildInfo::new_default(&b":child_storage:default:sub"[..]);
		let request = light::RemoteReadChildRequest {
			header: dummy_header(),
			block: Default::default(),
			storage_key: child_info.prefixed_storage_key(),
			keys: vec![b":key".to_vec()],
			retry_count: None,
		};
		issue_request(Request::ReadChild {
			request,
			sender: chan.0,
		});
		assert_matches!(chan.1.try_recv(), Ok(Some(Ok(_))))
	}

	#[test]
	fn receives_remote_header_response() {
		let mut chan = oneshot::channel();
		let request = light::RemoteHeaderRequest {
			cht_root: Default::default(),
			block: 1,
			retry_count: None,
		};
		issue_request(Request::Header {
			request,
			sender: chan.0,
		});
		assert_matches!(chan.1.try_recv(), Ok(Some(Ok(_))))
	}

	#[test]
	fn receives_remote_changes_response() {
		let mut chan = oneshot::channel();
		let request = light::RemoteChangesRequest {
			changes_trie_configs: vec![sp_core::ChangesTrieConfigurationRange {
				zero: (0, Default::default()),
				end: None,
				config: Some(sp_core::ChangesTrieConfiguration::new(4, 2)),
			}],
			first_block: (1, Default::default()),
			last_block: (100, Default::default()),
			max_block: (100, Default::default()),
			tries_roots: (1, Default::default(), Vec::new()),
			key: Vec::new(),
			storage_key: None,
			retry_count: None,
		};
		issue_request(Request::Changes {
			request,
			sender: chan.0,
		});
		assert_matches!(chan.1.try_recv(), Ok(Some(Ok(_))))
	}

	fn send_receive(request: Request<Block>) {
		// We start a swarm on the listening side which awaits incoming requests and answers them:
		let local_pset = peerset();
		let local_listen_addr: libp2p::Multiaddr =
			libp2p::multiaddr::Protocol::Memory(rand::random()).into();
		let mut local_swarm = make_swarm(true, local_pset.1, make_config());
		Swarm::listen_on(&mut local_swarm, local_listen_addr.clone()).unwrap();

		// We also start a swarm that makes requests and awaits responses:
		let remote_pset = peerset();
		let mut remote_swarm = make_swarm(true, remote_pset.1, make_config());

		// We now schedule a request, dial the remote and let the two swarm work it out:
		remote_swarm.request(request).unwrap();
		Swarm::dial_addr(&mut remote_swarm, local_listen_addr).unwrap();

		let future = {
			let a = local_swarm.for_each(|_| future::ready(()));
			let b = remote_swarm.for_each(|_| future::ready(()));
			future::join(a, b).map(|_| ())
		};

		task::spawn(future);
	}

	#[test]
	fn send_receive_call() {
		let chan = oneshot::channel();
		let request = light::RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: None,
		};
		send_receive(Request::Call {
			request,
			sender: chan.0,
		});
		assert_eq!(vec![42], task::block_on(chan.1).unwrap().unwrap());
		//              ^--- from `DummyFetchChecker::check_execution_proof`
	}

	#[test]
	fn send_receive_read() {
		let chan = oneshot::channel();
		let request = light::RemoteReadRequest {
			header: dummy_header(),
			block: Default::default(),
			keys: vec![b":key".to_vec()],
			retry_count: None,
		};
		send_receive(Request::Read {
			request,
			sender: chan.0,
		});
		assert_eq!(
			Some(vec![42]),
			task::block_on(chan.1)
				.unwrap()
				.unwrap()
				.remove(&b":key"[..])
				.unwrap()
		);
		//                   ^--- from `DummyFetchChecker::check_read_proof`
	}

	#[test]
	fn send_receive_read_child() {
		let chan = oneshot::channel();
		let child_info = ChildInfo::new_default(&b":child_storage:default:sub"[..]);
		let request = light::RemoteReadChildRequest {
			header: dummy_header(),
			block: Default::default(),
			storage_key: child_info.prefixed_storage_key(),
			keys: vec![b":key".to_vec()],
			retry_count: None,
		};
		send_receive(Request::ReadChild {
			request,
			sender: chan.0,
		});
		assert_eq!(
			Some(vec![42]),
			task::block_on(chan.1)
				.unwrap()
				.unwrap()
				.remove(&b":key"[..])
				.unwrap()
		);
		//                   ^--- from `DummyFetchChecker::check_read_child_proof`
	}

	#[test]
	fn send_receive_header() {
		sp_tracing::try_init_simple();
		let chan = oneshot::channel();
		let request = light::RemoteHeaderRequest {
			cht_root: Default::default(),
			block: 1,
			retry_count: None,
		};
		send_receive(Request::Header {
			request,
			sender: chan.0,
		});
		// The remote does not know block 1:
		assert_matches!(
			task::block_on(chan.1).unwrap(),
			Err(ClientError::RemoteFetchFailed)
		);
	}

	#[test]
	fn send_receive_changes() {
		let chan = oneshot::channel();
		let request = light::RemoteChangesRequest {
			changes_trie_configs: vec![sp_core::ChangesTrieConfigurationRange {
				zero: (0, Default::default()),
				end: None,
				config: Some(sp_core::ChangesTrieConfiguration::new(4, 2)),
			}],
			first_block: (1, Default::default()),
			last_block: (100, Default::default()),
			max_block: (100, Default::default()),
			tries_roots: (1, Default::default(), Vec::new()),
			key: Vec::new(),
			storage_key: None,
			retry_count: None,
		};
		send_receive(Request::Changes {
			request,
			sender: chan.0,
		});
		assert_eq!(vec![(100, 2)], task::block_on(chan.1).unwrap().unwrap());
		//              ^--- from `DummyFetchChecker::check_changes_proof`
	}

	#[test]
	fn body_request_fields_encoded_properly() {
		let (sender, _) = oneshot::channel();
		let serialized_request = serialize_request::<Block>(&Request::Body {
			request: RemoteBodyRequest {
				header: dummy_header(),
				retry_count: None,
			},
			sender,
		})
		.unwrap();
		let deserialized_request =
			schema::v1::BlockRequest::decode(&serialized_request[..]).unwrap();
		assert!(BlockAttributes::from_be_u32(deserialized_request.fields)
			.unwrap()
			.contains(BlockAttributes::BODY));
	}
}
