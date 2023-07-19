#![no_main]

use sc_network::{
	peerset::{Peerset, PeersetConfig, PeersetHandle, SetConfig},
	protocol::notifications::{
		handler::{NotifsHandler, NotifsHandlerOut},
		Notifications, ProtocolConfig,
	},
};

use arbitrary::{Arbitrary, Result as AResult, Unstructured};
use futures::{future::BoxFuture, FutureExt};
use libp2p::{
	core::ConnectedPoint,
	multihash::Multihash,
	swarm::{
		behaviour::FromSwarm, AddressRecord, ConnectionId, NetworkBehaviour, PollParameters,
		THandlerInEvent, ToSwarm,
	},
	Multiaddr, PeerId,
};

use std::{collections::HashSet, future::IntoFuture, iter};

use libfuzzer_sys::fuzz_target;

fn build_notifs() -> (Notifications, PeersetHandle) {
	let (peerset, peerset_handle) = {
		let mut sets = Vec::with_capacity(1);

		sets.push(SetConfig {
			in_peers: 25,
			out_peers: 25,
			bootnodes: Vec::new(),
			reserved_nodes: HashSet::new(),
			reserved_only: false,
		});

		Peerset::from_config(PeersetConfig { sets })
	};

	(
		Notifications::new(
			peerset,
			iter::once(ProtocolConfig {
				name: "/foo".into(),
				fallback_names: Vec::new(),
				handshake: vec![1, 2, 3, 4],
				max_notification_size: u64::MAX,
			}),
		),
		peerset_handle,
	)
}

#[derive(Clone, Debug)]
struct Mh(Multihash);

impl<'a> Arbitrary<'a> for Mh {
	fn arbitrary(u: &mut Unstructured<'a>) -> AResult<Self> {
		let hash: [u8; 32] = u.arbitrary()?;
		let r = Mh(Multihash::wrap(0x0, &hash).expect("The digest size is never too large"));
		Ok(r)
	}
}

#[derive(Clone, Debug)]
struct PId(PeerId);

impl<'a> Arbitrary<'a> for PId {
	fn arbitrary(u: &mut Unstructured<'a>) -> AResult<Self> {
		let mh = Mh::arbitrary(u)?;

		let r = PId(
			PeerId::from_multihash(mh.0).expect("identity multihash works if digest size < 64")
		);
		Ok(r)
	}
}

#[derive(Clone)]
struct MockPollParams {
	peer_id: PeerId,
	addr: Multiaddr,
}

impl MockPollParams {
	fn random() -> Self {
		Self { peer_id: PeerId::random(), addr: Multiaddr::empty() }
	}
}

impl PollParameters for MockPollParams {
	type SupportedProtocolsIter = std::vec::IntoIter<Vec<u8>>;
	type ListenedAddressesIter = std::vec::IntoIter<Multiaddr>;
	type ExternalAddressesIter = std::vec::IntoIter<AddressRecord>;

	fn supported_protocols(&self) -> Self::SupportedProtocolsIter {
		vec![].into_iter()
	}

	fn listened_addresses(&self) -> Self::ListenedAddressesIter {
		vec![self.addr.clone()].into_iter()
	}

	fn external_addresses(&self) -> Self::ExternalAddressesIter {
		vec![].into_iter()
	}

	fn local_peer_id(&self) -> &PeerId {
		&self.peer_id
	}
}

#[derive(Debug)]
struct NOut(PId, usize, NotifsHandlerOut);

impl<'a> Arbitrary<'a> for NOut {
	fn arbitrary(u: &mut Unstructured<'a>) -> AResult<Self> {
		let pid = PId::arbitrary(u)?;
		let conn = usize::arbitrary(u)?;
		let t = u8::arbitrary(u)? % 6;
		let protocol_index = 0; // TODO usize::arbitrary(u)?;
		let event = match t {
			0 => NotifsHandlerOut::OpenDesiredByRemote { protocol_index },
			1 => NotifsHandlerOut::CloseDesired { protocol_index },
			2 => NotifsHandlerOut::CloseResult { protocol_index },
			3 => NotifsHandlerOut::OpenDesiredByRemote { protocol_index }, // TODO OpenResultOk
			4 => NotifsHandlerOut::OpenResultErr { protocol_index },
			5 => {
				let b = Vec::<u8>::arbitrary(u)?;
				let message = b[..].into();
				NotifsHandlerOut::Notification { protocol_index, message }
			},
			_ => {
				unreachable!("no such event type is possible")
			},
		};
		let r = NOut(pid, conn, event);
		Ok(r)
	}
}

#[derive(Arbitrary, Debug)]
enum Action {
	//SetHandshake(usize, Vec<u8>),
	Disconnect(PId, usize),
	ConnectionEstablished(PId, usize),
	ConnectionClosed(PId, usize),
	OutEvent(NOut),
	Poll,
}

fuzz_target!(|actions: Vec<Action>| {
	let (mut notifs, _handle) = build_notifs();
	let connected = ConnectedPoint::Listener {
		local_addr: Multiaddr::empty(),
		send_back_addr: Multiaddr::empty(),
	};
	let mut connected_peers = HashSet::new();
	for action in actions {
		match action {
			// Action::SetHandshake(id, message) => {
			// 	let id = 0;
			// 	notifs.set_notif_protocol_handshake(id.into(), message);
			// }
			Action::Disconnect(pid, id) => {
				notifs.disconnect_peer(&pid.0, id.into());
			},
			Action::ConnectionEstablished(pid, id) => {
				let peer = pid.0;
				let conn = ConnectionId::new_unchecked(id);
				connected_peers.insert((peer.clone(), conn));
				notifs.on_swarm_event(FromSwarm::ConnectionEstablished(
					libp2p::swarm::behaviour::ConnectionEstablished {
						peer_id: peer,
						connection_id: conn,
						endpoint: &connected,
						failed_addresses: &[],
						other_established: 0usize,
					},
				));
			},
			Action::ConnectionClosed(pid, id) => {
				let peer = pid.0;
				let conn = ConnectionId::new_unchecked(id);
				let had_peer = connected_peers.remove(&(peer, conn));
				if had_peer {
					notifs.on_swarm_event(FromSwarm::ConnectionClosed(
						libp2p::swarm::behaviour::ConnectionClosed {
							peer_id: peer,
							connection_id: conn,
							endpoint: &connected,
							handler: NotifsHandler::new(peer, connected.clone(), vec![]),
							remaining_established: 0usize,
						},
					));
				}
			},
			Action::OutEvent(NOut(pid, id, event)) => {
				let peer = pid.0;
				let conn = ConnectionId::new_unchecked(id);
				match &event {
					| NotifsHandlerOut::OpenResultErr { .. }
					| NotifsHandlerOut::CloseResult { .. }
					=> {
						break; // TODO
					}
					| NotifsHandlerOut::CloseDesired { .. }
					//| NotifsHandlerOut::CloseResult { .. }
					//| NotifsHandlerOut::OpenResultErr { .. }
					| NotifsHandlerOut::OpenDesiredByRemote { .. }
					=> {
						if !connected_peers.contains(&(peer, conn)) {
							break;
						}
					},
					_ => {}
				}
				notifs.on_connection_handler_event(peer, conn, event);
			},
			Action::Poll => {
				struct Notifs<'a> {
					notifs: &'a mut Notifications,
				}

				impl<'a> IntoFuture for Notifs<'a> {
					type Output = ToSwarm<
						<Notifications as NetworkBehaviour>::OutEvent,
						THandlerInEvent<Notifications>,
					>;
					type IntoFuture = BoxFuture<'a, Self::Output>;

					fn into_future(self) -> Self::IntoFuture {
						let mut params = MockPollParams::random();
						Box::pin(async move {
							futures::future::poll_fn(|cx| self.notifs.poll(cx, &mut params)).await
						})
					}
				}

				loop {
					let n = Notifs { notifs: &mut notifs };

					if let Some(_event) = n.into_future().now_or_never() {
					} else {
						break
					}
				}
			},
		}
	}
});
