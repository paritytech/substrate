#![no_main]

use sc_network::{
	config::MultiaddrWithPeerId, NetworkNotification, NetworkPeers, NetworkStateInfo,
};

use futures::prelude::*;
use std::time::Duration;

use sc_network_test::service::build_nodes_one_proto;

use arbitrary::{Arbitrary, Result as ArbitraryResult, Unstructured};

const PROTOCOL_NAME: &str = "/foo";

#[derive(Debug)]
struct ReputationChange(sc_network::ReputationChange);

impl<'a> Arbitrary<'a> for ReputationChange {
	fn arbitrary(u: &mut Unstructured<'a>) -> ArbitraryResult<Self> {
		let value = u.arbitrary::<i32>()?;
		let reason = "some_reason";
		let reputation_change = sc_network::ReputationChange { value, reason };

		Ok(Self(reputation_change))
	}
}

// Who will trigger an event
#[derive(Arbitrary, Debug)]
enum SenderNode {
	A,
	B,
}

// A receiver to send events to
#[derive(Arbitrary, Debug)]
enum ReceiverNode {
	A,
	B,
}

#[derive(Arbitrary, Debug)]
enum Action {
	WriteNotification(SenderNode, ReceiverNode, Vec<u8>),
	NotificationSender(SenderNode, ReceiverNode),
	DisconnectPeer(SenderNode, ReceiverNode),
	ReportPeer(SenderNode, ReceiverNode, ReputationChange),
	AcceptUnreservedPeers(SenderNode),
	DenyUnreservedPeers(SenderNode),
	AddReservedPeer(SenderNode, ReceiverNode),
	RemoveReservedPeer(SenderNode, ReceiverNode),
	SetAuthorizedOnly(SenderNode, bool),
}

use libfuzzer_sys::fuzz_target;

use tokio::runtime;

fuzz_target!(|actions: Vec<Action>| {
	// Create a runtime that _must_ be driven from a call
	// to `Runtime::block_on`.
	let rt = runtime::Builder::new_current_thread().build().unwrap();

	rt.block_on(async move {
		run(actions);
	});
});

fn run(actions: Vec<Action>) {
	let (a, mut events_stream_a, b, mut events_stream_b) = build_nodes_one_proto();
	for action in actions {
		match action {
			Action::WriteNotification(sender, receiver, data) => {
				let sender = if matches!(sender, SenderNode::A) { &a } else { &b };
				let receiver = if matches!(receiver, ReceiverNode::A) { &a } else { &b };
				sender.write_notification(
					receiver.local_peer_id().clone(),
					PROTOCOL_NAME.into(),
					data,
				);
			},
			Action::NotificationSender(sender, receiver) => {
				let sender = if matches!(sender, SenderNode::A) { &a } else { &b };
				let receiver = if matches!(receiver, ReceiverNode::A) { &a } else { &b };
				let _ = sender
					.notification_sender(receiver.local_peer_id().clone(), PROTOCOL_NAME.into());
			},
			Action::DisconnectPeer(sender, receiver) => {
				let sender = if matches!(sender, SenderNode::A) { &a } else { &b };
				let receiver = if matches!(receiver, ReceiverNode::A) { &a } else { &b };
				sender.disconnect_peer(receiver.local_peer_id().clone(), PROTOCOL_NAME.into());
			},
			Action::ReportPeer(sender, receiver, reputation_change) => {
				let sender = if matches!(sender, SenderNode::A) { &a } else { &b };
				let receiver = if matches!(receiver, ReceiverNode::A) { &a } else { &b };
				let reputation_change = reputation_change.0;
				sender.report_peer(receiver.local_peer_id().clone(), reputation_change);
			},
			Action::AcceptUnreservedPeers(sender) => {
				let sender = if matches!(sender, SenderNode::A) { &a } else { &b };
				sender.accept_unreserved_peers();
			},
			Action::DenyUnreservedPeers(sender) => {
				let sender = if matches!(sender, SenderNode::A) { &a } else { &b };
				sender.deny_unreserved_peers();
			},
			Action::AddReservedPeer(sender, receiver) => {
				let sender = if matches!(sender, SenderNode::A) { &a } else { &b };
				let receiver = if matches!(receiver, ReceiverNode::A) { &a } else { &b };
				let listen_addr = receiver.listen_addresses()[0].clone();
				let multiaddr = MultiaddrWithPeerId {
					multiaddr: listen_addr,
					peer_id: receiver.local_peer_id(),
				};
				let _ = sender.add_reserved_peer(multiaddr);
			},
			Action::RemoveReservedPeer(sender, receiver) => {
				let sender = if matches!(sender, SenderNode::A) { &a } else { &b };
				let receiver = if matches!(receiver, ReceiverNode::A) { &a } else { &b };
				sender.remove_reserved_peer(receiver.local_peer_id().clone());
			},
			Action::SetAuthorizedOnly(sender, reserved_only) => {
				let sender = if matches!(sender, SenderNode::A) { &a } else { &b };
				sender.set_authorized_only(reserved_only);
			},
		};
	}

	async_std::task::block_on(async {
		// Grab next event from either `events_stream_a` or `events_stream_b`.
		let _next_event = {
			let next_a = events_stream_a.next();
			let next_b = events_stream_b.next();
			// We also await on a small timer, otherwise it is possible for the test to wait
			// forever while nothing at all happens on the network.
			let continue_test = futures_timer::Delay::new(Duration::from_millis(20));
			futures::select! {
				_next_a_res = next_a.fuse() => {},
				_next_b_res = next_b.fuse() => {},
				_ = continue_test.fuse() => {},
			};
		};
	});
}
