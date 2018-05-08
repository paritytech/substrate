// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

use super::*;
use message::*;
use futures::Stream;

#[test]
fn bft_messages_include_those_sent_before_asking_for_stream() {
	let mut config = ::config::ProtocolConfig::default();
	config.roles = ::service::Role::VALIDATOR | ::service::Role::FULL;

	let mut net = TestNet::new_with_config(2, config);
	net.sync(); // necessary for handshaking

	let peer = net.peer(0);
	let mut io = TestIo::new(&peer.queue, None);
	let bft_message = BftMessage::Consensus(SignedConsensusMessage::Vote(SignedConsensusVote {
		vote: ConsensusVote::AdvanceRound(0),
		sender: [0; 32],
		signature: Default::default(),
	}));

	let localized = LocalizedBftMessage {
		message: bft_message,
		parent_hash: [1; 32].into(),
	};


	let as_bytes = ::serde_json::to_vec(&Message::BftMessage(localized.clone())).unwrap();
	peer.sync.handle_packet(&mut io, 1, &as_bytes[..]);

	let stream = peer.sync.bft_messages([1; 32].into());

	assert_eq!(stream.wait().next(), Some(Ok(localized)));
}
