// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Incoming message streams that verify signatures, and outgoing message streams
//! that sign or re-shape.

use futures::prelude::*;
use futures::sync::mpsc;
use codec::{Encode, Decode};
use substrate_primitives::{ed25519, AuthorityId};
use runtime_primitives::traits::Block as BlockT;
use {Error, Network, Message, SignedMessage};

use std::collections::HashMap;
use std::sync::Arc;

fn localized_payload<E: Encode>(round: u64, set_id: u64, message: &E) -> Vec<u8> {
	let mut v = message.encode();

	round.using_encoded(|s| v.extend(s));
	set_id.using_encoded(|s| v.extend(s));

	v
}

/// converts a message stream into a stream of signed messages.
/// the output stream checks signatures also.
pub(crate) fn checked_message_stream<Block: BlockT, S>(
	round: u64,
	set_id: u64,
	inner: S,
	voters: Arc<HashMap<AuthorityId, u64>>,
)
	-> impl Stream<Item=SignedMessage<Block>,Error=Error> where
	S: Stream<Item=Vec<u8>,Error=()>
{
	inner
		.filter_map(|raw| {
			let decoded = SignedMessage::<Block>::decode(&mut &raw[..]);
			if decoded.is_none() {
				debug!(target: "afg", "Skipping malformed message {:?}", raw);
			}
			decoded
		})
		.and_then(move |msg| {
			// check signature.
			if !voters.contains_key(&msg.id) {
				debug!(target: "afg", "Skipping message from unknown voter {}", msg.id);
				return Ok(None);
			}

			let as_public = ::ed25519::Public::from_raw(msg.id.0);
			let encoded_raw = localized_payload(round, set_id, &msg.message);
			if ::ed25519::verify_strong(&msg.signature, &encoded_raw, as_public) {
				Ok(Some(msg))
			} else {
				debug!(target: "afg", "Skipping message with bad signature");
				Ok(None)
			}
		})
		.filter_map(|x| x)
		.map_err(|()| Error::Network(format!("Failed to receive message on unbounded stream")))
}

struct OutgoingMessages<Block: BlockT, N: Network> {
	round: u64,
	set_id: u64,
	locals: Option<(Arc<ed25519::Pair>, AuthorityId)>,
	sender: mpsc::UnboundedSender<SignedMessage<Block>>,
	network: N,
}

impl<Block: BlockT, N: Network> Sink for OutgoingMessages<Block, N> {
	type SinkItem = Message<Block>;
	type SinkError = Error;

	fn start_send(&mut self, msg: Message<Block>) -> StartSend<Message<Block>, Error> {
		// when locals exist, sign messages on import
		if let Some((ref pair, local_id)) = self.locals {
			let encoded = localized_payload(self.round, self.set_id, &msg);
			let signature = pair.sign(&encoded[..]);
			let signed = SignedMessage::<Block> {
				message: msg,
				signature,
				id: local_id,
			};

			// forward to network and to inner sender.
			self.network.send_message(self.round, self.set_id, signed.encode());
			let _ = self.sender.unbounded_send(signed);
		}

		Ok(AsyncSink::Ready)
	}

	fn poll_complete(&mut self) -> Poll<(), Error> { Ok(Async::Ready(())) }

	fn close(&mut self) -> Poll<(), Error> {
		// ignore errors since we allow this inner sender to be closed already.
		match self.sender.close() {
			Ok(Async::NotReady) => Ok(Async::NotReady),
			_ => Ok(Async::Ready(()))
		}
	}
}

impl<Block: BlockT, N: Network> Drop for OutgoingMessages<Block, N> {
	fn drop(&mut self) {
		self.network.drop_messages(self.round, self.set_id);
	}
}

/// A stream for outgoing messages. This signs the messages with the key,
/// if we are an authority.
///
/// A future can push unsigned messages into the sink. They will be automatically
/// broadcast to the network. The returned stream should be combined with other input.
pub(crate) fn outgoing_messages<Block: BlockT, N: Network>(
	round: u64,
	set_id: u64,
	local_key: Option<Arc<ed25519::Pair>>,
	voters: Arc<HashMap<AuthorityId, u64>>,
	network: N,
) -> (
	impl Stream<Item=SignedMessage<Block>,Error=Error>,
	impl Sink<SinkItem=Message<Block>,SinkError=Error>,
) {
	let locals = local_key.and_then(|pair| {
		let public = pair.public();
		let id = AuthorityId(public.0);
		if voters.contains_key(&id) {
			Some((pair, id))
		} else {
			None
		}
	});

	let (tx, rx) = mpsc::unbounded();
	let outgoing = OutgoingMessages::<Block, N> {
		round,
		set_id,
		network,
		locals,
		sender: tx,
	};

	let rx = rx.map_err(move |()| Error::Network(
		format!("Failed to receive on unbounded receiver for round {}", round)
	));

	(rx, outgoing)
}
