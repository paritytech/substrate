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

//! BFT Agreement based on a proposal.
//!
//! This is based off of PBFT with an assumption that a proposal is already
//! known by each node. The proposals they have may differ, so the agreement
//! may never complete.

use std::collections::HashSet;
use std::hash::Hash;

use futures::{Future, Stream, Sink};
use futures::future::{ok, loop_fn, Loop};

/// Messages over the proposal.
pub enum Message<P> {
	/// Prepare to vote for proposal P.
	Prepare(P),
}

/// A localized message, including the sender.
pub struct LocalizedMessage<P, V> {
	/// The message received.
	pub message: Message<P>,
	/// The sender of the message
	pub sender: V,
}

/// Reach BFT agreement. Input the local proposal, message input stream, message output stream,
/// and maximum number of faulty participants.
///
/// Messages should only be yielded from the input stream if the sender is authorized
/// to send messages.
///
/// The input stream also may never conclude or the agreement code will panic.
/// Duplicate messages are allowed.
///
/// The output stream assumes that messages will eventually be delivered to all
/// honest participants, either by repropagation, gossip, or some reliable
/// broadcast mechanism.
///
/// This will collect 2f + 1 "prepare" messages. Since this is all within a single
/// view, the commit phase is not necessary.
// TODO: consider cross-view committing?
// TODO: impl future.
pub fn agree<'a, P, I, O, V>(local_proposal: P, input: I, output: O, max_faulty: usize)
	-> Box<Future<Item=P, Error=I::Error> + 'a>
	where
		P: 'a + Eq + Clone,
		V: 'a + Hash + Eq,
		I: 'a + Stream<Item=LocalizedMessage<P, V>>,
		O: 'a + Sink<SinkItem=Message<P>,SinkError=I::Error>,
{
	let prepared = HashSet::new();

	let broadcast_message = output.send(Message::Prepare(local_proposal.clone()));

	let wait_for_prepares = loop_fn((input, prepared), move |(input, mut prepared)| {
		let local_proposal = local_proposal.clone();
		input.into_future().and_then(move |(msg, remainder)| {
			let msg = msg.expect("input stream never concludes; qed");
			let LocalizedMessage { message: Message::Prepare(p), sender } = msg;

			if p == local_proposal {
				prepared.insert(sender);

				// the threshold is 2f + 1, but this node makes up the one.
				if prepared.len() >= max_faulty * 2 {
					return ok(Loop::Break(p))
				}
			}

			ok(Loop::Continue((remainder, prepared)))
		}).map_err(|(e, _)| e)
	});

	Box::new(broadcast_message.and_then(move |_| wait_for_prepares))
}
