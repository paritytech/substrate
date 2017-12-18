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
	-> Box<Future<Item=P, Error=I::Error> + Send + 'a>
	where
		P: 'a + Send + Eq + Clone,
		V: 'a + Send + Hash + Eq,
		I: 'a + Send + Stream<Item=LocalizedMessage<P, V>>,
		O: 'a + Send + Sink<SinkItem=Message<P>,SinkError=I::Error>,
		I::Error: Send
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

#[cfg(test)]
mod tests {
	use futures::{Future, Stream, Sink};
	use super::*;

	#[test]
	fn broadcasts_message() {
		let (i_tx, i_rx) = ::futures::sync::mpsc::channel::<LocalizedMessage<usize, usize>>(10);
		let (o_tx, o_rx) = ::futures::sync::mpsc::channel(10);
		let max_faulty = 3;

		let agreement = agree(
			100_000,
			i_rx.map_err(|_| ()),
			o_tx.sink_map_err(|_| ()),
			max_faulty,
		);

		::std::thread::spawn(move || {
			let _i_tx = i_tx;
			let _ = agreement.wait();
		});

		let sent_message = o_rx.wait()
			.next()
			.expect("to have a next item")
			.expect("not to have an error");
		let Message::Prepare(p) = sent_message;

		assert_eq!(p, 100_000);
	}

	#[test]
	fn concludes_on_2f_prepares() {
		let (i_tx, i_rx) = ::futures::sync::mpsc::channel(10);
		let (o_tx, _o_rx) = ::futures::sync::mpsc::channel(10);
		let (timeout_tx, timeout_rx) = ::futures::sync::oneshot::channel();
		let max_faulty = 3;

		let agreement = agree(
			100_000,
			i_rx.map_err(|_| ()),
			o_tx.sink_map_err(|_| ()),
			max_faulty,
		);

		let iter = (0..(max_faulty * 2)).map(|i| {
			LocalizedMessage {
				message: Message::Prepare(100_000),
				sender: i,
			}
		});

		let (_i_tx, _) = i_tx.send_all(::futures::stream::iter_ok(iter)).wait().unwrap();

		::std::thread::spawn(move || {
			::std::thread::sleep(::std::time::Duration::from_secs(5));
			timeout_tx.send(None).unwrap();
		});

		let agreed_value = agreement.map(Some).select(timeout_rx.map_err(|_| ()))
			.wait()
			.map(|(r, _)| r)
			.map_err(|(e, _)| e)
			.expect("not to have an error")
			.expect("not to fail to agree");

		assert_eq!(agreed_value, 100_000);
	}

	#[test]
	fn never_concludes_on_less_than_2f_prepares() {
		let (i_tx, i_rx) = ::futures::sync::mpsc::channel(10);
		let (o_tx, _o_rx) = ::futures::sync::mpsc::channel(10);
		let (timeout_tx, timeout_rx) = ::futures::sync::oneshot::channel();
		let max_faulty = 3;

		let agreement = agree(
			100_000,
			i_rx.map_err(|_| ()),
			o_tx.sink_map_err(|_| ()),
			max_faulty,
		);

		let iter = (1..(max_faulty * 2)).map(|i| {
			LocalizedMessage {
				message: Message::Prepare(100_000),
				sender: i,
			}
		});

		let (_i_tx, _) = i_tx.send_all(::futures::stream::iter_ok(iter)).wait().unwrap();

		::std::thread::spawn(move || {
			::std::thread::sleep(::std::time::Duration::from_millis(250));
			timeout_tx.send(None).unwrap();
		});

		let agreed_value = agreement.map(Some).select(timeout_rx.map_err(|_| ()))
			.wait()
			.map(|(r, _)| r)
			.map_err(|(e, _)| e)
			.expect("not to have an error");

		assert!(agreed_value.is_none());
	}
}
