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

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use futures::{Future, Stream, Sink};
use futures::future::{ok, loop_fn, Loop};

/// Messages over the proposal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Message<P> {
	/// Prepare to vote for proposal P.
	Prepare(P),
}

/// A localized message, including the sender.
#[derive(Debug, Clone)]
pub struct LocalizedMessage<P, V, S> {
	/// The message received.
	pub message: Message<P>,
	/// The sender of the message
	pub sender: V,
	/// The signature of the message.
	pub signature: S,
}

/// The agreed-upon data.
#[derive(Debug, Clone)]
pub struct Agreed<P, V, S> {
	/// The agreed-upon proposal.
	pub proposal: P,
	/// The justification for the proposal.
	pub justification: Vec<LocalizedMessage<P, V, S>>,
}

/// Check validity and compactness justification set for a proposal.
///
/// Validity checks whether the set of signed messages is enough to justify
/// the agreement of the proposal by the validators.
///
/// Compactness enforces that no extraneous messages are included.
///
/// Provide the proposal, the justification set to check, and a closure for
/// extracting validator IDs from signatures. Should return true only if the
/// signature is valid and the signer was a validator at that time.
pub fn check_justification<P, V, S, C>(
	proposal: P,
	justification: &[LocalizedMessage<P, V, S>],
	max_faulty: usize,
	check_sig: C,
) -> bool
	where
		P: Eq,
		V: Hash + Eq,
		C: Fn(&Message<P>, &S) -> Option<V>
{
	let mut prepared = HashSet::new();

	for message in justification {
		let signer = match check_sig(&message.message, &message.signature) {
			Some(signer) => signer,
			None => return false, // compactness.
		};

		if signer != message.sender { return false }

		match message.message {
			Message::Prepare(ref p) if p == &proposal => {},
			_ => return false,
		};

		// compactness
		if !prepared.insert(signer) { return false }

		if prepared.len() > max_faulty * 2 { return true }
	}

	false
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
// TODO: consider cross-view committing
// TODO: impl future.
pub fn agree<'a, P, V, S, F, I, O>(
	local_proposal: P,
	local_id: V,
	mut sign_local: F,
	input: I,
	output: O,
	max_faulty: usize,
) -> Box<Future<Item=Agreed<P, V, S>, Error=I::Error> + Send + 'a>
	where
		P: 'a + Send + Hash + Eq + Clone,
		V: 'a + Send + Hash + Eq + Clone,
		S: 'a + Send + Eq + Clone,
		F: 'a + Send + FnMut(&Message<P>) -> S,
		I: 'a + Send + Stream<Item=LocalizedMessage<P, V, S>>,
		O: 'a + Send + Sink<SinkItem=LocalizedMessage<P, V, S>,SinkError=I::Error>,
		I::Error: Send
{
	use std::collections::hash_map::Entry;

	let voting_for = HashMap::new();
	let prepared = HashMap::new();

	let local_prepare = {
		let local_prepare = Message::Prepare(local_proposal);
		let local_signature = sign_local(&local_prepare);

		LocalizedMessage {
			message: local_prepare,
			sender: local_id,
			signature: local_signature,
		}
	};

	// broadcast out our local prepare message and shortcut it into our input
	// stream.
	let broadcast_message = output.send(local_prepare.clone());
	let input = ::futures::stream::once(Ok(local_prepare)).chain(input);

	let wait_for_prepares = loop_fn((input, voting_for, prepared), move |(input, mut voting_for, mut prepared)| {
		input.into_future().and_then(move |(msg, remainder)| {
			let msg = msg.expect("input stream never concludes; qed");
			let LocalizedMessage { message: Message::Prepare(p), sender, signature } = msg;

			let is_complete = match voting_for.entry(sender) {
				Entry::Occupied(_) => {
					// TODO: handle double vote.
					false
				}
				Entry::Vacant(vacant) => {
					vacant.insert((p.clone(), signature));
					let n = prepared.entry(p.clone()).or_insert(0);
					*n += 1;
					*n > max_faulty * 2
				}
			};

			if is_complete {
				let justification = voting_for.into_iter().filter_map(|(v, (x, s))| {
					if x == p {
						Some(LocalizedMessage {
							message: Message::Prepare(x),
							sender: v,
							signature: s,
						})
					} else {
						None
					}
				}).collect();

				ok(Loop::Break(Agreed {
					justification,
					proposal: p,
				}))
			} else {
				ok(Loop::Continue((remainder, voting_for, prepared)))
			}

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
		let (i_tx, i_rx) = ::futures::sync::mpsc::channel::<LocalizedMessage<usize, usize, bool>>(10);
		let (o_tx, o_rx) = ::futures::sync::mpsc::channel(10);
		let max_faulty = 3;

		let agreement = agree(
			100_000,
			255,
			|_msg| true,
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

		let Message::Prepare(p) = sent_message.message;
		assert_eq!(p, 100_000);
		assert_eq!(sent_message.sender, 255);
	}

	#[test]
	fn concludes_on_2f_prepares_for_local_proposal() {
		let (i_tx, i_rx) = ::futures::sync::mpsc::channel(10);
		let (o_tx, _o_rx) = ::futures::sync::mpsc::channel(10);
		let (timeout_tx, timeout_rx) = ::futures::sync::oneshot::channel();
		let max_faulty = 3;

		let agreement = agree(
			100_000,
			255,
			|msg| (msg.clone(), 255),
			i_rx.map_err(|_| ()),
			o_tx.sink_map_err(|_| ()),
			max_faulty,
		);

		let iter = (0..(max_faulty * 2)).map(|i| {
			LocalizedMessage {
				message: Message::Prepare(100_000),
				sender: i,
				signature: (Message::Prepare(100_000), i),
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

		assert_eq!(agreed_value.proposal, 100_000);
		assert!(check_justification(
			agreed_value.proposal,
			&agreed_value.justification,
			max_faulty,
			|msg, sig| if msg == &sig.0 { Some(sig.1) } else { None }
		));
	}

	#[test]
	fn concludes_on_2f_plus_one_prepares_for_alternate_proposal() {
		let (i_tx, i_rx) = ::futures::sync::mpsc::channel(10);
		let (o_tx, _o_rx) = ::futures::sync::mpsc::channel(10);
		let (timeout_tx, timeout_rx) = ::futures::sync::oneshot::channel();
		let max_faulty = 3;

		let agreement = agree(
			100_000,
			255,
			|msg| (msg.clone(), 255),
			i_rx.map_err(|_| ()),
			o_tx.sink_map_err(|_| ()),
			max_faulty,
		);

		let iter = (0..(max_faulty * 2 + 1)).map(|i| {
			LocalizedMessage {
				message: Message::Prepare(100_001),
				sender: i,
				signature: (Message::Prepare(100_001), i),
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

		assert_eq!(agreed_value.proposal, 100_001);
		assert!(check_justification(
			agreed_value.proposal,
			&agreed_value.justification,
			max_faulty,
			|msg, sig| if msg == &sig.0 { Some(sig.1) } else { None }
		));
	}

	#[test]
	fn never_concludes_on_less_than_2f_prepares_for_local() {
		let (i_tx, i_rx) = ::futures::sync::mpsc::channel(10);
		let (o_tx, _o_rx) = ::futures::sync::mpsc::channel(10);
		let (timeout_tx, timeout_rx) = ::futures::sync::oneshot::channel();
		let max_faulty = 3;

		let agreement = agree(
			100_000,
			255,
			|_msg| true,
			i_rx.map_err(|_| ()),
			o_tx.sink_map_err(|_| ()),
			max_faulty,
		);

		let iter = (1..(max_faulty * 2)).map(|i| {
			LocalizedMessage {
				message: Message::Prepare(100_000),
				sender: i,
				signature: true,
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

	#[test]
	fn never_concludes_on_less_than_2f_plus_one_prepares_for_alternate() {
		let (i_tx, i_rx) = ::futures::sync::mpsc::channel(10);
		let (o_tx, _o_rx) = ::futures::sync::mpsc::channel(10);
		let (timeout_tx, timeout_rx) = ::futures::sync::oneshot::channel();
		let max_faulty = 3;

		let agreement = agree(
			100_000,
			255,
			|_msg| true,
			i_rx.map_err(|_| ()),
			o_tx.sink_map_err(|_| ()),
			max_faulty,
		);

		let iter = (1..(max_faulty * 2 + 1)).map(|i| {
			LocalizedMessage {
				message: Message::Prepare(100_001),
				sender: i,
				signature: true,
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
