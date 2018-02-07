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

//! Round-robin buffer for incoming messages.
//!
//! This takes batches of messages associated with a sender as input,
//! and yields messages in a fair order by sender.

use std::collections::{Bound, BTreeMap, VecDeque};

use futures::prelude::*;
use futures::stream::Fuse;

/// Implementation of the round-robin buffer for incoming messages.
#[derive(Debug)]
pub struct RoundRobinBuffer<V: Ord + Eq, S, M> {
	buffer: BTreeMap<V, VecDeque<M>>,
	last_processed_from: Option<V>,
	stored_messages: usize,
	max_messages: usize,
	inner: Fuse<S>,
}

impl<V: Ord + Eq + Clone, S: Stream, M> RoundRobinBuffer<V, S, M> {
	/// Create a new round-robin buffer which holds up to a maximum
	/// amount of messages.
	pub fn new(stream: S, buffer_size: usize) -> Self {
		RoundRobinBuffer {
			buffer: BTreeMap::new(),
			last_processed_from: None,
			stored_messages: 0,
			max_messages: buffer_size,
			inner: stream.fuse(),
		}
	}
}

impl<V: Ord + Eq + Clone, S, M> RoundRobinBuffer<V, S, M> {
	fn next_message(&mut self) -> Option<(V, M)> {
		if self.stored_messages == 0 {
			return None
		}

		// first pick up from the last authority we processed a message from
		let mut next = {
			let lower_bound = match self.last_processed_from {
				None => Bound::Unbounded,
				Some(ref x) => Bound::Excluded(x.clone()),
			};

			self.buffer.range_mut((lower_bound, Bound::Unbounded))
				.filter_map(|(k, v)| v.pop_front().map(|v| (k.clone(), v)))
				.next()
		};

		// but wrap around to the beginning again if we got nothing.
		if next.is_none() {
			next = self.buffer.iter_mut()
				.filter_map(|(k, v)| v.pop_front().map(|v| (k.clone(), v)))
				.next();
		}

		if let Some((ref authority, _)) = next {
			self.stored_messages -= 1;
			self.last_processed_from = Some(authority.clone());
		}

		next
	}

	// import messages, discarding when the buffer is full.
	fn import_messages(&mut self, sender: V, messages: Vec<M>) {
		let space_remaining = self.max_messages - self.stored_messages;
		self.stored_messages += ::std::cmp::min(space_remaining, messages.len());

		let v = self.buffer.entry(sender).or_insert_with(VecDeque::new);
		v.extend(messages.into_iter().take(space_remaining));
	}
}

impl<V: Ord + Eq + Clone, S, M> Stream for RoundRobinBuffer<V, S, M>
	where S: Stream<Item=(V, Vec<M>)>
{
	type Item = (V, M);
	type Error = S::Error;

	fn poll(&mut self) -> Poll<Option<Self::Item>, S::Error> {
		loop {
			match self.inner.poll()? {
				Async::NotReady | Async::Ready(None) => break,
				Async::Ready(Some((sender, msgs))) => self.import_messages(sender, msgs),
			}
		}

		let done = self.inner.is_done();
		Ok(match self.next_message() {
			Some(msg) => Async::Ready(Some(msg)),
			None => if done { Async::Ready(None) } else { Async::NotReady },
		})
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use futures::stream::{self, Stream};

	#[derive(Debug, PartialEq, Eq)]
	struct UncheckedMessage { data: Vec<u8> }

	#[test]
	fn is_fair_and_wraps_around() {
		let stream = stream::iter_ok(vec![
			(1, vec![
				UncheckedMessage { data: vec![1, 3, 5] },
				UncheckedMessage { data: vec![3, 5, 7] },
				UncheckedMessage { data: vec![5, 7, 9] },
			]),
			(2, vec![
				UncheckedMessage { data: vec![2, 4, 6] },
				UncheckedMessage { data: vec![4, 6, 8] },
				UncheckedMessage { data: vec![6, 8, 10] },
			]),
		]);

		let round_robin = RoundRobinBuffer::new(stream, 100);
		let output = round_robin.wait().collect::<Result<Vec<_>, ()>>().unwrap();

		assert_eq!(output, vec![
			(1, UncheckedMessage { data: vec![1, 3, 5] }),
			(2, UncheckedMessage { data: vec![2, 4, 6] }),
			(1, UncheckedMessage { data: vec![3, 5, 7] }),

			(2, UncheckedMessage { data: vec![4, 6, 8] }),
			(1, UncheckedMessage { data: vec![5, 7, 9] }),
			(2, UncheckedMessage { data: vec![6, 8, 10] }),
		]);
	}

	#[test]
	fn discards_when_full() {
		let stream = stream::iter_ok(vec![
			(1, (0..200).map(|i| UncheckedMessage { data: vec![i] }).collect())
		]);

		let round_robin = RoundRobinBuffer::new(stream, 100);
		let output = round_robin.wait().collect::<Result<Vec<_>, ()>>().unwrap();

		assert_eq!(output.len(), 100);
	}
}
