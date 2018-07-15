// Copyright 2018 Parity Technologies (UK) Ltd.
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
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.?

use futures::{future, Future, stream, Stream, sync::mpsc};
use std::io::Error as IoError;
use std::time::Instant;
use tokio_core::reactor::{Handle, Timeout};

/// Builds the timeouts system.
///
/// The `timeouts_rx` should be a stream receiving newly-created timeout
/// requests. Returns a stream that produces items as their timeout elapses.
/// `T` can be anything you want, as it is transparently passed from the input
/// to the output.
pub fn build_timeouts_stream<T>(
	core: Handle,
	timeouts_rx: mpsc::UnboundedReceiver<(Instant, T)>
) -> impl Stream<Item = T, Error = IoError> {
	let next_timeout = next_in_timeouts_stream(timeouts_rx);

	// The `unfold` function is essentially a loop turned into a stream. The
	// first parameter is the initial state, and the closure returns the new
	// state and an item.
	stream::unfold(vec![future::Either::A(next_timeout)], move |timeouts| {
		// `timeouts` is a `Vec` of futures that produce an `Out`.

		let core = core.clone();

		// `select_ok` panics if `timeouts` is empty anyway.
		if timeouts.is_empty() {
			return None
		}

		Some(future::select_ok(timeouts.into_iter())
			.and_then(move |(item, mut timeouts)|
				match item {
					Out::NewTimeout((Some((at, item)), next_timeouts)) => {
						// Received a new timeout request on the channel.
						let next_timeout = next_in_timeouts_stream(next_timeouts);
						let timeout = Timeout::new_at(at, &core)?
							.map(move |()| Out::Timeout(item));
						timeouts.push(future::Either::B(timeout));
						timeouts.push(future::Either::A(next_timeout));
						Ok((None, timeouts))
					},
					Out::NewTimeout((None, _)) =>
						// The channel has been closed.
						Ok((None, timeouts)),
					Out::Timeout(item) =>
						// A timeout has happened.
						Ok((Some(item), timeouts)),
				}
			)
		)
	}).filter_map(|item| item)
}

/// Local enum representing the output of the selection.
enum Out<A, B> {
	NewTimeout(A),
	Timeout(B),
}

/// Convenience function that calls `.into_future()` on the timeouts stream,
/// and applies some modifiers.
/// This function is necessary. Otherwise if we copy-paste its content we run
/// into errors because the type of the copy-pasted closures differs.
fn next_in_timeouts_stream<T, B>(stream: mpsc::UnboundedReceiver<T>)
	-> impl Future<Item = Out<(Option<T>, mpsc::UnboundedReceiver<T>), B>, Error = IoError> {
	stream
		.into_future()
		.map(Out::NewTimeout)
		.map_err(|_| unreachable!("an UnboundedReceiver can never error"))
}
