// Copyright 2018 Parity Technologies (UK) Ltd.
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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.?

use futures::{Async, future, Future, Poll, stream, Stream, sync::mpsc};
use std::io::{Error as IoError, ErrorKind as IoErrorKind};
use std::marker::PhantomData;
use std::time::{Duration, Instant};
use tokio_timer::{self, Delay};

/// Builds the timeouts system.
///
/// The `timeouts_rx` should be a stream receiving newly-created timeout
/// requests. Returns a stream that produces items as their timeout elapses.
/// `T` can be anything you want, as it is transparently passed from the input
/// to the output. Timeouts continue to fire forever, as there is no way to
/// unregister them.
pub fn build_timeouts_stream<'a, T>(
	timeouts_rx: mpsc::UnboundedReceiver<(Duration, T)>
) -> Box<Stream<Item = T, Error = IoError> + 'a>
	where T: Clone + 'a {
	let next_timeout = next_in_timeouts_stream(timeouts_rx);

	// The `unfold` function is essentially a loop turned into a stream. The
	// first parameter is the initial state, and the closure returns the new
	// state and an item.
	let stream = stream::unfold(vec![future::Either::A(next_timeout)], move |timeouts| {
		// `timeouts` is a `Vec` of futures that produce an `Out`.

		// `select_ok` panics if `timeouts` is empty anyway.
		if timeouts.is_empty() {
			return None
		}

		Some(future::select_ok(timeouts.into_iter())
			.and_then(move |(item, mut timeouts)|
				match item {
					Out::NewTimeout((Some((duration, item)), next_timeouts)) => {
						// Received a new timeout request on the channel.
						let next_timeout = next_in_timeouts_stream(next_timeouts);
						let timeout = Delay::new(Instant::now() + duration);
						let timeout = TimeoutWrapper(timeout, duration, Some(item), PhantomData);
						timeouts.push(future::Either::B(timeout));
						timeouts.push(future::Either::A(next_timeout));
						Ok((None, timeouts))
					},
					Out::NewTimeout((None, _)) =>
						// The channel has been closed.
						Ok((None, timeouts)),
					Out::Timeout(duration, item) => {
						// A timeout has happened.
						let returned = item.clone();
						let timeout = Delay::new(Instant::now() + duration);
						let timeout = TimeoutWrapper(timeout, duration, Some(item), PhantomData);
						timeouts.push(future::Either::B(timeout));
						Ok((Some(returned), timeouts))
					},
				}
			)
		)
	}).filter_map(|item| item);

	// Note that we use a `Box` in order to speed up compilation time.
	Box::new(stream) as Box<Stream<Item = _, Error = _>>
}

/// Local enum representing the output of the selection.
enum Out<A, B> {
	NewTimeout(A),
	Timeout(Duration, B),
}

/// Convenience function that calls `.into_future()` on the timeouts stream,
/// and applies some modifiers.
/// This function is necessary. Otherwise if we copy-paste its content we run
/// into errors because the type of the copy-pasted closures differs.
fn next_in_timeouts_stream<T, B>(
	stream: mpsc::UnboundedReceiver<T>
) -> impl Future<Item = Out<(Option<T>, mpsc::UnboundedReceiver<T>), B>, Error = IoError> {
	stream
		.into_future()
		.map(Out::NewTimeout)
		.map_err(|_| unreachable!("an UnboundedReceiver can never error"))
}

/// Does the equivalent to `future.map(move |()| (duration, item)).map_err(|err| to_io_err(err))`.
struct TimeoutWrapper<A, F, T>(F, Duration, Option<T>, PhantomData<A>);
impl<A, F, T> Future for TimeoutWrapper<A, F, T>
	where F: Future<Item = (), Error = tokio_timer::Error> {
	type Item = Out<A, T>;
	type Error = IoError;

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
		match self.0.poll() {
			Ok(Async::Ready(())) => (),
			Ok(Async::NotReady) => return Ok(Async::NotReady),
			Err(err) => return Err(IoError::new(IoErrorKind::Other, err.to_string())),
		}

		let out = Out::Timeout(self.1, self.2.take().expect("poll() called again after success"));
		Ok(Async::Ready(out))
	}
}
