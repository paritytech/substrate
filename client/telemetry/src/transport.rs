// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use futures::{
	executor::block_on,
	prelude::*,
	ready,
	task::{Context, Poll},
};
use libp2p::{core::transport::timeout::TransportTimeout, Transport};
use std::{io, pin::Pin, time::Duration};

/// Timeout after which a connection attempt is considered failed. Includes the WebSocket HTTP
/// upgrading.
const CONNECT_TIMEOUT: Duration = Duration::from_secs(20);

pub(crate) fn initialize_transport() -> Result<WsTrans, io::Error> {
	let transport = {
		let inner = block_on(libp2p::dns::DnsConfig::system(libp2p::tcp::TcpConfig::new()))?;
		libp2p::websocket::framed::WsConfig::new(inner).and_then(|connec, _| {
			let connec = connec
				.with(|item| {
					let item = libp2p::websocket::framed::OutgoingData::Binary(item);
					future::ready(Ok::<_, io::Error>(item))
				})
				.try_filter(|item| future::ready(item.is_data()))
				.map_ok(|data| data.into_bytes());
			future::ready(Ok::<_, io::Error>(connec))
		})
	};

	Ok(TransportTimeout::new(
		transport.map(|out, _| {
			let out = out
				.map_err(|err| io::Error::new(io::ErrorKind::Other, err))
				.sink_map_err(|err| io::Error::new(io::ErrorKind::Other, err));
			Box::pin(out) as Pin<Box<_>>
		}),
		CONNECT_TIMEOUT,
	)
	.boxed())
}

/// A trait that implements `Stream` and `Sink`.
pub(crate) trait StreamAndSink<I>: Stream + Sink<I> {}
impl<T: ?Sized + Stream + Sink<I>, I> StreamAndSink<I> for T {}

/// A type alias for the WebSocket transport.
pub(crate) type WsTrans = libp2p::core::transport::Boxed<
	Pin<
		Box<
			dyn StreamAndSink<Vec<u8>, Item = Result<Vec<u8>, io::Error>, Error = io::Error> + Send,
		>,
	>,
>;

/// Wraps around an `AsyncWrite` and implements `Sink`. Guarantees that each item being sent maps
/// to one call of `write`.
#[pin_project::pin_project]
pub(crate) struct StreamSink<T>(#[pin] T, Option<Vec<u8>>);

impl<T> From<T> for StreamSink<T> {
	fn from(inner: T) -> StreamSink<T> {
		StreamSink(inner, None)
	}
}

impl<T: AsyncRead> Stream for StreamSink<T> {
	type Item = Result<Vec<u8>, io::Error>;

	fn poll_next(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
		let this = self.project();
		let mut buf = vec![0; 128];
		match ready!(AsyncRead::poll_read(this.0, cx, &mut buf)) {
			Ok(0) => Poll::Ready(None),
			Ok(n) => {
				buf.truncate(n);
				Poll::Ready(Some(Ok(buf)))
			},
			Err(err) => Poll::Ready(Some(Err(err))),
		}
	}
}

impl<T: AsyncWrite> StreamSink<T> {
	fn poll_flush_buffer(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), io::Error>> {
		let this = self.project();

		if let Some(buffer) = this.1 {
			if ready!(this.0.poll_write(cx, &buffer[..]))? != buffer.len() {
				log::error!(target: "telemetry",
					"Detected some internal buffering happening in the telemetry");
				let err = io::Error::new(io::ErrorKind::Other, "Internal buffering detected");
				return Poll::Ready(Err(err))
			}
		}

		*this.1 = None;
		Poll::Ready(Ok(()))
	}
}

impl<T: AsyncWrite> Sink<Vec<u8>> for StreamSink<T> {
	type Error = io::Error;

	fn poll_ready(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), Self::Error>> {
		ready!(StreamSink::poll_flush_buffer(self, cx))?;
		Poll::Ready(Ok(()))
	}

	fn start_send(self: Pin<&mut Self>, item: Vec<u8>) -> Result<(), Self::Error> {
		let this = self.project();
		debug_assert!(this.1.is_none());
		*this.1 = Some(item);
		Ok(())
	}

	fn poll_flush(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), Self::Error>> {
		ready!(self.as_mut().poll_flush_buffer(cx))?;
		let this = self.project();
		AsyncWrite::poll_flush(this.0, cx)
	}

	fn poll_close(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), Self::Error>> {
		ready!(self.as_mut().poll_flush_buffer(cx))?;
		let this = self.project();
		AsyncWrite::poll_close(this.0, cx)
	}
}
