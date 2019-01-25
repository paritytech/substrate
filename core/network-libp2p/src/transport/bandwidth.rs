// Copyright 2019 Parity Technologies (UK) Ltd.
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

use futures::{prelude::*, try_ready};
use lazy_static::lazy_static;
use libp2p::{Multiaddr, core::Transport, core::transport::TransportError};
use parking_lot::Mutex;
use smallvec::{smallvec, SmallVec};
use std::{io, io::Read, io::Write, sync::Arc, time::Instant};

/// Wraps around a `Transport` and logs the bandwidth that goes through all the opened connections.
#[derive(Clone)]
pub struct BandwidthLogging<TInner> {
	inner: TInner,
	sinks: Arc<BandwidthSinks>,
}

impl<TInner> BandwidthLogging<TInner> {
	/// Creates a new `BandwidthLogging` around the transport.
	#[inline]
	pub fn new(inner: TInner, period_seconds: u32) -> (Self, Arc<BandwidthSinks>) {
		let sink = Arc::new(BandwidthSinks {
			download: Mutex::new(BandwidthSink::new(period_seconds)),
			upload: Mutex::new(BandwidthSink::new(period_seconds)),
		});

		let trans = BandwidthLogging {
			inner,
			sinks: sink.clone(),
		};

		(trans, sink)
	}
}

impl<TInner> Transport for BandwidthLogging<TInner>
where
	TInner: Transport,
{
	type Output = BandwidthConnecLogging<TInner::Output>;
	type Error = TInner::Error;
	type Listener = BandwidthListener<TInner::Listener>;
	type ListenerUpgrade = BandwidthFuture<TInner::ListenerUpgrade>;
	type Dial = BandwidthFuture<TInner::Dial>;

	fn listen_on(self, addr: Multiaddr) -> Result<(Self::Listener, Multiaddr), TransportError<Self::Error>> {
		let sinks = self.sinks;
		self.inner
			.listen_on(addr)
			.map(|(inner, new_addr)| (BandwidthListener { inner, sinks }, new_addr))
	}

	fn dial(self, addr: Multiaddr) -> Result<Self::Dial, TransportError<Self::Error>> {
		let sinks = self.sinks;
		self.inner
			.dial(addr)
			.map(move |fut| BandwidthFuture {
				inner: fut,
				sinks,
			})
	}

	fn nat_traversal(&self, server: &Multiaddr, observed: &Multiaddr) -> Option<Multiaddr> {
		self.inner.nat_traversal(server, observed)
	}
}

/// Wraps around a `Stream` that produces connections. Wraps each connection around a bandwidth
/// counter.
pub struct BandwidthListener<TInner> {
	inner: TInner,
	sinks: Arc<BandwidthSinks>,
}

impl<TInner, TConn> Stream for BandwidthListener<TInner>
where TInner: Stream<Item = (TConn, Multiaddr)>,
{
	type Item = (BandwidthFuture<TConn>, Multiaddr);
	type Error = TInner::Error;

	fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
		let (inner, addr) = match try_ready!(self.inner.poll()) {
			Some(v) => v,
			None => return Ok(Async::Ready(None))
		};

		let fut = BandwidthFuture {
			inner,
			sinks: self.sinks.clone(),
		};

		Ok(Async::Ready(Some((fut, addr))))
	}
}

/// Wraps around a `Future` that produces a connection. Wraps the connection around a bandwidth
/// counter.
pub struct BandwidthFuture<TInner> {
	inner: TInner,
	sinks: Arc<BandwidthSinks>,
}

impl<TInner> Future for BandwidthFuture<TInner>
	where TInner: Future,
{
	type Item = BandwidthConnecLogging<TInner::Item>;
	type Error = TInner::Error;

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
		let inner = try_ready!(self.inner.poll());
		Ok(Async::Ready(BandwidthConnecLogging {
			inner,
			sinks: self.sinks.clone(),
		}))
	}
}

/// Allows obtaining the average bandwidth of the connections created from a `BandwidthLogging`.
pub struct BandwidthSinks {
	download: Mutex<BandwidthSink>,
	upload: Mutex<BandwidthSink>,
}

impl BandwidthSinks {
	/// Returns the average number of bytes that have been downloaded in the period.
	#[inline]
	pub fn average_download_per_sec(&self) -> u64 {
		self.download.lock().get()
	}

	/// Returns the average number of bytes that have been uploaded in the period.
	#[inline]
	pub fn average_upload_per_sec(&self) -> u64 {
		self.upload.lock().get()
	}
}

/// Wraps around an `AsyncRead + AsyncWrite` and logs the bandwidth that goes through it.
pub struct BandwidthConnecLogging<TInner> {
	inner: TInner,
	sinks: Arc<BandwidthSinks>,
}

impl<TInner> Read for BandwidthConnecLogging<TInner>
	where TInner: Read
{
	#[inline]
	fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
		let num_bytes = self.inner.read(buf)?;
		self.sinks.download.lock().inject(num_bytes);
		Ok(num_bytes)
	}
}

impl<TInner> tokio_io::AsyncRead for BandwidthConnecLogging<TInner>
	where TInner: tokio_io::AsyncRead
{
}

impl<TInner> Write for BandwidthConnecLogging<TInner>
	where TInner: Write
{
	#[inline]
	fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
		let num_bytes = self.inner.write(buf)?;
		self.sinks.upload.lock().inject(num_bytes);
		Ok(num_bytes)
	}

	#[inline]
	fn flush(&mut self) -> io::Result<()> {
		self.inner.flush()
	}
}

impl<TInner> tokio_io::AsyncWrite for BandwidthConnecLogging<TInner>
	where TInner: tokio_io::AsyncWrite
{
	#[inline]
	fn shutdown(&mut self) -> Poll<(), io::Error> {
		self.inner.shutdown()
	}
}

/// Returns the number of seconds that have elapsed between an arbitrary EPOCH and now.
#[inline]
fn current_second() -> u32 {
	lazy_static! {
		static ref EPOCH: Instant = Instant::now();
	}

	EPOCH.elapsed().as_secs() as u32
}

/// Structure that calculates the average bandwidth over the last few seconds.
///
/// If you want to calculate for example both download and upload bandwidths, create two different
/// objects.
struct BandwidthSink {
	/// Bytes sent over the past seconds. Contains `rolling_seconds + 1` elements. Only the first
	/// `rolling_seconds` elements are taken into account for the average, while the last element
	/// is the element to be inserted later.
	bytes: SmallVec<[u64; 8]>,
	/// Number of seconds between `EPOCH` and the moment we have last updated `bytes`.
	latest_update: u32,
	/// Number of seconds. Configured at initialization and never modified.
	rolling_seconds: u32,
}

impl BandwidthSink {
	/// Initializes a `BandwidthSink`.
	fn new(seconds: u32) -> Self {
		BandwidthSink {
			bytes: smallvec![0; seconds as usize + 1],
			latest_update: current_second(),
			rolling_seconds: seconds,
		}
	}

	/// Returns the number of bytes over the last few seconds. The number of seconds is the value
	/// configured at initialization.
	fn get(&mut self) -> u64 {
		self.update();
		self.bytes.iter()
			.take(self.rolling_seconds.saturating_sub(1) as usize)
			.fold(0u64, |a, &b| a.saturating_add(b)) / u64::from(self.rolling_seconds)
	}

	/// Notifies the `BandwidthSink` that a certain number of bytes have been transmitted at this
	/// moment.
	fn inject(&mut self, bytes: usize) {
		self.update();
		if let Some(last) = self.bytes.last_mut() {
			*last = last.saturating_add(bytes as u64);
		}
	}

	/// Updates the state of the `BandwidthSink` so that the last element of `bytes` contains the
	/// current second.
	fn update(&mut self) {
		let current_second = current_second();
		for _ in self.latest_update .. current_second {
			self.bytes.remove(0);
			self.bytes.push(0);
		}

		self.latest_update = current_second;
	}
}
