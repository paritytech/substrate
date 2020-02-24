// Copyright 2018-2020 Parity Technologies (UK) Ltd.
//
// Permission is hereby granted, free of charge, to any person obtaining a
// copy of this software and associated documentation files (the "Software"),
// to deal in the Software without restriction, including without limitation
// the rights to use, copy, modify, merge, publish, distribute, sublicense,
// and/or sell copies of the Software, and to permit persons to whom the
// Software is furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
// OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
// DEALINGS IN THE SOFTWARE.

use futures::prelude::*;
use libp2p::core::upgrade::{InboundUpgrade, ProtocolName, UpgradeInfo};
use std::{iter::FromIterator, pin::Pin, task::{Context, Poll}, vec};

// TODO: move this to libp2p => https://github.com/libp2p/rust-libp2p/issues/1445

/// Upgrade that combines multiple upgrades of the same type into one. Supports all the protocols
/// supported by either sub-upgrade.
#[derive(Debug, Clone)]
pub struct UpgradeCollec<T>(pub Vec<T>);

impl<T> From<Vec<T>> for UpgradeCollec<T> {
	fn from(list: Vec<T>) -> Self {
		UpgradeCollec(list)
	}
}

impl<T> FromIterator<T> for UpgradeCollec<T> {
	fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
		UpgradeCollec(iter.into_iter().collect())
	}
}

impl<T: UpgradeInfo> UpgradeInfo for UpgradeCollec<T> {
	type Info = ProtoNameWithUsize<T::Info>;
	type InfoIter = vec::IntoIter<Self::Info>;

	fn protocol_info(&self) -> Self::InfoIter {
		self.0.iter().enumerate()
			.flat_map(|(n, p)|
				p.protocol_info().into_iter().map(move |i| ProtoNameWithUsize(i, n)))
			.collect::<Vec<_>>()
			.into_iter()
	}
}

impl<T, C> InboundUpgrade<C> for UpgradeCollec<T>
where
	T: InboundUpgrade<C>,
{
	type Output = (T::Output, usize);
	type Error = (T::Error, usize);
	type Future = FutWithUsize<T::Future>;

	fn upgrade_inbound(mut self, sock: C, info: Self::Info) -> Self::Future {
		let fut = self.0.remove(info.1).upgrade_inbound(sock, info.0);
		FutWithUsize(fut, info.1)
	}
}

/// Groups a `ProtocolName` with a `usize`.
#[derive(Debug, Clone)]
pub struct ProtoNameWithUsize<T>(T, usize);

impl<T: ProtocolName> ProtocolName for ProtoNameWithUsize<T> {
	fn protocol_name(&self) -> &[u8] {
		self.0.protocol_name()
	}
}

/// Equivalent to `fut.map_ok(|v| (v, num)).map_err(|e| (e, num))`, where `fut` and `num` are
/// the two fields of this struct.
#[pin_project::pin_project]
pub struct FutWithUsize<T>(#[pin] T, usize);

impl<T: Future<Output = Result<O, E>>, O, E> Future for FutWithUsize<T> {
	type Output = Result<(O, usize), (E, usize)>;

	fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		let this = self.project();
		match Future::poll(this.0, cx) {
			Poll::Ready(Ok(v)) => Poll::Ready(Ok((v, *this.1))),
			Poll::Ready(Err(e)) => Poll::Ready(Err((e, *this.1))),
			Poll::Pending => Poll::Pending,
		}
	}
}
