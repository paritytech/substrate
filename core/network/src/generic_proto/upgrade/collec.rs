// Copyright 2018 Parity Technologies (UK) Ltd.
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
use libp2p::core::{
	upgrade::{InboundUpgrade, OutboundUpgrade, UpgradeInfo},
	Negotiated
};
use std::{iter::FromIterator, vec};

// TODO: move this to libp2p

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
	type Info = T::Info;
	type InfoIter = vec::IntoIter<T::Info>;

	fn protocol_info(&self) -> Self::InfoIter {
		self.0.iter().flat_map(|p| p.protocol_info()).collect::<Vec<_>>().into_iter()
	}
}

impl<T, C> InboundUpgrade<C> for UpgradeCollec<T>
where
	T: InboundUpgrade<C>,
{
	type Output = (T::Output, usize);
	type Error = (T::Error, usize);
	type Future = FutWithUsize<T::Future>;

	fn upgrade_inbound(self, sock: Negotiated<C>, info: Self::Info) -> Self::Future {
		unimplemented!()
	}
}

impl<T, C> OutboundUpgrade<C> for UpgradeCollec<T>
where
	T: OutboundUpgrade<C>,
{
	type Output = (T::Output, usize);
	type Error = (T::Error, usize);
	type Future = FutWithUsize<T::Future>;

	fn upgrade_outbound(self, sock: Negotiated<C>, info: Self::Info) -> Self::Future {
		unimplemented!()
	}
}

/// Equivalent to `fut.map(|v| (v, num))`, where `fut` and `num` are the two fields of this
/// struct.
pub struct FutWithUsize<T>(T, usize);

impl<T: Future> Future for FutWithUsize<T> {
	type Item = (T::Item, usize);
	type Error = (T::Error, usize);

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
		match self.0.poll() {
			Ok(Async::NotReady) => Ok(Async::NotReady),
			Ok(Async::Ready(v)) => Ok(Async::Ready((v, self.1))),
			Err(err) => Err((err, self.1)),
		}
	}
}
