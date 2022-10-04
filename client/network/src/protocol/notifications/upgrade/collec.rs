// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

use futures::prelude::*;
use libp2p::core::upgrade::{InboundUpgrade, ProtocolName, UpgradeInfo};
use std::{
	iter::FromIterator,
	pin::Pin,
	task::{Context, Poll},
	vec,
};

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
		self.0
			.iter()
			.enumerate()
			.flat_map(|(n, p)| p.protocol_info().into_iter().map(move |i| ProtoNameWithUsize(i, n)))
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
