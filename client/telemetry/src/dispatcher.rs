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

use crate::node::{Infallible, Node};
use crate::transport::WsTrans;
use futures::prelude::*;
use libp2p::Multiaddr;
use std::collections::HashMap;
use std::iter::FromIterator;
use std::pin::Pin;
use std::task::{Context, Poll};

#[derive(Debug)]
pub(crate) struct Dispatcher {
	pool: HashMap<Multiaddr, Node<WsTrans>>,
	item: Option<(Multiaddr, String)>,
	flush_node: Option<Multiaddr>,
}

impl FromIterator<(Multiaddr, Node<WsTrans>)> for Dispatcher {
	fn from_iter<I: IntoIterator<Item = (Multiaddr, Node<WsTrans>)>>(iter: I) -> Self {
		let pool: HashMap<_, _> = FromIterator::from_iter(iter);
		Dispatcher {
			pool,
			item: None,
			flush_node: None,
		}
	}
}

impl Dispatcher {
	fn try_empty_buffer(
		mut self: Pin<&mut Self>,
		cx: &mut Context<'_>,
	) -> Poll<Result<(), Infallible>> {
		if let Some(addr) = self.flush_node.take() {
			let node = self
				.pool
				.get_mut(&addr)
				.expect("we added the address ourselves; qed");
			match node.poll_flush_unpin(cx) {
				Poll::Ready(Ok(())) => {}
				Poll::Ready(Err(x)) => match x {},
				Poll::Pending => {
					self.flush_node = Some(addr);
					return Poll::Pending;
				}
			}
		}

		if let Some((addr, message)) = self.item.take() {
			let node = if let Some(node) = self.pool.get_mut(&addr) {
				node
			} else {
				log::error!(
					target: "telemetry",
					"Received message for unknown node ({}). This is a bug. Message sent: {}",
					addr,
					message,
				);
				return Poll::Ready(Ok(()));
			};

			match node.poll_ready_unpin(cx) {
				Poll::Ready(Ok(())) => {}
				Poll::Ready(Err(x)) => match x {},
				Poll::Pending => {
					self.item = Some((addr, message));
					return Poll::Pending;
				}
			}

			match node.start_send_unpin(message) {
				Ok(()) => {}
				Err(x) => match x {},
			}

			match node.poll_flush_unpin(cx) {
				Poll::Ready(Ok(())) => {}
				Poll::Ready(Err(x)) => match x {},
				Poll::Pending => {
					self.flush_node = Some(addr);
					return Poll::Pending;
				}
			}
		}

		Poll::Ready(Ok(()))
	}
}

impl Sink<(Multiaddr, String)> for Dispatcher {
	type Error = Infallible;

	fn poll_ready(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), Self::Error>> {
		self.try_empty_buffer(cx)
	}

	fn start_send(mut self: Pin<&mut Self>, item: (Multiaddr, String)) -> Result<(), Self::Error> {
		let overrun = self.item.replace(item).is_some();

		if overrun {
			log::error!(
				target: "telemetry",
				"Received another message while the previous one has not finished processing. \
				This is a bug",
			);
		}

		Ok(())
	}

	fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
		self.try_empty_buffer(cx)
	}

	fn poll_close(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
		let mut new_pool = HashMap::with_capacity(self.pool.len());

		for (addr, mut node) in self.pool.drain() {
			match node.poll_close_unpin(cx) {
				Poll::Ready(Ok(())) => {}
				Poll::Ready(Err(x)) => match x {},
				Poll::Pending => {
					new_pool.insert(addr, node);
				}
			}
		}

		let _ = std::mem::replace(&mut self.pool, new_pool);

		if self.pool.is_empty() {
			Poll::Ready(Ok(()))
		} else {
			Poll::Pending
		}
	}
}
