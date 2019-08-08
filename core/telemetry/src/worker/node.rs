// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Contains the `Node` struct, which handles communications with a single telemetry endpoint.

use bytes::BytesMut;
use futures::{prelude::*, compat::{Future01CompatExt as _, Compat01As03}};
use futures_timer::Delay;
use libp2p::Multiaddr;
use libp2p::core::transport::Transport;
use log::{trace, debug, warn, error};
use rand::Rng as _;
use std::{collections::VecDeque, fmt, mem, pin::Pin, task::Context, task::Poll, time::Duration};

/// Maximum number of pending telemetry messages.
const MAX_PENDING: usize = 10;

/// Handler for a single telemetry node.
pub struct Node<TTrans: Transport> {
	/// Address of the node.
	addr: Multiaddr,
	/// State of the connection.
	socket: NodeSocket<TTrans>,
	/// Transport used to establish new connections.
	transport: TTrans,
}

enum NodeSocket<TTrans: Transport> {
	/// We're connected to the node. This is the normal state.
	Connected(NodeSocketConnected<TTrans>),
	/// We are currently dialing the node.
	Dialing(Compat01As03<TTrans::Dial>),
	/// A new connection should be started as soon as possible.
	ReconnectNow,
	/// Waiting before attempting to dial again.
	WaitingReconnect(Delay),
	/// Temporary transition state.
	Poisoned,
}

struct NodeSocketConnected<TTrans: Transport> {
	/// Where to send data.
	sink: TTrans::Output,
	/// Queue of packets to send.
	pending: VecDeque<BytesMut>,
	/// If true, we need to flush the sink.
	need_flush: bool,
}

/// Event that can happen with this node.
#[derive(Debug)]
pub enum NodeEvent<TSinkErr> {
	/// We are now connected to this node.
	Connected,
	/// We are now disconnected from this node.
	Disconnected(TSinkErr),
}

impl<TTrans: Transport> Node<TTrans> {
	/// Builds a new node handler.
	pub fn new(transport: TTrans, addr: Multiaddr) -> Self {
		Node {
			addr,
			socket: NodeSocket::ReconnectNow,
			transport,
		}
	}

	/// Returns the address that was passed to `new`.
	pub fn addr(&self) -> &Multiaddr {
		&self.addr
	}
}

impl<TTrans: Transport, TSinkErr> Node<TTrans>
where TTrans: Clone + Unpin, TTrans::Dial: Unpin,
	TTrans::Output: Sink<BytesMut, Error = TSinkErr>
		+ Stream<Item=Result<BytesMut, TSinkErr>>
		+ Unpin,
	TSinkErr: fmt::Debug
{
	/// Sends a WebSocket frame to the node. Returns an error if we are not connected to the node.
	///
	/// After calling this method, you should call `poll` in order for it to be properly processed.
	pub fn send_message(&mut self, payload: Vec<u8>) -> Result<(), ()> {
		if let NodeSocket::Connected(NodeSocketConnected { pending, .. }) = &mut self.socket {
			if pending.len() <= MAX_PENDING {
				trace!(target: "telemetry", "Adding log entry to queue for {:?}", self.addr);
				pending.push_back(payload.into());
				Ok(())
			} else {
				warn!(target: "telemetry", "Rejected log entry because queue is full for {:?}",
					self.addr);
				Err(())
			}
		} else {
			Err(())
		}
	}

	/// Polls the node for updates. Must be performed regularly.
	pub fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<NodeEvent<TSinkErr>> {
		let mut socket = mem::replace(&mut self.socket, NodeSocket::Poisoned);
		self.socket = loop {
			match socket {
				NodeSocket::Connected(mut conn) =>
					match NodeSocketConnected::poll(Pin::new(&mut conn), cx, &self.addr) {
						Poll::Ready(Ok(v)) => match v {}
						Poll::Pending => break NodeSocket::Connected(conn),
						Poll::Ready(Err(err)) => {
							warn!(target: "telemetry", "Disconnected from {}: {:?}", self.addr, err);
							let timeout = gen_rand_reconnect_delay();
							self.socket = NodeSocket::WaitingReconnect(timeout);
							return Poll::Ready(NodeEvent::Disconnected(err))
						}
					}
				NodeSocket::Dialing(mut s) => match Future::poll(Pin::new(&mut s), cx) {
					Poll::Ready(Ok(sink)) => {
						debug!(target: "telemetry", "Connected to {}", self.addr);
						let conn = NodeSocketConnected { sink, pending: VecDeque::new(), need_flush: false };
						self.socket = NodeSocket::Connected(conn);
						return Poll::Ready(NodeEvent::Connected)
					},
					Poll::Pending => break NodeSocket::Dialing(s),
					Poll::Ready(Err(err)) => {
						warn!(target: "telemetry", "Error while dialing {}: {:?}", self.addr, err);
						let timeout = gen_rand_reconnect_delay();
						socket = NodeSocket::WaitingReconnect(timeout);
					}
				}
				NodeSocket::ReconnectNow => match self.transport.clone().dial(self.addr.clone()) {
					Ok(d) => {
						debug!(target: "telemetry", "Started dialing {}", self.addr);
						socket = NodeSocket::Dialing(d.compat());
					}
					Err(err) => {
						warn!(target: "telemetry", "Error while dialing {}: {:?}", self.addr, err);
						let timeout = gen_rand_reconnect_delay();
						socket = NodeSocket::WaitingReconnect(timeout);
					}
				}
				NodeSocket::WaitingReconnect(mut s) =>
					if let Poll::Ready(_) = Future::poll(Pin::new(&mut s), cx) {
						socket = NodeSocket::ReconnectNow;
					} else {
						break NodeSocket::WaitingReconnect(s)
					}
				NodeSocket::Poisoned => {
					error!(target: "telemetry", "Poisoned connection with {}", self.addr);
					break NodeSocket::Poisoned
				}
			}
		};

		Poll::Pending
	}
}

/// Generates a `Delay` object with a random timeout.
///
/// If there are general connection issues, not all endpoints should be synchronized in their
/// re-connection time.
fn gen_rand_reconnect_delay() -> Delay {
	let random_delay = rand::thread_rng().gen_range(5, 10);
	Delay::new(Duration::from_secs(random_delay))
}

impl<TTrans: Transport, TSinkErr> NodeSocketConnected<TTrans>
where TTrans::Output: Sink<BytesMut, Error = TSinkErr>
	+ Stream<Item=Result<BytesMut, TSinkErr>>
	+ Unpin
{
	/// Processes the queue of messages for the connected socket.
	///
	/// The address is passed for logging purposes only.
	fn poll(
		mut self: Pin<&mut Self>,
		cx: &mut Context,
		my_addr: &Multiaddr
	) -> Poll<Result<futures::never::Never, TSinkErr>> {
		loop {
			if let Some(item) = self.pending.pop_front() {
				if let Poll::Pending = Sink::poll_ready(Pin::new(&mut self.sink), cx) {
					self.pending.push_front(item);
					return Poll::Pending
				}

				let item_len = item.len();
				if let Err(err) = Sink::start_send(Pin::new(&mut self.sink), item) {
					return Poll::Ready(Err(err))
				}
				trace!(
					target: "telemetry", "Successfully sent {:?} bytes message to {}",
					item_len, my_addr
				);
				self.need_flush = true;

			} else if self.need_flush {
				match Sink::poll_flush(Pin::new(&mut self.sink), cx) {
					Poll::Pending => return Poll::Pending,
					Poll::Ready(Err(err)) => return Poll::Ready(Err(err)),
					Poll::Ready(Ok(())) => self.need_flush = false,
				}

			} else {
				match Stream::poll_next(Pin::new(&mut self.sink), cx) {
					Poll::Ready(Some(Ok(_))) => {
						// We poll the telemetry `Stream` because the underlying implementation relies on
						// this in order to answer PINGs.
						// We don't do anything with incoming messages, however.
					},
					Poll::Ready(Some(Err(err))) => {
						return Poll::Ready(Err(err))
					},
					Poll::Pending | Poll::Ready(None) => break,
				}
			}
		}

		Poll::Pending
	}
}

impl<TTrans: Transport> fmt::Debug for Node<TTrans> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		let state = match self.socket {
			NodeSocket::Connected(_) => "Connected",
			NodeSocket::Dialing(_) => "Dialing",
			NodeSocket::ReconnectNow => "Pending reconnect",
			NodeSocket::WaitingReconnect(_) => "Pending reconnect",
			NodeSocket::Poisoned => "Poisoned",
		};

		f.debug_struct("Node")
			.field("addr", &self.addr)
			.field("state", &state)
			.finish()
	}
}
