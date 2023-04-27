// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use core::pin::Pin;
use futures::prelude::*;
use soketto::handshake::{server::Response, Server};
use std::{io, net::SocketAddr};
use tokio::net::{TcpListener, TcpStream};
use tokio_util::compat::{Compat, TokioAsyncReadCompatExt};

/// Configuration for a [`WsServer`].
pub struct Config {
	/// IP address to try to bind to.
	pub bind_address: SocketAddr,

	/// Maximum size, in bytes, of a frame sent by the remote.
	///
	/// Since the messages are entirely buffered before being returned, a maximum value is
	/// necessary in order to prevent malicious clients from sending huge frames that would
	/// occupy a lot of memory.
	pub max_frame_size: usize,

	/// Number of pending messages to buffer up for sending before the socket is considered
	/// unresponsive.
	pub send_buffer_len: usize,

	/// Pre-allocated capacity for the list of connections.
	pub capacity: usize,
}

/// Identifier for a connection with regard to a [`WsServer`].
///
/// After a connection has been closed, its [`ConnectionId`] might be reused.
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ConnectionId(u64);

/// A WebSocket message.
pub enum Message {
	Text(String),
	Binary(Vec<u8>),
}

/// WebSockets listening socket and list of open connections.
pub struct WsServer {
	/// Value passed through [`Config::max_frame_size`].
	max_frame_size: usize,

	/// Endpoint for incoming TCP sockets.
	listener: TcpListener,

	/// Pending incoming connection to accept. Accepted by calling [`WsServer::accept`].
	pending_incoming: Option<TcpStream>,

	/// List of TCP connections that are currently negotiating the WebSocket handshake.
	///
	/// The output can be an error if the handshake fails.
	negotiating: stream::FuturesUnordered<
		Pin<
			Box<
				dyn Future<
						Output = Result<
							Server<'static, Compat<TcpStream>>,
							Box<dyn std::error::Error>,
						>,
					> + Send,
			>,
		>,
	>,

	/// List of streams of incoming messages for all connections.
	incoming_messages: stream::SelectAll<
		Pin<Box<dyn Stream<Item = Result<Message, Box<dyn std::error::Error>>> + Send>>,
	>,

	/// Tasks dedicated to closing sockets that have been rejected.
	rejected_sockets: stream::FuturesUnordered<Pin<Box<dyn Future<Output = ()> + Send>>>,
}

impl WsServer {
	/// Try opening a TCP listening socket.
	///
	/// Returns an error if the listening socket fails to open.
	pub async fn new(config: Config) -> Result<Self, io::Error> {
		let listener = TcpListener::bind(config.bind_address).await?;

		Ok(WsServer {
			max_frame_size: config.max_frame_size,
			listener,
			pending_incoming: None,
			negotiating: stream::FuturesUnordered::new(),
			incoming_messages: stream::SelectAll::new(),
			rejected_sockets: stream::FuturesUnordered::new(),
		})
	}

	/// Address of the local TCP listening socket, as provided by the operating system.
	pub fn local_addr(&self) -> Result<SocketAddr, io::Error> {
		self.listener.local_addr()
	}

	/// Accepts the pending connection.
	///
	/// Either [`WsServer::accept`] or [`WsServer::reject`] must be called after a
	/// [`Event::ConnectionOpen`] event is returned.
	///
	/// # Panic
	///
	/// Panics if no connection is pending.
	pub fn accept(&mut self) {
		let pending_incoming = self.pending_incoming.take().expect("no pending socket");

		self.negotiating.push(Box::pin(async move {
			let mut server = Server::new(pending_incoming.compat());

			let websocket_key = match server.receive_request().await {
				Ok(req) => req.key(),
				Err(err) => return Err(Box::new(err) as Box<_>),
			};

			match server
				.send_response(&{ Response::Accept { key: websocket_key, protocol: None } })
				.await
			{
				Ok(()) => {},
				Err(err) => return Err(Box::new(err) as Box<_>),
			};

			Ok(server)
		}));
	}

	/// Reject the pending connection.
	///
	/// Either [`WsServer::accept`] or [`WsServer::reject`] must be called after a
	/// [`Event::ConnectionOpen`] event is returned.
	///
	/// # Panic
	///
	/// Panics if no connection is pending.
	pub fn reject(&mut self) {
		let _ = self.pending_incoming.take().expect("no pending socket");
	}

	/// Returns the next event happening on the server.
	pub async fn next_event(&mut self) -> Event {
		loop {
			futures::select! {
				// Only try to fetch a new incoming connection if none is pending.
				socket = {
					let listener = &self.listener;
					let has_pending = self.pending_incoming.is_some();
					async move {
						if !has_pending {
							listener.accept().await
						} else {
							loop { futures::pending!() }
						}
					}
				}.fuse() => {
					let (socket, address) = match socket {
						Ok(s) => s,
						Err(_) => continue,
					};
					debug_assert!(self.pending_incoming.is_none());
					self.pending_incoming = Some(socket);
					return Event::ConnectionOpen { address };
				},

				result = self.negotiating.select_next_some() => {
					let server = match result {
						Ok(s) => s,
						Err(error) => return Event::ConnectionError {
							error,
						},
					};

					let (mut _sender, receiver) = {
						let mut builder = server.into_builder();
						builder.set_max_frame_size(self.max_frame_size);
						builder.set_max_message_size(self.max_frame_size);
						builder.finish()
					};

					// Spawn a task dedicated to receiving messages from the socket.
					self.incoming_messages.push({
						// Turn `receiver` into a stream of received packets.
						let socket_packets = stream::unfold((receiver, Vec::new()), move |(mut receiver, mut buf)| async {
							buf.clear();
							let ret = match receiver.receive_data(&mut buf).await {
								Ok(soketto::Data::Text(len)) => String::from_utf8(buf[..len].to_vec())
									.map(Message::Text)
									.map_err(|err| Box::new(err) as Box<_>),
								Ok(soketto::Data::Binary(len)) => Ok(buf[..len].to_vec())
									.map(Message::Binary),
								Err(err) => Err(Box::new(err) as Box<_>),
							};
							Some((ret, (receiver, buf)))
						});

						Box::pin(socket_packets.map(move |msg| (msg)))
					});
				},

				result = self.incoming_messages.select_next_some() => {
					let message = match result {
						Ok(m) => m,
						Err(error) => return Event::ConnectionError {
							error,
						},
					};

					match message {
						Message::Text(message) => {
							return Event::TextFrame {
								message,
							}
						}
						Message::Binary(message) => {
							return Event::BinaryFrame {
								message,
							}
						}
					}
				},

				_ = self.rejected_sockets.select_next_some() => {
				}
			}
		}
	}
}

/// Event that has happened on a [`WsServer`].
#[derive(Debug)]
pub enum Event {
	/// A new TCP connection has arrived on the listening socket.
	///
	/// The connection *must* be accepted or rejected using [`WsServer::accept`] or
	/// [`WsServer::reject`].
	/// No other [`Event::ConnectionOpen`] event will be generated until the current pending
	/// connection has been either accepted or rejected.
	ConnectionOpen {
		/// Address of the remote, as provided by the operating system.
		address: SocketAddr,
	},

	/// An error has happened on a connection. The connection is now closed and its
	/// [`ConnectionId`] is now invalid.
	ConnectionError { error: Box<dyn std::error::Error> },

	/// A text frame has been received on a connection.
	TextFrame {
		/// Message sent by the remote. Its content is entirely decided by the client, and
		/// nothing must be assumed about the validity of this message.
		message: String,
	},

	/// A text frame has been received on a connection.
	BinaryFrame {
		/// Message sent by the remote. Its content is entirely decided by the client, and
		/// nothing must be assumed about the validity of this message.
		message: Vec<u8>,
	},
}
