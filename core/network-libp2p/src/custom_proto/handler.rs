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

use crate::custom_proto::upgrade::{CustomMessage, RegisteredProtocol};
use crate::custom_proto::upgrade::{RegisteredProtocolEvent, RegisteredProtocolSubstream};
use futures::prelude::*;
use libp2p::core::{
	PeerId, Endpoint, ProtocolsHandler, ProtocolsHandlerEvent,
	protocols_handler::IntoProtocolsHandler,
	protocols_handler::KeepAlive,
	protocols_handler::ProtocolsHandlerUpgrErr,
	protocols_handler::SubstreamProtocol,
	upgrade::{InboundUpgrade, OutboundUpgrade}
};
use log::{debug, error};
use smallvec::{smallvec, SmallVec};
use std::{borrow::Cow, error, fmt, io, marker::PhantomData, mem, time::Duration};
use tokio_io::{AsyncRead, AsyncWrite};
use tokio_timer::{Delay, clock::Clock};

/// Implements the `IntoProtocolsHandler` trait of libp2p.
///
/// Every time a connection with a remote starts, an instance of this struct is created and
/// sent to a background task dedicated to this connection. Once the connection is established,
/// it is turned into a `CustomProtoHandler`. It then handles all communications that are specific
/// to Substrate on that single connection.
///
/// Note that there can be multiple instance of this struct simultaneously for same peer. However
/// if that happens, only one main instance can communicate with the outer layers of the code. In
/// other words, the outer layers of the code only ever see one handler.
///
/// ## State of the handler
///
/// There are six possible states for the handler:
///
/// - Enabled and open, which is a normal operation.
/// - Enabled and closed, in which case it will try to open substreams.
/// - Disabled and open, in which case it will try to close substreams.
/// - Disabled and closed, in which case the handler is idle. The connection will be
///   garbage-collected after a few seconds if nothing more happens.
/// - Initializing and open.
/// - Initializing and closed, which is the state the handler starts in.
///
/// The Init/Enabled/Disabled state is entirely controlled by the user by sending `Enable` or
/// `Disable` messages to the handler. The handler itself never transitions automatically between
/// these states. For example, if the handler reports a network misbehaviour, it will close the
/// substreams but it is the role of the user to send a `Disabled` event if it wants the connection
/// to close. Otherwise, the handler will try to reopen substreams.
/// The handler starts in the "Initializing" state and must be transitionned to Enabled or Disabled
/// as soon as possible.
///
/// The Open/Closed state is decided by the handler and is reported with the `CustomProtocolOpen`
/// and `CustomProtocolClosed` events. The `CustomMessage` event can only be generated if the
/// handler is open.
///
/// ## How it works
///
/// When the handler is created, it is initially in the `Init` state and waits for either a
/// `Disable` or an `Enable` message from the outer layer. At any time, the outer layer is free to
/// toggle the handler between the disabled and enabled states.
///
/// When the handler switches to "enabled", it opens a substream and negotiates the protocol named
/// `/substrate/xxx`, where `xxx` is chosen by the user and depends on the chain.
///
/// For backwards compatibility reasons, when we switch to "enabled" for the first time (while we
/// are still in "init" mode) and we are the connection listener, we don't open a substream.
///
/// In order the handle the situation where both the remote and us get enabled at the same time,
/// we tolerate multiple substreams open at the same time. Messages are transmitted on an arbitrary
/// substream. The endpoints don't try to agree on a single substream.
///
/// We consider that we are now "closed" if the remote closes all the existing substreams.
/// Re-opening it can then be performed by closing all active substream and re-opening one.
///
pub struct CustomProtoHandlerProto<TMessage, TSubstream> {
	/// Configuration for the protocol upgrade to negotiate.
	protocol: RegisteredProtocol<TMessage>,

	/// Marker to pin the generic type.
	marker: PhantomData<TSubstream>,
}

impl<TMessage, TSubstream> CustomProtoHandlerProto<TMessage, TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
	TMessage: CustomMessage,
{
	/// Builds a new `CustomProtoHandlerProto`.
	pub fn new(protocol: RegisteredProtocol<TMessage>) -> Self {
		CustomProtoHandlerProto {
			protocol,
			marker: PhantomData,
		}
	}
}

impl<TMessage, TSubstream> IntoProtocolsHandler for CustomProtoHandlerProto<TMessage, TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
	TMessage: CustomMessage,
{
	type Handler = CustomProtoHandler<TMessage, TSubstream>;

	fn into_handler(self, remote_peer_id: &PeerId) -> Self::Handler {
		let clock = Clock::new();
		CustomProtoHandler {
			protocol: self.protocol,
			remote_peer_id: remote_peer_id.clone(),
			state: ProtocolState::Init {
				substreams: SmallVec::new(),
				init_deadline: Delay::new(clock.now() + Duration::from_secs(5))
			},
			events_queue: SmallVec::new(),
			clock,
		}
	}
}

/// The actual handler once the connection has been established.
pub struct CustomProtoHandler<TMessage, TSubstream> {
	/// Configuration for the protocol upgrade to negotiate.
	protocol: RegisteredProtocol<TMessage>,

	/// State of the communications with the remote.
	state: ProtocolState<TMessage, TSubstream>,

	/// Identifier of the node we're talking to. Used only for logging purposes and shouldn't have
	/// any influence on the behaviour.
	remote_peer_id: PeerId,

	/// Queue of events to send to the outside.
	///
	/// This queue must only ever be modified to insert elements at the back, or remove the first
	/// element.
	events_queue: SmallVec<[ProtocolsHandlerEvent<RegisteredProtocol<TMessage>, (), CustomProtoHandlerOut<TMessage>>; 16]>,

	/// `Clock` instance that uses the current execution context's source of time.
	clock: Clock,
}

/// State of the handler.
enum ProtocolState<TMessage, TSubstream> {
	/// Waiting for the behaviour to tell the handler whether it is enabled or disabled.
	Init {
		/// List of substreams opened by the remote but that haven't been processed yet.
		substreams: SmallVec<[RegisteredProtocolSubstream<TMessage, TSubstream>; 6]>,
		/// Deadline after which the initialization is abnormally long.
		init_deadline: Delay,
	},

	/// Handler is opening a substream in order to activate itself.
	/// If we are in this state, we haven't sent any `CustomProtocolOpen` yet.
	Opening {
		/// Deadline after which the opening is abnormally long.
		deadline: Delay,
	},

	/// Normal operating mode. Contains the substreams that are open.
	/// If we are in this state, we have sent a `CustomProtocolOpen` message to the outside.
	Normal {
		/// The substreams where bidirectional communications happen.
		substreams: SmallVec<[RegisteredProtocolSubstream<TMessage, TSubstream>; 4]>,
		/// Contains substreams which are being shut down.
		shutdown: SmallVec<[RegisteredProtocolSubstream<TMessage, TSubstream>; 4]>,
	},

	/// We are disabled. Contains substreams that are being closed.
	/// If we are in this state, either we have sent a `CustomProtocolClosed` message to the
	/// outside or we have never sent any `CustomProtocolOpen` in the first place.
	Disabled {
		/// List of substreams to shut down.
		shutdown: SmallVec<[RegisteredProtocolSubstream<TMessage, TSubstream>; 6]>,

		/// If true, we should reactivate the handler after all the substreams in `shutdown` have
		/// been closed.
		///
		/// Since we don't want to mix old and new substreams, we wait for all old substreams to
		/// be closed before opening any new one.
		reenable: bool,
	},

	/// In this state, we don't care about anything anymore and need to kill the connection as soon
	/// as possible.
	KillAsap,

	/// We sometimes temporarily switch to this state during processing. If we are in this state
	/// at the beginning of a method, that means something bad happened in the source code.
	Poisoned,
}

/// Event that can be received by a `CustomProtoHandler`.
#[derive(Debug)]
pub enum CustomProtoHandlerIn<TMessage> {
	/// The node should start using custom protocols. Contains whether we are the dialer or the
	/// listener of the connection.
	Enable(Endpoint),

	/// The node should stop using custom protocols.
	Disable,

	/// Sends a message through a custom protocol substream.
	SendCustomMessage {
		/// The message to send.
		message: TMessage,
	},
}

/// Event that can be emitted by a `CustomProtoHandler`.
#[derive(Debug)]
pub enum CustomProtoHandlerOut<TMessage> {
	/// Opened a custom protocol with the remote.
	CustomProtocolOpen {
		/// Version of the protocol that has been opened.
		version: u8,
	},

	/// Closed a custom protocol with the remote.
	CustomProtocolClosed {
		/// Reason why the substream closed, for diagnostic purposes.
		reason: Cow<'static, str>,
	},

	/// Receives a message on a custom protocol substream.
	CustomMessage {
		/// Message that has been received.
		message: TMessage,
	},

	/// A substream to the remote is clogged. The send buffer is very large, and we should print
	/// a diagnostic message and/or avoid sending more data.
	Clogged {
		/// Copy of the messages that are within the buffer, for further diagnostic.
		messages: Vec<TMessage>,
	},

	/// An error has happened on the protocol level with this node.
	ProtocolError {
		/// If true the error is severe, such as a protocol violation.
		is_severe: bool,
		/// The error that happened.
		error: Box<dyn error::Error + Send + Sync>,
	},
}

impl<TMessage, TSubstream> CustomProtoHandler<TMessage, TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
	TMessage: CustomMessage,
{
	/// Enables the handler.
	fn enable(&mut self, endpoint: Endpoint) {
		self.state = match mem::replace(&mut self.state, ProtocolState::Poisoned) {
			ProtocolState::Poisoned => {
				error!(target: "sub-libp2p", "Handler with {:?} is in poisoned state",
					self.remote_peer_id);
				ProtocolState::Poisoned
			}

			ProtocolState::Init { substreams: incoming, .. } => {
				if incoming.is_empty() {
					if let Endpoint::Dialer = endpoint {
						self.events_queue.push(ProtocolsHandlerEvent::OutboundSubstreamRequest {
							protocol: SubstreamProtocol::new(self.protocol.clone()),
							info: (),
						});
					}
					ProtocolState::Opening {
						deadline: Delay::new(self.clock.now() + Duration::from_secs(60))
					}

				} else {
					let event = CustomProtoHandlerOut::CustomProtocolOpen {
						version: incoming[0].protocol_version()
					};
					self.events_queue.push(ProtocolsHandlerEvent::Custom(event));
					ProtocolState::Normal {
						substreams: incoming.into_iter().collect(),
						shutdown: SmallVec::new()
					}
				}
			}

			st @ ProtocolState::KillAsap => st,
			st @ ProtocolState::Opening { .. } => st,
			st @ ProtocolState::Normal { .. } => st,
			ProtocolState::Disabled { shutdown, .. } => {
				ProtocolState::Disabled { shutdown, reenable: true }
			}
		}
	}

	/// Disables the handler.
	fn disable(&mut self) {
		self.state = match mem::replace(&mut self.state, ProtocolState::Poisoned) {
			ProtocolState::Poisoned => {
				error!(target: "sub-libp2p", "Handler with {:?} is in poisoned state",
					self.remote_peer_id);
				ProtocolState::Poisoned
			}

			ProtocolState::Init { substreams: mut shutdown, .. } => {
				for s in &mut shutdown {
					s.shutdown();
				}
				ProtocolState::Disabled { shutdown, reenable: false }
			}

			ProtocolState::Opening { .. } | ProtocolState::Normal { .. } =>
				// At the moment, if we get disabled while things were working, we kill the entire
				// connection in order to force a reset of the state.
				// This is obviously an extremely shameful way to do things, but at the time of
				// the writing of this comment, the networking works very poorly and a solution
				// needs to be found.
				ProtocolState::KillAsap,

			ProtocolState::Disabled { shutdown, .. } =>
				ProtocolState::Disabled { shutdown, reenable: false },

			ProtocolState::KillAsap => ProtocolState::KillAsap,
		};
	}

	/// Polls the state for events. Optionally returns an event to produce.
	#[must_use]
	fn poll_state(&mut self)
		-> Option<ProtocolsHandlerEvent<RegisteredProtocol<TMessage>, (), CustomProtoHandlerOut<TMessage>>> {
		match mem::replace(&mut self.state, ProtocolState::Poisoned) {
			ProtocolState::Poisoned => {
				error!(target: "sub-libp2p", "Handler with {:?} is in poisoned state",
					self.remote_peer_id);
				self.state = ProtocolState::Poisoned;
				None
			}

			ProtocolState::Init { substreams, mut init_deadline } => {
				match init_deadline.poll() {
					Ok(Async::Ready(())) => {
						init_deadline.reset(self.clock.now() + Duration::from_secs(60));
						error!(target: "sub-libp2p", "Handler initialization process is too long \
							with {:?}", self.remote_peer_id)
					},
					Ok(Async::NotReady) => {}
					Err(_) => error!(target: "sub-libp2p", "Tokio timer has errored")
				}

				self.state = ProtocolState::Init { substreams, init_deadline };
				None
			}

			ProtocolState::Opening { mut deadline } => {
				match deadline.poll() {
					Ok(Async::Ready(())) => {
						deadline.reset(self.clock.now() + Duration::from_secs(60));
						let event = CustomProtoHandlerOut::ProtocolError {
							is_severe: true,
							error: "Timeout when opening protocol".to_string().into(),
						};
						self.state = ProtocolState::Opening { deadline };
						Some(ProtocolsHandlerEvent::Custom(event))
					},
					Ok(Async::NotReady) => {
						self.state = ProtocolState::Opening { deadline };
						None
					},
					Err(_) => {
						error!(target: "sub-libp2p", "Tokio timer has errored");
						deadline.reset(self.clock.now() + Duration::from_secs(60));
						self.state = ProtocolState::Opening { deadline };
						None
					},
				}
			}

			ProtocolState::Normal { mut substreams, mut shutdown } => {
				for n in (0..substreams.len()).rev() {
					let mut substream = substreams.swap_remove(n);
					match substream.poll() {
						Ok(Async::NotReady) => substreams.push(substream),
						Ok(Async::Ready(Some(RegisteredProtocolEvent::Message(message)))) => {
							let event = CustomProtoHandlerOut::CustomMessage {
								message
							};
							substreams.push(substream);
							self.state = ProtocolState::Normal { substreams, shutdown };
							return Some(ProtocolsHandlerEvent::Custom(event));
						},
						Ok(Async::Ready(Some(RegisteredProtocolEvent::Clogged { messages }))) => {
							let event = CustomProtoHandlerOut::Clogged {
								messages,
							};
							substreams.push(substream);
							self.state = ProtocolState::Normal { substreams, shutdown };
							return Some(ProtocolsHandlerEvent::Custom(event));
						}
						Ok(Async::Ready(None)) => {
							shutdown.push(substream);
							if substreams.is_empty() {
								let event = CustomProtoHandlerOut::CustomProtocolClosed {
									reason: "All substreams have been closed by the remote".into(),
								};
								self.state = ProtocolState::Disabled {
									shutdown: shutdown.into_iter().collect(),
									reenable: true
								};
								return Some(ProtocolsHandlerEvent::Custom(event));
							}
						}
						Err(err) => {
							if substreams.is_empty() {
								let event = CustomProtoHandlerOut::CustomProtocolClosed {
									reason: format!("Error on the last substream: {:?}", err).into(),
								};
								self.state = ProtocolState::Disabled {
									shutdown: shutdown.into_iter().collect(),
									reenable: true
								};
								return Some(ProtocolsHandlerEvent::Custom(event));
							} else {
								debug!(target: "sub-libp2p", "Error on extra substream: {:?}", err);
							}
						}
					}
				}

				// This code is reached is none if and only if none of the substreams are in a ready state.
				self.state = ProtocolState::Normal { substreams, shutdown };
				None
			}

			ProtocolState::Disabled { mut shutdown, reenable } => {
				shutdown_list(&mut shutdown);
				// If `reenable` is `true`, that means we should open the substreams system again
				// after all the substreams are closed.
				if reenable && shutdown.is_empty() {
					self.state = ProtocolState::Opening {
						deadline: Delay::new(self.clock.now() + Duration::from_secs(60))
					};
					Some(ProtocolsHandlerEvent::OutboundSubstreamRequest {
						protocol: SubstreamProtocol::new(self.protocol.clone()),
						info: (),
					})
				} else {
					self.state = ProtocolState::Disabled { shutdown, reenable };
					None
				}
			}

			ProtocolState::KillAsap => None,
		}
	}

	/// Called by `inject_fully_negotiated_inbound` and `inject_fully_negotiated_outbound`.
	fn inject_fully_negotiated(
		&mut self,
		mut substream: RegisteredProtocolSubstream<TMessage, TSubstream>
	) {
		self.state = match mem::replace(&mut self.state, ProtocolState::Poisoned) {
			ProtocolState::Poisoned => {
				error!(target: "sub-libp2p", "Handler with {:?} is in poisoned state",
					self.remote_peer_id);
				ProtocolState::Poisoned
			}

			ProtocolState::Init { mut substreams, init_deadline } => {
				if substream.endpoint() == Endpoint::Dialer {
					error!(target: "sub-libp2p", "Opened dialing substream with {:?} before \
						initialization", self.remote_peer_id);
				}
				substreams.push(substream);
				ProtocolState::Init { substreams, init_deadline }
			}

			ProtocolState::Opening { .. } => {
				let event = CustomProtoHandlerOut::CustomProtocolOpen {
					version: substream.protocol_version()
				};
				self.events_queue.push(ProtocolsHandlerEvent::Custom(event));
				ProtocolState::Normal {
					substreams: smallvec![substream],
					shutdown: SmallVec::new()
				}
			}

			ProtocolState::Normal { substreams: mut existing, shutdown } => {
				existing.push(substream);
				ProtocolState::Normal { substreams: existing, shutdown }
			}

			ProtocolState::Disabled { mut shutdown, .. } => {
				substream.shutdown();
				shutdown.push(substream);
				ProtocolState::Disabled { shutdown, reenable: false }
			}

			ProtocolState::KillAsap => ProtocolState::KillAsap,
		};
	}

	/// Sends a message to the remote.
	fn send_message(&mut self, message: TMessage) {
		match self.state {
			ProtocolState::Normal { ref mut substreams, .. } =>
				substreams[0].send_message(message),

			_ => debug!(target: "sub-libp2p", "Tried to send message over closed protocol \
				with {:?}", self.remote_peer_id)
		}
	}
}

impl<TMessage, TSubstream> ProtocolsHandler for CustomProtoHandler<TMessage, TSubstream>
where TSubstream: AsyncRead + AsyncWrite, TMessage: CustomMessage {
	type InEvent = CustomProtoHandlerIn<TMessage>;
	type OutEvent = CustomProtoHandlerOut<TMessage>;
	type Substream = TSubstream;
	type Error = ConnectionKillError;
	type InboundProtocol = RegisteredProtocol<TMessage>;
	type OutboundProtocol = RegisteredProtocol<TMessage>;
	type OutboundOpenInfo = ();

	fn listen_protocol(&self) -> SubstreamProtocol<Self::InboundProtocol> {
		SubstreamProtocol::new(self.protocol.clone())
	}

	fn inject_fully_negotiated_inbound(
		&mut self,
		proto: <Self::InboundProtocol as InboundUpgrade<TSubstream>>::Output
	) {
		self.inject_fully_negotiated(proto);
	}

	fn inject_fully_negotiated_outbound(
		&mut self,
		proto: <Self::OutboundProtocol as OutboundUpgrade<TSubstream>>::Output,
		_: Self::OutboundOpenInfo
	) {
		self.inject_fully_negotiated(proto);
	}

	fn inject_event(&mut self, message: CustomProtoHandlerIn<TMessage>) {
		match message {
			CustomProtoHandlerIn::Disable => self.disable(),
			CustomProtoHandlerIn::Enable(endpoint) => self.enable(endpoint),
			CustomProtoHandlerIn::SendCustomMessage { message } =>
				self.send_message(message),
		}
	}

	#[inline]
	fn inject_dial_upgrade_error(&mut self, _: (), err: ProtocolsHandlerUpgrErr<io::Error>) {
		let is_severe = match err {
			ProtocolsHandlerUpgrErr::Upgrade(_) => true,
			_ => false,
		};

		self.events_queue.push(ProtocolsHandlerEvent::Custom(CustomProtoHandlerOut::ProtocolError {
			is_severe,
			error: Box::new(err),
		}));
	}

	fn connection_keep_alive(&self) -> KeepAlive {
		match self.state {
			ProtocolState::Init { .. } | ProtocolState::Opening { .. } |
			ProtocolState::Normal { .. } => KeepAlive::Yes,
			ProtocolState::Disabled { .. } | ProtocolState::Poisoned |
      ProtocolState::KillAsap => KeepAlive::No,
		}
	}

	fn poll(
		&mut self,
	) -> Poll<
		ProtocolsHandlerEvent<Self::OutboundProtocol, Self::OutboundOpenInfo, Self::OutEvent>,
		Self::Error,
	> {
		// Flush the events queue if necessary.
		if !self.events_queue.is_empty() {
			let event = self.events_queue.remove(0);
			return Ok(Async::Ready(event))
		}

		// Kill the connection if needed.
		if let ProtocolState::KillAsap = self.state {
			return Err(ConnectionKillError);
		}

		// Process all the substreams.
		if let Some(event) = self.poll_state() {
			return Ok(Async::Ready(event))
		}

		Ok(Async::NotReady)
	}
}

impl<TMessage, TSubstream> fmt::Debug for CustomProtoHandler<TMessage, TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
{
	fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
		f.debug_struct("CustomProtoHandler")
			.finish()
	}
}

/// Given a list of substreams, tries to shut them down. The substreams that have been successfully
/// shut down are removed from the list.
fn shutdown_list<TMessage, TSubstream>
	(list: &mut SmallVec<impl smallvec::Array<Item = RegisteredProtocolSubstream<TMessage, TSubstream>>>)
where TSubstream: AsyncRead + AsyncWrite, TMessage: CustomMessage {
	'outer: for n in (0..list.len()).rev() {
		let mut substream = list.swap_remove(n);
		loop {
			match substream.poll() {
				Ok(Async::Ready(Some(_))) => {}
				Ok(Async::NotReady) => break,
				Err(_) | Ok(Async::Ready(None)) => continue 'outer,
			}
		}
		list.push(substream);
	}
}

/// Error returned when switching from normal to disabled.
#[derive(Debug)]
pub struct ConnectionKillError;

impl error::Error for ConnectionKillError {
}

impl fmt::Display for ConnectionKillError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "Connection kill when switching from normal to disabled")
	}
}
