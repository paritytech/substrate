// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

use crate::protocol::generic_proto::upgrade::{RegisteredProtocol, RegisteredProtocolEvent, RegisteredProtocolSubstream};
use bytes::BytesMut;
use futures::prelude::*;
use futures_timer::Delay;
use libp2p::core::{ConnectedPoint, PeerId, Endpoint};
use libp2p::core::upgrade::{InboundUpgrade, OutboundUpgrade};
use libp2p::swarm::{
	ProtocolsHandler, ProtocolsHandlerEvent,
	IntoProtocolsHandler,
	KeepAlive,
	ProtocolsHandlerUpgrErr,
	SubstreamProtocol,
	NegotiatedSubstream,
};
use log::{debug, error};
use smallvec::{smallvec, SmallVec};
use std::{borrow::Cow, collections::VecDeque, convert::Infallible, error, fmt, io, mem};
use std::{pin::Pin, task::{Context, Poll}, time::Duration};

/// Implements the `IntoProtocolsHandler` trait of libp2p.
///
/// Every time a connection with a remote starts, an instance of this struct is created and
/// sent to a background task dedicated to this connection. Once the connection is established,
/// it is turned into a `LegacyProtoHandler`. It then handles all communications that are specific
/// to Substrate on that single connection.
///
/// Note that there can be multiple instance of this struct simultaneously for same peer,
/// if there are multiple established connections to the peer.
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
///
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
pub struct LegacyProtoHandlerProto {
	/// Configuration for the protocol upgrade to negotiate.
	protocol: RegisteredProtocol,
}

impl LegacyProtoHandlerProto {
	/// Builds a new `LegacyProtoHandlerProto`.
	pub fn new(protocol: RegisteredProtocol) -> Self {
		LegacyProtoHandlerProto {
			protocol,
		}
	}
}

impl IntoProtocolsHandler for LegacyProtoHandlerProto {
	type Handler = LegacyProtoHandler;

	fn inbound_protocol(&self) -> RegisteredProtocol {
		self.protocol.clone()
	}

	fn into_handler(self, remote_peer_id: &PeerId, _: &ConnectedPoint) -> Self::Handler {
		LegacyProtoHandler {
			protocol: self.protocol,
			remote_peer_id: remote_peer_id.clone(),
			state: ProtocolState::Init {
				substreams: SmallVec::new(),
				init_deadline: Delay::new(Duration::from_secs(20))
			},
			events_queue: VecDeque::new(),
		}
	}
}

/// The actual handler once the connection has been established.
pub struct LegacyProtoHandler {
	/// Configuration for the protocol upgrade to negotiate.
	protocol: RegisteredProtocol,

	/// State of the communications with the remote.
	state: ProtocolState,

	/// Identifier of the node we're talking to. Used only for logging purposes and shouldn't have
	/// any influence on the behaviour.
	remote_peer_id: PeerId,

	/// Queue of events to send to the outside.
	///
	/// This queue must only ever be modified to insert elements at the back, or remove the first
	/// element.
	events_queue: VecDeque<
		ProtocolsHandlerEvent<RegisteredProtocol, Infallible, LegacyProtoHandlerOut, ConnectionKillError>
	>,
}

/// State of the handler.
enum ProtocolState {
	/// Waiting for the behaviour to tell the handler whether it is enabled or disabled.
	Init {
		/// List of substreams opened by the remote but that haven't been processed yet.
		/// For each substream, also includes the handshake message that we have received.
		substreams: SmallVec<[(RegisteredProtocolSubstream<NegotiatedSubstream>, Vec<u8>); 6]>,
		/// Deadline after which the initialization is abnormally long.
		init_deadline: Delay,
	},

	/// Handler is ready to accept incoming substreams.
	/// If we are in this state, we haven't sent any `CustomProtocolOpen` yet.
	Opening,

	/// Normal operating mode. Contains the substreams that are open.
	/// If we are in this state, we have sent a `CustomProtocolOpen` message to the outside.
	Normal {
		/// The substreams where bidirectional communications happen.
		substreams: SmallVec<[RegisteredProtocolSubstream<NegotiatedSubstream>; 4]>,
		/// Contains substreams which are being shut down.
		shutdown: SmallVec<[RegisteredProtocolSubstream<NegotiatedSubstream>; 4]>,
	},

	/// We are disabled. Contains substreams that are being closed.
	/// If we are in this state, either we have sent a `CustomProtocolClosed` message to the
	/// outside or we have never sent any `CustomProtocolOpen` in the first place.
	Disabled {
		/// List of substreams to shut down.
		shutdown: SmallVec<[RegisteredProtocolSubstream<NegotiatedSubstream>; 6]>,

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

/// Event that can be received by a `LegacyProtoHandler`.
#[derive(Debug)]
pub enum LegacyProtoHandlerIn {
	/// The node should start using custom protocols.
	Enable,

	/// The node should stop using custom protocols.
	Disable,
}

/// Event that can be emitted by a `LegacyProtoHandler`.
#[derive(Debug)]
pub enum LegacyProtoHandlerOut {
	/// Opened a custom protocol with the remote.
	CustomProtocolOpen {
		/// Version of the protocol that has been opened.
		version: u8,
		/// Handshake message that has been sent to us.
		/// This is normally a "Status" message, but this out of the concern of this code.
		received_handshake: Vec<u8>,
	},

	/// Closed a custom protocol with the remote.
	CustomProtocolClosed {
		/// Reason why the substream closed, for diagnostic purposes.
		reason: Cow<'static, str>,
	},

	/// Receives a message on a custom protocol substream.
	CustomMessage {
		/// Message that has been received.
		message: BytesMut,
	},
}

impl LegacyProtoHandler {
	/// Enables the handler.
	fn enable(&mut self) {
		self.state = match mem::replace(&mut self.state, ProtocolState::Poisoned) {
			ProtocolState::Poisoned => {
				error!(target: "sub-libp2p", "Handler with {:?} is in poisoned state",
					self.remote_peer_id);
				ProtocolState::Poisoned
			}

			ProtocolState::Init { substreams: mut incoming, .. } => {
				if incoming.is_empty() {
					ProtocolState::Opening
				} else {
					let event = LegacyProtoHandlerOut::CustomProtocolOpen {
						version: incoming[0].0.protocol_version(),
						received_handshake: mem::replace(&mut incoming[0].1, Vec::new()),
					};
					self.events_queue.push_back(ProtocolsHandlerEvent::Custom(event));
					ProtocolState::Normal {
						substreams: incoming.into_iter().map(|(s, _)| s).collect(),
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

			ProtocolState::Init { substreams: shutdown, .. } => {
				let mut shutdown = shutdown.into_iter().map(|(s, _)| s).collect::<SmallVec<[_; 6]>>();
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
	fn poll_state(&mut self, cx: &mut Context)
		-> Option<ProtocolsHandlerEvent<RegisteredProtocol, Infallible, LegacyProtoHandlerOut, ConnectionKillError>> {
		match mem::replace(&mut self.state, ProtocolState::Poisoned) {
			ProtocolState::Poisoned => {
				error!(target: "sub-libp2p", "Handler with {:?} is in poisoned state",
					self.remote_peer_id);
				self.state = ProtocolState::Poisoned;
				None
			}

			ProtocolState::Init { substreams, mut init_deadline } => {
				match Pin::new(&mut init_deadline).poll(cx) {
					Poll::Ready(()) => {
						error!(target: "sub-libp2p", "Handler initialization process is too long \
							with {:?}", self.remote_peer_id);
						self.state = ProtocolState::KillAsap;
					},
					Poll::Pending => {
						self.state = ProtocolState::Init { substreams, init_deadline };
					}
				}

				None
			}

			ProtocolState::Opening => {
				self.state = ProtocolState::Opening;
				None
			}

			ProtocolState::Normal { mut substreams, mut shutdown } => {
				for n in (0..substreams.len()).rev() {
					let mut substream = substreams.swap_remove(n);
					match Pin::new(&mut substream).poll_next(cx) {
						Poll::Pending => substreams.push(substream),
						Poll::Ready(Some(Ok(RegisteredProtocolEvent::Message(message)))) => {
							let event = LegacyProtoHandlerOut::CustomMessage {
								message
							};
							substreams.push(substream);
							self.state = ProtocolState::Normal { substreams, shutdown };
							return Some(ProtocolsHandlerEvent::Custom(event));
						},
						Poll::Ready(Some(Ok(RegisteredProtocolEvent::Clogged))) => {
							shutdown.push(substream);
							if substreams.is_empty() {
								let event = LegacyProtoHandlerOut::CustomProtocolClosed {
									reason: "Legacy substream clogged".into(),
								};
								self.state = ProtocolState::Disabled {
									shutdown: shutdown.into_iter().collect(),
									reenable: true
								};
								return Some(ProtocolsHandlerEvent::Custom(event));
							}
						}
						Poll::Ready(None) => {
							shutdown.push(substream);
							if substreams.is_empty() {
								let event = LegacyProtoHandlerOut::CustomProtocolClosed {
									reason: "All substreams have been closed by the remote".into(),
								};
								self.state = ProtocolState::Disabled {
									shutdown: shutdown.into_iter().collect(),
									reenable: true
								};
								return Some(ProtocolsHandlerEvent::Custom(event));
							}
						}
						Poll::Ready(Some(Err(err))) => {
							if substreams.is_empty() {
								let event = LegacyProtoHandlerOut::CustomProtocolClosed {
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
				shutdown_list(&mut shutdown, cx);
				// If `reenable` is `true`, that means we should open the substreams system again
				// after all the substreams are closed.
				if reenable && shutdown.is_empty() {
					self.state = ProtocolState::Opening;
				} else {
					self.state = ProtocolState::Disabled { shutdown, reenable };
				}
				None
			}

			ProtocolState::KillAsap => None,
		}
	}
}

impl ProtocolsHandler for LegacyProtoHandler {
	type InEvent = LegacyProtoHandlerIn;
	type OutEvent = LegacyProtoHandlerOut;
	type Error = ConnectionKillError;
	type InboundProtocol = RegisteredProtocol;
	type OutboundProtocol = RegisteredProtocol;
	type OutboundOpenInfo = Infallible;
	type InboundOpenInfo = ();

	fn listen_protocol(&self) -> SubstreamProtocol<Self::InboundProtocol, ()> {
		SubstreamProtocol::new(self.protocol.clone(), ())
	}

	fn inject_fully_negotiated_inbound(
		&mut self,
		(mut substream, received_handshake): <Self::InboundProtocol as InboundUpgrade<NegotiatedSubstream>>::Output,
		(): ()
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
				substreams.push((substream, received_handshake));
				ProtocolState::Init { substreams, init_deadline }
			}

			ProtocolState::Opening { .. } => {
				let event = LegacyProtoHandlerOut::CustomProtocolOpen {
					version: substream.protocol_version(),
					received_handshake,
				};
				self.events_queue.push_back(ProtocolsHandlerEvent::Custom(event));
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

	fn inject_fully_negotiated_outbound(
		&mut self,
		_: <Self::OutboundProtocol as OutboundUpgrade<NegotiatedSubstream>>::Output,
		unreachable: Self::OutboundOpenInfo
	) {
		match unreachable {}
	}

	fn inject_event(&mut self, message: LegacyProtoHandlerIn) {
		match message {
			LegacyProtoHandlerIn::Disable => self.disable(),
			LegacyProtoHandlerIn::Enable => self.enable(),
		}
	}

	fn inject_dial_upgrade_error(
		&mut self,
		unreachable: Self::OutboundOpenInfo,
		_: ProtocolsHandlerUpgrErr<io::Error>
	) {
		match unreachable {}
	}

	fn connection_keep_alive(&self) -> KeepAlive {
		match self.state {
			ProtocolState::Init { .. } | ProtocolState::Normal { .. } => KeepAlive::Yes,
			ProtocolState::Opening { .. } | ProtocolState::Disabled { .. } |
			ProtocolState::Poisoned | ProtocolState::KillAsap => KeepAlive::No,
		}
	}

	fn poll(
		&mut self,
		cx: &mut Context,
	) -> Poll<
		ProtocolsHandlerEvent<Self::OutboundProtocol, Self::OutboundOpenInfo, Self::OutEvent, Self::Error>
	> {
		// Flush the events queue if necessary.
		if let Some(event) = self.events_queue.pop_front() {
			return Poll::Ready(event)
		}

		// Kill the connection if needed.
		if let ProtocolState::KillAsap = self.state {
			return Poll::Ready(ProtocolsHandlerEvent::Close(ConnectionKillError));
		}

		// Process all the substreams.
		if let Some(event) = self.poll_state(cx) {
			return Poll::Ready(event)
		}

		Poll::Pending
	}
}

impl fmt::Debug for LegacyProtoHandler {
	fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
		f.debug_struct("LegacyProtoHandler")
			.finish()
	}
}

/// Given a list of substreams, tries to shut them down. The substreams that have been successfully
/// shut down are removed from the list.
fn shutdown_list
	(list: &mut SmallVec<impl smallvec::Array<Item = RegisteredProtocolSubstream<NegotiatedSubstream>>>,
	cx: &mut Context)
{
	'outer: for n in (0..list.len()).rev() {
		let mut substream = list.swap_remove(n);
		loop {
			match substream.poll_next_unpin(cx) {
				Poll::Ready(Some(Ok(_))) => {}
				Poll::Pending => break,
				Poll::Ready(Some(Err(_))) | Poll::Ready(None) => continue 'outer,
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
