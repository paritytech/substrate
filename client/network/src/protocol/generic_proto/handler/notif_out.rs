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

//! Implementations of the `IntoProtocolsHandler` and `ProtocolsHandler` traits for outgoing
//! substreams of a single gossiping protocol.
//!
//! > **Note**: Each instance corresponds to a single protocol. In order to support multiple
//! >			protocols, you need to create multiple instances and group them.
//!

use crate::protocol::generic_proto::upgrade::{NotificationsOut, NotificationsOutSubstream, NotificationsHandshakeError};
use futures::prelude::*;
use libp2p::core::{ConnectedPoint, PeerId};
use libp2p::core::upgrade::{DeniedUpgrade, InboundUpgrade, OutboundUpgrade};
use libp2p::swarm::{
	ProtocolsHandler, ProtocolsHandlerEvent,
	IntoProtocolsHandler,
	KeepAlive,
	ProtocolsHandlerUpgrErr,
	SubstreamProtocol,
	NegotiatedSubstream,
};
use log::{debug, warn, error};
use std::{
	borrow::Cow, collections::VecDeque, fmt, mem, pin::Pin, task::{Context, Poll, Waker},
	time::Duration
};
use wasm_timer::Instant;

/// Maximum duration to open a substream and receive the handshake message. After that, we
/// consider that we failed to open the substream.
const OPEN_TIMEOUT: Duration = Duration::from_secs(10);
/// After successfully establishing a connection with the remote, we keep the connection open for
/// at least this amount of time in order to give the rest of the code the chance to notify us to
/// open substreams.
const INITIAL_KEEPALIVE_TIME: Duration = Duration::from_secs(5);

/// Implements the `IntoProtocolsHandler` trait of libp2p.
///
/// Every time a connection with a remote starts, an instance of this struct is created and
/// sent to a background task dedicated to this connection. Once the connection is established,
/// it is turned into a [`NotifsOutHandler`].
///
/// See the documentation of [`NotifsOutHandler`] for more information.
pub struct NotifsOutHandlerProto {
	/// Name of the protocol to negotiate.
	protocol_name: Cow<'static, str>,
}

impl NotifsOutHandlerProto {
	/// Builds a new [`NotifsOutHandlerProto`]. Will use the given protocol name for the
	/// notifications substream.
	pub fn new(protocol_name: impl Into<Cow<'static, str>>) -> Self {
		NotifsOutHandlerProto {
			protocol_name: protocol_name.into(),
		}
	}
}

impl IntoProtocolsHandler for NotifsOutHandlerProto {
	type Handler = NotifsOutHandler;

	fn inbound_protocol(&self) -> DeniedUpgrade {
		DeniedUpgrade
	}

	fn into_handler(self, _: &PeerId, _: &ConnectedPoint) -> Self::Handler {
		NotifsOutHandler {
			protocol_name: self.protocol_name,
			when_connection_open: Instant::now(),
			state: State::Disabled,
			events_queue: VecDeque::new(),
		}
	}
}

/// Handler for an outbound notification substream.
///
/// When a connection is established, this handler starts in the "disabled" state, meaning that
/// no substream will be open.
///
/// One can try open a substream by sending an [`NotifsOutHandlerIn::Enable`] message to the
/// handler. Once done, the handler will try to establish then maintain an outbound substream with
/// the remote for the purpose of sending notifications to it.
pub struct NotifsOutHandler {
	/// Name of the protocol to negotiate.
	protocol_name: Cow<'static, str>,

	/// Relationship with the node we're connected to.
	state: State,

	/// When the connection with the remote has been successfully established.
	when_connection_open: Instant,

	/// Queue of events to send to the outside.
	///
	/// This queue must only ever be modified to insert elements at the back, or remove the first
	/// element.
	events_queue: VecDeque<ProtocolsHandlerEvent<NotificationsOut, (), NotifsOutHandlerOut, void::Void>>,
}

/// Our relationship with the node we're connected to.
enum State {
	/// The handler is disabled and idle. No substream is open.
	Disabled,

	/// The handler is disabled. A substream is still open and needs to be closed.
	///
	/// > **Important**: Having this state means that `poll_close` has been called at least once,
	/// >				 but the `Sink` API is unclear about whether or not the stream can then
	/// >				 be recovered. Because of that, we must never switch from the
	/// >				 `DisabledOpen` state to the `Open` state while keeping the same substream.
	DisabledOpen(NotificationsOutSubstream<NegotiatedSubstream>),

	/// The handler is disabled but we are still trying to open a substream with the remote.
	///
	/// If the handler gets enabled again, we can immediately switch to `Opening`.
	DisabledOpening,

	/// The handler is enabled and we are trying to open a substream with the remote.
	Opening {
		/// The initial message that we sent. Necessary if we need to re-open a substream.
		initial_message: Vec<u8>,
	},

	/// The handler is enabled. We have tried opening a substream in the past but the remote
	/// refused it.
	Refused,

	/// The handler is enabled and substream is open.
	Open {
		/// Substream that is currently open.
		substream: NotificationsOutSubstream<NegotiatedSubstream>,
		/// Waker for the last task that got `Poll::Pending` from `poll_ready`, to notify
		/// when the open substream closes due to being disabled or encountering an
		/// error, i.e. to notify the task as soon as the substream becomes unavailable,
		/// without waiting for an underlying I/O task wakeup.
		close_waker: Option<Waker>,
		/// The initial message that we sent. Necessary if we need to re-open a substream.
		initial_message: Vec<u8>,
	},

	/// Poisoned state. Shouldn't be found in the wild.
	Poisoned,
}

/// Event that can be received by a `NotifsOutHandler`.
#[derive(Debug)]
pub enum NotifsOutHandlerIn {
	/// Enables the notifications substream for this node. The handler will try to maintain a
	/// substream with the remote.
	Enable {
		/// Initial message to send to remote nodes when we open substreams.
		initial_message: Vec<u8>,
	},

	/// Disables the notifications substream for this node. This is the default state.
	Disable,
}

/// Event that can be emitted by a `NotifsOutHandler`.
#[derive(Debug)]
pub enum NotifsOutHandlerOut {
	/// The notifications substream has been accepted by the remote.
	Open {
		/// Handshake message sent by the remote after we opened the substream.
		handshake: Vec<u8>,
	},

	/// The notifications substream has been closed by the remote.
	Closed,

	/// We tried to open a notifications substream, but the remote refused it.
	///
	/// Can only happen if we're in a closed state.
	Refused,
}

impl NotifsOutHandler {
	/// Returns true if the substream is currently open.
	pub fn is_open(&self) -> bool {
		match &self.state {
			State::Disabled => false,
			State::DisabledOpening => false,
			State::DisabledOpen(_) => true,
			State::Opening { .. } => false,
			State::Refused => false,
			State::Open { .. } => true,
			State::Poisoned => false,
		}
	}

	/// Returns `true` if there has been an attempt to open the substream, but the remote refused
	/// the substream.
	///
	/// Always returns `false` if the handler is in a disabled state.
	pub fn is_refused(&self) -> bool {
		match &self.state {
			State::Disabled => false,
			State::DisabledOpening => false,
			State::DisabledOpen(_) => false,
			State::Opening { .. } => false,
			State::Refused => true,
			State::Open { .. } => false,
			State::Poisoned => false,
		}
	}

	/// Returns the name of the protocol that we negotiate.
	pub fn protocol_name(&self) -> &Cow<'static, str> {
		&self.protocol_name
	}

	/// Polls whether the outbound substream is ready to send a notification.
	///
	/// - Returns `Poll::Pending` if the substream is open but not ready to send a notification.
	/// - Returns `Poll::Ready(true)` if the substream is ready to send a notification.
	/// - Returns `Poll::Ready(false)` if the substream is closed.
	///
	pub fn poll_ready(&mut self, cx: &mut Context) -> Poll<bool> {
		if let State::Open { substream, close_waker, .. } = &mut self.state {
			match substream.poll_ready_unpin(cx) {
				Poll::Ready(Ok(())) => Poll::Ready(true),
				Poll::Ready(Err(_)) => Poll::Ready(false),
				Poll::Pending => {
					*close_waker = Some(cx.waker().clone());
					Poll::Pending
				}
			}
		} else {
			Poll::Ready(false)
		}
	}

	/// Sends out a notification.
	///
	/// If the substream is closed, or not ready to send out a notification yet, then the
	/// notification is silently discarded.
	///
	/// You are encouraged to call [`NotifsOutHandler::poll_ready`] beforehand to determine
	/// whether this will succeed. If `Poll::Ready(true)` is returned, then this method will send
	/// out a notification.
	pub fn send_or_discard(&mut self, notification: Vec<u8>) {
		if let State::Open { substream, .. } = &mut self.state {
			let _ = substream.start_send_unpin(notification);
		}
	}
}

impl ProtocolsHandler for NotifsOutHandler {
	type InEvent = NotifsOutHandlerIn;
	type OutEvent = NotifsOutHandlerOut;
	type Error = void::Void;
	type InboundProtocol = DeniedUpgrade;
	type OutboundProtocol = NotificationsOut;
	type OutboundOpenInfo = ();

	fn listen_protocol(&self) -> SubstreamProtocol<Self::InboundProtocol> {
		SubstreamProtocol::new(DeniedUpgrade)
	}

	fn inject_fully_negotiated_inbound(
		&mut self,
		proto: <Self::InboundProtocol as InboundUpgrade<NegotiatedSubstream>>::Output
	) {
		// We should never reach here. `proto` is a `Void`.
		void::unreachable(proto)
	}

	fn inject_fully_negotiated_outbound(
		&mut self,
		(handshake_msg, substream): <Self::OutboundProtocol as OutboundUpgrade<NegotiatedSubstream>>::Output,
		_: ()
	) {
		match mem::replace(&mut self.state, State::Poisoned) {
			State::Opening { initial_message } => {
				let ev = NotifsOutHandlerOut::Open { handshake: handshake_msg };
				self.events_queue.push_back(ProtocolsHandlerEvent::Custom(ev));
				self.state = State::Open { substream, initial_message, close_waker: None };
			},
			// If the handler was disabled while we were negotiating the protocol, immediately
			// close it.
			State::DisabledOpening => self.state = State::DisabledOpen(substream),

			// Any other situation should never happen.
			State::Disabled | State::Refused | State::Open { .. } | State::DisabledOpen(_) =>
				error!("☎️ State mismatch in notifications handler: substream already open"),
			State::Poisoned => error!("☎️ Notifications handler in a poisoned state"),
		}
	}

	fn inject_event(&mut self, message: NotifsOutHandlerIn) {
		match message {
			NotifsOutHandlerIn::Enable { initial_message } => {
				match mem::replace(&mut self.state, State::Poisoned) {
					State::Disabled => {
						let proto = NotificationsOut::new(self.protocol_name.clone(), initial_message.clone());
						self.events_queue.push_back(ProtocolsHandlerEvent::OutboundSubstreamRequest {
							protocol: SubstreamProtocol::new(proto).with_timeout(OPEN_TIMEOUT),
							info: (),
						});
						self.state = State::Opening { initial_message };
					},
					State::DisabledOpening => self.state = State::Opening { initial_message },
					State::DisabledOpen(mut sub) => {
						// As documented above, in this state we have already called `poll_close`
						// once on the substream, and it is unclear whether the substream can then
						// be recovered. When in doubt, let's drop the existing substream and
						// open a new one.
						if sub.close().now_or_never().is_none() {
							warn!(
								target: "sub-libp2p",
								"📞 Improperly closed outbound notifications substream"
							);
						}

						let proto = NotificationsOut::new(self.protocol_name.clone(), initial_message.clone());
						self.events_queue.push_back(ProtocolsHandlerEvent::OutboundSubstreamRequest {
							protocol: SubstreamProtocol::new(proto).with_timeout(OPEN_TIMEOUT),
							info: (),
						});
						self.state = State::Opening { initial_message };
					},
					st @ State::Opening { .. } | st @ State::Refused | st @ State::Open { .. } => {
						debug!(target: "sub-libp2p",
							"Tried to enable notifications handler that was already enabled");
						self.state = st;
					}
					State::Poisoned => error!("Notifications handler in a poisoned state"),
				}
			}

			NotifsOutHandlerIn::Disable => {
				match mem::replace(&mut self.state, State::Poisoned) {
					st @ State::Disabled | st @ State::DisabledOpen(_) | st @ State::DisabledOpening => {
						debug!(target: "sub-libp2p",
							"Tried to disable notifications handler that was already disabled");
						self.state = st;
					}
					State::Opening { .. } => self.state = State::DisabledOpening,
					State::Refused => self.state = State::Disabled,
					State::Open { substream, close_waker, .. } => {
						if let Some(close_waker) = close_waker {
							close_waker.wake();
						}
						self.state = State::DisabledOpen(substream)
					},
					State::Poisoned => error!("☎️ Notifications handler in a poisoned state"),
				}
			}
		}
	}

	fn inject_dial_upgrade_error(&mut self, _: (), _: ProtocolsHandlerUpgrErr<NotificationsHandshakeError>) {
		match mem::replace(&mut self.state, State::Poisoned) {
			State::Disabled => {},
			State::DisabledOpen(_) | State::Refused | State::Open { .. } =>
				error!("☎️ State mismatch in NotificationsOut"),
			State::Opening { .. } => {
				self.state = State::Refused;
				let ev = NotifsOutHandlerOut::Refused;
				self.events_queue.push_back(ProtocolsHandlerEvent::Custom(ev));
			},
			State::DisabledOpening => self.state = State::Disabled,
			State::Poisoned => error!("☎️ Notifications handler in a poisoned state"),
		}
	}

	fn connection_keep_alive(&self) -> KeepAlive {
		match self.state {
			// We have a small grace period of `INITIAL_KEEPALIVE_TIME` during which we keep the
			// connection open no matter what, in order to avoid closing and reopening
			// connections all the time.
			State::Disabled | State::DisabledOpen(_) | State::DisabledOpening =>
				KeepAlive::Until(self.when_connection_open + INITIAL_KEEPALIVE_TIME),
			State::Opening { .. } | State::Open { .. } => KeepAlive::Yes,
			State::Refused | State::Poisoned => KeepAlive::No,
		}
	}

	fn poll(
		&mut self,
		cx: &mut Context,
	) -> Poll<ProtocolsHandlerEvent<Self::OutboundProtocol, Self::OutboundOpenInfo, Self::OutEvent, Self::Error>> {
		// Flush the events queue if necessary.
		if let Some(event) = self.events_queue.pop_front() {
			return Poll::Ready(event)
		}

		match &mut self.state {
			State::Open { substream, initial_message, close_waker } =>
				match Sink::poll_flush(Pin::new(substream), cx) {
					Poll::Pending | Poll::Ready(Ok(())) => {},
					Poll::Ready(Err(_)) => {
						if let Some(close_waker) = close_waker.take() {
							close_waker.wake();
						}

						// We try to re-open a substream.
						let initial_message = mem::replace(initial_message, Vec::new());
						self.state = State::Opening { initial_message: initial_message.clone() };
						let proto = NotificationsOut::new(self.protocol_name.clone(), initial_message);
						self.events_queue.push_back(ProtocolsHandlerEvent::OutboundSubstreamRequest {
							protocol: SubstreamProtocol::new(proto).with_timeout(OPEN_TIMEOUT),
							info: (),
						});
						return Poll::Ready(ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::Closed));
					}
				},

			State::DisabledOpen(sub) => match Sink::poll_close(Pin::new(sub), cx) {
				Poll::Pending => {},
				Poll::Ready(Ok(())) | Poll::Ready(Err(_)) => {
					self.state = State::Disabled;
					return Poll::Ready(ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::Closed));
				},
			},

			_ => {}
		}

		Poll::Pending
	}
}

impl fmt::Debug for NotifsOutHandler {
	fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
		f.debug_struct("NotifsOutHandler")
			.field("open", &self.is_open())
			.finish()
	}
}
