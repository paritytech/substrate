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

use crate::ProtocolId;
use crate::custom_proto::upgrade::{CustomMessage, CustomMessageId, RegisteredProtocol, RegisteredProtocols};
use crate::custom_proto::upgrade::{RegisteredProtocolEvent, RegisteredProtocolSubstream};
use futures::prelude::*;
use libp2p::core::{
	Endpoint, ProtocolsHandler, ProtocolsHandlerEvent,
	protocols_handler::KeepAlive,
	protocols_handler::ProtocolsHandlerUpgrErr,
	upgrade::{InboundUpgrade, OutboundUpgrade}
};
use log::{debug, error, warn};
use smallvec::{smallvec, SmallVec};
use std::{error, fmt, io, mem, time::Duration, time::Instant};
use tokio_io::{AsyncRead, AsyncWrite};
use tokio_timer::Delay;
use void::Void;

/// Implements the `ProtocolsHandler` trait of libp2p.
///
/// Every time a connection with a remote is established, an instance of this struct is created and
/// sent to a background task dedicated to this connection. It handles all communications that are
/// specific to Substrate.
///
/// Note that there can be multiple instance of this struct simultaneously for same peer. However
/// if that happens, only one main instance can communicate with the outer layers of the code.
///
/// ## How it works
///
/// For backwards compatibility reasons, the behaviour of the handler is quite complicated. After
/// enough nodes have upgraded, it should be simplified by using helpers provided by libp2p.
///
/// When the handler is created, it is initially in the `Init` state and waits for either a
/// `Disable` or an `Enable` message from the outer layer. At any time, the outer layer is free to
/// toggle the handler between the disabled and enabled states.
///
/// When the handler is enabled for the first time, if it is the dialer of the connection, it tries
/// to open a substream. The substream negotiates either a protocol named `/substrate/xxx` or a
/// protocol named `/substrate/multi/xxx`. If it is the former, then we are in
/// "backwards-compatibility mode". If it is the latter, we are in normal operation mode.
///
/// In "backwards-compatibility mode", we have one unique substream where bidirectional
/// communications happen. If the remote closes the substream, we consider that we are now
/// disconnected. Re-enabling is performed by re-opening the substream.
///
/// In normal operation mode, each request gets sent over a different substream where the response
/// is then sent back. If the remote refuses one of our substream open request, or if an error
/// happens on one substream, we consider that we are disconnected. Re-enabling is performed by
/// opening an outbound substream.
///
pub struct CustomProtosHandler<TMessage, TSubstream> {
	/// Fields individual to each protocol that we support.
	protocols: SmallVec<[PerProtocol<TMessage, TSubstream>; 1]>,

	/// Queue of events to send to the outside.
	///
	/// This queue must only ever be modified to insert elements at the back, or remove the first
	/// element.
	events_queue: SmallVec<[ProtocolsHandlerEvent<RegisteredProtocol<TMessage>, ProtocolId, CustomProtosHandlerOut<TMessage>>; 16]>,

	/// We have a warm-up period after creating the handler during which we don't shut down the
	/// connection.
	warm_up_end: Instant,
}

/// Fields individual to each protocol that we support.
struct PerProtocol<TMessage, TSubstream> {
	/// Configuration for the protocol upgrade to negotiate.
	protocol: RegisteredProtocol<TMessage>,

	/// State of the communications with the remote.
	state: PerProtocolState<TMessage, TSubstream>,
}

/// State of the handler for a specific protocol.
enum PerProtocolState<TMessage, TSubstream> {
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

	/// Backwards-compatible mode. Contains the unique substream that is open.
	/// If we are in this state, we have sent a `CustomProtocolOpen` message to the outside.
	BackCompat {
		/// The unique substream where bidirectional communications happen.
		substream: RegisteredProtocolSubstream<TMessage, TSubstream>,
		/// Contains substreams which are being shut down.
		shutdown: SmallVec<[RegisteredProtocolSubstream<TMessage, TSubstream>; 4]>,
	},

	/// Normal functionning. Contains the substreams that are open.
	/// If we are in this state, we have sent a `CustomProtocolOpen` message to the outside.
	Normal(PerProtocolNormalState<TMessage, TSubstream>),

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

	/// We are trying to shut down the connection and thus should refuse any incoming connection.
	/// Contains substreams that are being closed. Once all the substreams are closed, we close
	/// the connection.
	ShuttingDown(SmallVec<[RegisteredProtocolSubstream<TMessage, TSubstream>; 6]>),

	/// We sometimes temporarily switch to this state during processing. If we are in this state
	/// at the beginning of a method, that means something bad happend in the source code.
	Poisoned,
}

/// Normal functionning mode for a protocol.
struct PerProtocolNormalState<TMessage, TSubstream> {
	/// Optional substream that we opened.
	outgoing_substream: Option<RegisteredProtocolSubstream<TMessage, TSubstream>>,

	/// Substreams that have been opened by the remote. We are waiting for a packet from it.
	incoming_substreams: SmallVec<[RegisteredProtocolSubstream<TMessage, TSubstream>; 4]>,

	/// For each request that has been sent to the remote, contains the substream where we
	/// expect a response.
	pending_response: SmallVec<[(u64, RegisteredProtocolSubstream<TMessage, TSubstream>); 4]>,

	/// For each request received by the remote, contains the substream where to send back our
	/// response. Once a response has been sent, the substream closes.
	pending_send_back: SmallVec<[(u64, RegisteredProtocolSubstream<TMessage, TSubstream>); 4]>,

	/// List of messages waiting for a substream to open in order to be sent.
	pending_messages: SmallVec<[TMessage; 6]>,

	/// Contains substreams which are being shut down.
	shutdown: SmallVec<[RegisteredProtocolSubstream<TMessage, TSubstream>; 4]>,
}

impl<TMessage, TSubstream> PerProtocol<TMessage, TSubstream>
where TMessage: CustomMessage, TSubstream: AsyncRead + AsyncWrite {
	/// Enables the protocol. Returns an optional event to emit.
	/// Must be passed the endpoint of the connection.
	#[must_use]
	fn enable(&mut self, endpoint: Endpoint)
		-> Option<ProtocolsHandlerEvent<RegisteredProtocol<TMessage>, ProtocolId, CustomProtosHandlerOut<TMessage>>> {

		let return_value;

		self.state = match mem::replace(&mut self.state, PerProtocolState::Poisoned) {
			PerProtocolState::Poisoned => {
				error!(target: "sub-libp2p", "Handler is in poisoned state");
				return_value = None;
				PerProtocolState::Poisoned
			}

			PerProtocolState::Init { substreams: incoming, .. } => {
				if incoming.is_empty() {
					if let Endpoint::Dialer = endpoint {
						return_value = Some(ProtocolsHandlerEvent::OutboundSubstreamRequest {
							upgrade: self.protocol.clone(),
							info: self.protocol.id(),
						});
					} else {
						return_value = None;
					}
					PerProtocolState::Opening {
						deadline: Delay::new(Instant::now() + Duration::from_secs(60))
					}

				} else if incoming.iter().any(|s| s.is_multiplex()) {
					let event = CustomProtosHandlerOut::CustomProtocolOpen {
						protocol_id: self.protocol.id(),
						version: incoming[0].protocol_version()
					};
					return_value = Some(ProtocolsHandlerEvent::Custom(event));
					PerProtocolState::Normal(PerProtocolNormalState {
						outgoing_substream: None,
						incoming_substreams: incoming.into_iter().collect(),
						pending_response: SmallVec::new(),
						pending_send_back: SmallVec::new(),
						pending_messages: SmallVec::new(),
						shutdown: SmallVec::new(),
					})

				} else {
					let event = CustomProtosHandlerOut::CustomProtocolOpen {
						protocol_id: self.protocol.id(),
						version: incoming[0].protocol_version()
					};
					return_value = Some(ProtocolsHandlerEvent::Custom(event));
					PerProtocolState::BackCompat {
						substream: incoming.into_iter().next()
							.expect("We have a check above that incoming isn't empty; QED"),
						shutdown: SmallVec::new()
					}
				}
			}

			st @ PerProtocolState::Opening { .. } => { return_value = None; st }
			st @ PerProtocolState::BackCompat { .. } => { return_value = None; st }
			st @ PerProtocolState::Normal { .. } => { return_value = None; st }
			PerProtocolState::Disabled { shutdown, .. } => {
				return_value = None;
				PerProtocolState::Disabled { shutdown, reenable: true }
			}
			PerProtocolState::ShuttingDown(list) => {
				return_value = None;
				PerProtocolState::ShuttingDown(list)
			}
		};

		return_value
	}

	/// Disables the protocol. Returns `true` if the protocol was closed, `false` if it was already
	/// closed or not open yet.
	fn disable(&mut self) -> bool {
		let mut return_value = false;

		self.state = match mem::replace(&mut self.state, PerProtocolState::Poisoned) {
			PerProtocolState::Poisoned => {
				error!(target: "sub-libp2p", "Handler is in poisoned state");
				PerProtocolState::Poisoned
			}

			PerProtocolState::Init { substreams: mut shutdown, .. } => {
				for s in &mut shutdown {
					s.shutdown();
				}
				PerProtocolState::Disabled { shutdown, reenable: false }
			}

			PerProtocolState::Opening { .. } => {
				PerProtocolState::Disabled { shutdown: SmallVec::new(), reenable: false }
			}

			PerProtocolState::BackCompat { mut substream, mut shutdown } => {
				substream.shutdown();
				shutdown.push(substream);
				return_value = true;
				PerProtocolState::Disabled {
					shutdown: shutdown.into_iter().collect(),
					reenable: false
				}
			}

			PerProtocolState::Normal(state) => {
				let mut out: SmallVec<[_; 6]> = SmallVec::new();
				out.extend(state.outgoing_substream.into_iter());
				out.extend(state.incoming_substreams.into_iter());
				out.extend(state.pending_response.into_iter().map(|(_, s)| s));
				out.extend(state.pending_send_back.into_iter().map(|(_, s)| s));
				for s in &mut out {
					s.shutdown();
				}
				out.extend(state.shutdown.into_iter());
				return_value = true;
				PerProtocolState::Disabled { shutdown: out, reenable: false }
			}

			PerProtocolState::Disabled { shutdown, .. } =>
				PerProtocolState::Disabled { shutdown, reenable: false },
			PerProtocolState::ShuttingDown(list) =>
				PerProtocolState::ShuttingDown(list),
		};

		return_value
	}

	/// Shuts down all the substream. Returns `true` if the protocol was closed, `false` if it was
	/// already closed or not open yet.
	fn shutdown(&mut self) -> bool {
		let mut return_value = false;
		self.state = match mem::replace(&mut self.state, PerProtocolState::Poisoned) {
			PerProtocolState::Poisoned => {
				error!(target: "sub-libp2p", "Handler is in poisoned state");
				PerProtocolState::Poisoned
			}

			PerProtocolState::Init { substreams: mut list, .. } => {
				for s in &mut list { s.shutdown(); }
				PerProtocolState::ShuttingDown(list)
			}

			PerProtocolState::Opening { .. } => {
				PerProtocolState::ShuttingDown(SmallVec::new())
			}

			PerProtocolState::BackCompat { mut substream, mut shutdown } => {
				substream.shutdown();
				shutdown.push(substream);
				return_value = true;
				PerProtocolState::ShuttingDown(shutdown.into_iter().collect())
			}

			PerProtocolState::Normal(state) => {
				let mut out: SmallVec<[_; 6]> = SmallVec::new();
				out.extend(state.outgoing_substream.into_iter());
				out.extend(state.incoming_substreams.into_iter());
				out.extend(state.pending_response.into_iter().map(|(_, s)| s));
				out.extend(state.pending_send_back.into_iter().map(|(_, s)| s));
				for s in &mut out {
					s.shutdown();
				}
				out.extend(state.shutdown.into_iter());
				return_value = true;
				PerProtocolState::ShuttingDown(out)
			}

			PerProtocolState::Disabled { shutdown, .. } =>
				PerProtocolState::ShuttingDown(shutdown),
			PerProtocolState::ShuttingDown(list) =>
				PerProtocolState::ShuttingDown(list),
		};
		return_value
	}

	/// Polls the state for events. Optionally returns an event to produce.
	#[must_use]
	fn poll(&mut self)
		-> Option<ProtocolsHandlerEvent<RegisteredProtocol<TMessage>, ProtocolId, CustomProtosHandlerOut<TMessage>>> {

		let return_value;
		self.state = match mem::replace(&mut self.state, PerProtocolState::Poisoned) {
			PerProtocolState::Poisoned => {
				error!(target: "sub-libp2p", "Handler is in poisoned state; shutting down");
				return_value = Some(ProtocolsHandlerEvent::Shutdown);
				PerProtocolState::Poisoned
			}

			PerProtocolState::Init { substreams, mut init_deadline } => {
				match init_deadline.poll() {
					Ok(Async::Ready(())) =>
						error!(target: "sub-libp2p", "Handler initialization process is too long"),
					Ok(Async::NotReady) => {}
					Err(_) => error!(target: "sub-libp2p", "Tokio timer has errored")
				}

				return_value = None;
				PerProtocolState::Init { substreams, init_deadline }
			}

			PerProtocolState::Opening { mut deadline } => {
				match deadline.poll() {
					Ok(Async::Ready(())) => {
						deadline.reset(Instant::now() + Duration::from_secs(60));
						let event = CustomProtosHandlerOut::ProtocolError {
							protocol_id: self.protocol.id(),
							is_severe: false,
							error: "Timeout when opening protocol".to_string().into(),
						};
						return_value = Some(ProtocolsHandlerEvent::Custom(event));
						PerProtocolState::Opening { deadline }
					},
					Ok(Async::NotReady) => {
						return_value = None;
						PerProtocolState::Opening { deadline }
					},
					Err(_) => {
						error!(target: "sub-libp2p", "Tokio timer has errored");
						deadline.reset(Instant::now() + Duration::from_secs(60));
						return_value = None;
						PerProtocolState::Opening { deadline }
					},
				}
			}

			PerProtocolState::BackCompat { mut substream, shutdown } => {
				match substream.poll() {
					Ok(Async::Ready(Some(RegisteredProtocolEvent::Message(message)))) => {
						let event = CustomProtosHandlerOut::CustomMessage {
							protocol_id: substream.protocol_id(),
							message
						};
						return_value = Some(ProtocolsHandlerEvent::Custom(event));
						PerProtocolState::BackCompat { substream, shutdown }
					},
					Ok(Async::Ready(Some(RegisteredProtocolEvent::Clogged { messages }))) => {
						let event = CustomProtosHandlerOut::Clogged {
							protocol_id: substream.protocol_id(),
							messages,
						};
						return_value = Some(ProtocolsHandlerEvent::Custom(event));
						PerProtocolState::BackCompat { substream, shutdown }
					}
					Ok(Async::NotReady) => {
						return_value = None;
						PerProtocolState::BackCompat { substream, shutdown }
					}
					Ok(Async::Ready(None)) => {
						let event = CustomProtosHandlerOut::CustomProtocolClosed {
							protocol_id: substream.protocol_id(),
							result: Ok(())
						};
						return_value = Some(ProtocolsHandlerEvent::Custom(event));
						PerProtocolState::Disabled {
							shutdown: shutdown.into_iter().collect(),
							reenable: false
						}
					}
					Err(err) => {
						let event = CustomProtosHandlerOut::CustomProtocolClosed {
							protocol_id: substream.protocol_id(),
							result: Err(err),
						};
						return_value = Some(ProtocolsHandlerEvent::Custom(event));
						PerProtocolState::Disabled {
							shutdown: shutdown.into_iter().collect(),
							reenable: false
						}
					}
				}
			}

			PerProtocolState::Normal(mut norm_state) => {
				if let Some(event) = norm_state.poll(self.protocol.id()) {
					return_value = Some(ProtocolsHandlerEvent::Custom(event));
				} else {
					return_value = None;
				}

				PerProtocolState::Normal(norm_state)
			}

			PerProtocolState::Disabled { mut shutdown, reenable } => {
				shutdown_list(&mut shutdown);
				// If `reenable` is `true`, that means we should open the substreams system again
				// after all the substreams are closed.
				if reenable && shutdown.is_empty() {
					return_value = Some(ProtocolsHandlerEvent::OutboundSubstreamRequest {
						upgrade: self.protocol.clone(),
						info: self.protocol.id(),
					});
					PerProtocolState::Opening {
						deadline: Delay::new(Instant::now() + Duration::from_secs(60))
					}
				} else {
					return_value = None;
					PerProtocolState::Disabled { shutdown, reenable }
				}
			}

			PerProtocolState::ShuttingDown(mut list) => {
				shutdown_list(&mut list);
				return_value = None;
				PerProtocolState::ShuttingDown(list)
			}
		};

		return_value
	}
}

impl<TMessage, TSubstream> PerProtocolNormalState<TMessage, TSubstream>
where TMessage: CustomMessage, TSubstream: AsyncRead + AsyncWrite {
	/// Polls for things that are new. Same API constraints as `Future::poll()`.
	/// Optionally returns the event to produce.
	/// You must pass the `protocol_id` as we need have to inject it in the returned event.
	/// API note: Ideally we wouldn't need to be passed a `ProtocolId`, and we would return a
	/// 	different enum that doesn't contain any `protocol_id`, and the caller would inject
	/// 	the ID itself, but that's a ton of code for not much gain.
	fn poll(&mut self, protocol_id: ProtocolId) -> Option<CustomProtosHandlerOut<TMessage>> {
		for n in (0..self.pending_response.len()).rev() {
			let (request_id, mut substream) = self.pending_response.swap_remove(n);
			match substream.poll() {
				Ok(Async::Ready(Some(RegisteredProtocolEvent::Message(message)))) => {
					if message.request_id() == CustomMessageId::Response(request_id) {
						let event = CustomProtosHandlerOut::CustomMessage {
							protocol_id: substream.protocol_id(),
							message
						};
						self.shutdown.push(substream);
						return Some(event);
					} else {
						self.shutdown.push(substream);
						let event = CustomProtosHandlerOut::ProtocolError {
							protocol_id,
							is_severe: true,
							error: format!("Request ID doesn't match substream: expected {:?}, \
								got {:?}", request_id, message.request_id()).into(),
						};
						return Some(event);
					}
				},
				Ok(Async::Ready(Some(RegisteredProtocolEvent::Clogged { .. }))) =>
					unreachable!("Cannot receive Clogged message with new protocol version; QED"),
				Ok(Async::NotReady) =>
					self.pending_response.push((request_id, substream)),
				Ok(Async::Ready(None)) => {
					self.shutdown.push(substream);
					let event = CustomProtosHandlerOut::ProtocolError {
						protocol_id,
						is_severe: false,
						error: format!("Request ID {:?} didn't receive an answer", request_id).into(),
					};
					return Some(event);
				}
				Err(err) => {
					self.shutdown.push(substream);
					let event = CustomProtosHandlerOut::ProtocolError {
						protocol_id,
						is_severe: false,
						error: format!("Error while waiting for an answer for {:?}: {}",
							request_id, err).into(),
					};
					return Some(event);
				}
			}
		}

		for n in (0..self.incoming_substreams.len()).rev() {
			let mut substream = self.incoming_substreams.swap_remove(n);
			match substream.poll() {
				Ok(Async::Ready(Some(RegisteredProtocolEvent::Message(message)))) => {
					let protocol_id = substream.protocol_id();
					if let CustomMessageId::Request(id) = message.request_id() {
						self.pending_send_back.push((id, substream));
						return Some(CustomProtosHandlerOut::CustomMessage {
							protocol_id,
							message
						});
					} else if let CustomMessageId::OneWay = message.request_id() {
						self.shutdown.push(substream);
						return Some(CustomProtosHandlerOut::CustomMessage {
							protocol_id,
							message
						});
					} else {
						self.shutdown.push(substream);
						return Some(CustomProtosHandlerOut::ProtocolError {
							protocol_id,
							is_severe: true,
							error: format!("Received response in new substream").into(),
						});
					}
				},
				Ok(Async::Ready(Some(RegisteredProtocolEvent::Clogged { .. }))) =>
					unreachable!("Cannot receive Clogged message with new protocol version; QED"),
				Ok(Async::NotReady) =>
					self.incoming_substreams.push(substream),
				Ok(Async::Ready(None)) => {}
				Err(err) => {
					self.shutdown.push(substream);
					return Some(CustomProtosHandlerOut::ProtocolError {
						protocol_id,
						is_severe: false,
						error: format!("Error in incoming substream: {}", err).into(),
					});
				}
			}
		}

		shutdown_list(&mut self.shutdown);
		None
	}
}

/// Event that can be received by a `CustomProtosHandler`.
#[derive(Debug)]
pub enum CustomProtosHandlerIn<TMessage> {
	/// The node should start using custom protocols. Contains whether we are the dialer or the
	/// listener of the connection.
	Enable(Endpoint),

	/// The node should stop using custom protocols.
	Disable,

	/// Sends a message through a custom protocol substream.
	SendCustomMessage {
		/// The protocol to use.
		protocol: ProtocolId,
		/// The message to send.
		message: TMessage,
	},
}

/// Event that can be emitted by a `CustomProtosHandler`.
#[derive(Debug)]
pub enum CustomProtosHandlerOut<TMessage> {
	/// Opened a custom protocol with the remote.
	CustomProtocolOpen {
		/// Identifier of the protocol.
		protocol_id: ProtocolId,
		/// Version of the protocol that has been opened.
		version: u8,
	},

	/// Closed a custom protocol with the remote.
	CustomProtocolClosed {
		/// Identifier of the protocol.
		protocol_id: ProtocolId,
		/// Reason why the substream closed. If `Ok`, then it's a graceful exit (EOF).
		result: io::Result<()>,
	},

	/// Receives a message on a custom protocol substream.
	CustomMessage {
		/// Protocol which generated the message.
		protocol_id: ProtocolId,
		/// Message that has been received.
		message: TMessage,
	},

	/// A substream to the remote is clogged. The send buffer is very large, and we should print
	/// a diagnostic message and/or avoid sending more data.
	Clogged {
		/// Protocol which is clogged.
		protocol_id: ProtocolId,
		/// Copy of the messages that are within the buffer, for further diagnostic.
		messages: Vec<TMessage>,
	},

	/// An error has happened on the protocol level with this node.
	ProtocolError {
		/// Protocol for which the error happened.
		protocol_id: ProtocolId,
		/// If true the error is severe, such as a protocol violation.
		is_severe: bool,
		/// The error that happened.
		error: Box<dyn error::Error + Send + Sync>,
	},
}

impl<TMessage, TSubstream> CustomProtosHandler<TMessage, TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
	TMessage: CustomMessage,
{
	/// Builds a new `CustomProtosHandler`.
	pub fn new(protocols: RegisteredProtocols<TMessage>) -> Self {
		CustomProtosHandler {
			protocols: protocols.0.into_iter().map(|protocol| {
				PerProtocol {
					protocol,
					state: PerProtocolState::Init {
						substreams: SmallVec::new(),
						init_deadline: Delay::new(Instant::now() + Duration::from_secs(5))
					},
				}
			}).collect(),
			events_queue: SmallVec::new(),
			warm_up_end: Instant::now() + Duration::from_secs(5),
		}
	}

	/// Enables the handler for all protocols.
	fn enable(&mut self, endpoint: Endpoint) {
		for protocol in &mut self.protocols {
			if let Some(message) = protocol.enable(endpoint) {
				self.events_queue.push(message);
			}
		}
	}

	/// Disables the handler for all protocols.
	fn disable(&mut self) {
		for protocol in &mut self.protocols {
			if protocol.disable() {
				let event = CustomProtosHandlerOut::CustomProtocolClosed {
					protocol_id: protocol.protocol.id(),
					result: Ok(())
				};
				self.events_queue.push(ProtocolsHandlerEvent::Custom(event));
			}
		}
	}

	/// Called by `inject_fully_negotiated_inbound` and `inject_fully_negotiated_outbound`.
	fn inject_fully_negotiated(
		&mut self,
		mut substream: RegisteredProtocolSubstream<TMessage, TSubstream>
	) {
		let state = match self.protocols.iter_mut().find(|p| p.protocol.id() == substream.protocol_id()) {
			Some(p) => &mut p.state,
			None => {
				error!(target: "sub-libp2p", "Found unknown protocol ID {:?}",
					substream.protocol_id());
				return
			},
		};

		*state = match mem::replace(state, PerProtocolState::Poisoned) {
			PerProtocolState::Poisoned => {
				error!(target: "sub-libp2p", "Handler is in poisoned state");
				PerProtocolState::Poisoned
			}

			PerProtocolState::Init { mut substreams, init_deadline } => {
				if substream.endpoint() == Endpoint::Dialer {
					error!(target: "sub-libp2p", "Opened dialing substream before initialization");
				}
				substreams.push(substream);
				PerProtocolState::Init { substreams, init_deadline }
			}

			PerProtocolState::Opening { .. } => {
				let event = CustomProtosHandlerOut::CustomProtocolOpen {
					protocol_id: substream.protocol_id(),
					version: substream.protocol_version()
				};
				self.events_queue.push(ProtocolsHandlerEvent::Custom(event));

				match (substream.endpoint(), substream.is_multiplex()) {
					(Endpoint::Dialer, true) => {
						PerProtocolState::Normal(PerProtocolNormalState {
							outgoing_substream: Some(substream),
							incoming_substreams: SmallVec::new(),
							pending_response: SmallVec::new(),
							pending_send_back: SmallVec::new(),
							pending_messages: SmallVec::new(),
							shutdown: SmallVec::new(),
						})
					},
					(Endpoint::Listener, true) => {
						PerProtocolState::Normal(PerProtocolNormalState {
							outgoing_substream: None,
							incoming_substreams: smallvec![substream],
							pending_response: SmallVec::new(),
							pending_send_back: SmallVec::new(),
							pending_messages: SmallVec::new(),
							shutdown: SmallVec::new(),
						})
					},
					(_, false) => {
						PerProtocolState::BackCompat {
							substream,
							shutdown: SmallVec::new()
						}
					},
				}
			}

			PerProtocolState::BackCompat { substream: existing, mut shutdown } => {
				warn!(target: "sub-libp2p", "Received extra substream after having already one \
					open in backwards-compatibility mode");
				substream.shutdown();
				shutdown.push(substream);
				PerProtocolState::BackCompat { substream: existing, shutdown }
			}

			PerProtocolState::Normal(mut state) => {
				if substream.endpoint() == Endpoint::Listener {
					state.incoming_substreams.push(substream);
				} else if !state.pending_messages.is_empty() {
					let message = state.pending_messages.remove(0);
					let request_id = message.request_id();
					substream.send_message(message);
					if let CustomMessageId::Request(request_id) = request_id {
						state.pending_response.push((request_id, substream));
					} else {
						state.shutdown.push(substream);
					}
				} else {
					debug!(target: "sub-libp2p", "Opened spurious outbound substream");
					substream.shutdown();
					state.shutdown.push(substream);
				}

				PerProtocolState::Normal(state)
			}

			PerProtocolState::Disabled { mut shutdown, .. } => {
				substream.shutdown();
				shutdown.push(substream);
				PerProtocolState::Disabled { shutdown, reenable: false }
			}

			PerProtocolState::ShuttingDown(mut list) => {
				substream.shutdown();
				list.push(substream);
				PerProtocolState::ShuttingDown(list)
			}
		};
	}

	/// Sends a message to the remote.
	fn send_message(&mut self, protocol: ProtocolId, message: TMessage) {
		let (protocol, state) = match self.protocols.iter_mut().find(|p| p.protocol.id() == protocol) {
			Some(p) => (&mut p.protocol, &mut p.state),
			None => {
				error!(target: "sub-libp2p", "Tried to send message over unknown protocol ID {:?}",
					protocol);
				return
			},
		};

		match *state {
			PerProtocolState::BackCompat { ref mut substream, .. } =>
				substream.send_message(message),

			PerProtocolState::Normal(ref mut state) => {
				if let CustomMessageId::Request(request_id) = message.request_id() {
					if let Some(mut outgoing_substream) = state.outgoing_substream.take() {
						outgoing_substream.send_message(message);
						state.pending_response.push((request_id, outgoing_substream));
					} else {
						if state.pending_messages.len() >= 2048 {
							let event = CustomProtosHandlerOut::Clogged {
								messages: Vec::new(),
								protocol_id: protocol.id()
							};
							self.events_queue.push(ProtocolsHandlerEvent::Custom(event));
						}
						state.pending_messages.push(message);
						self.events_queue.push(ProtocolsHandlerEvent::OutboundSubstreamRequest {
							upgrade: protocol.clone(),
							info: protocol.id()
						});
					}
				} else if let CustomMessageId::Response(request_id) = message.request_id() {
					if let Some(pos) = state.pending_send_back.iter().position(|(id, _)| *id == request_id) {
						let (_, mut substream) = state.pending_send_back.remove(pos);
						substream.send_message(message);
						state.shutdown.push(substream);
					} else {
						warn!(target: "sub-libp2p", "Libp2p layer received response to a \
							non-existing request ID {:?}", request_id);
					}
				} else if let Some(mut outgoing_substream) = state.outgoing_substream.take() {
					outgoing_substream.send_message(message);
					state.shutdown.push(outgoing_substream);
				} else {
					if state.pending_messages.len() >= 2048 {
						let event = CustomProtosHandlerOut::Clogged {
							messages: Vec::new(),
							protocol_id: protocol.id()
						};
						self.events_queue.push(ProtocolsHandlerEvent::Custom(event));
					}
					state.pending_messages.push(message);
					self.events_queue.push(ProtocolsHandlerEvent::OutboundSubstreamRequest {
						upgrade: protocol.clone(),
						info: protocol.id()
					});
				}
			}

			_ => debug!(target: "sub-libp2p", "Tried to send message over closed protocol")
		}
	}
}

impl<TMessage, TSubstream> ProtocolsHandler for CustomProtosHandler<TMessage, TSubstream>
where TSubstream: AsyncRead + AsyncWrite, TMessage: CustomMessage {
	type InEvent = CustomProtosHandlerIn<TMessage>;
	type OutEvent = CustomProtosHandlerOut<TMessage>;
	type Substream = TSubstream;
	type Error = Void;
	type InboundProtocol = RegisteredProtocols<TMessage>;
	type OutboundProtocol = RegisteredProtocol<TMessage>;
	type OutboundOpenInfo = ProtocolId;

	#[inline]
	fn listen_protocol(&self) -> Self::InboundProtocol {
		RegisteredProtocols(self.protocols.iter().map(|p| p.protocol.clone()).collect())
	}

	fn inject_fully_negotiated_inbound(
		&mut self,
		proto: <Self::InboundProtocol as InboundUpgrade<TSubstream>>::Output
	) {
		self.inject_fully_negotiated(proto);
	}

	#[inline]
	fn inject_fully_negotiated_outbound(
		&mut self,
		proto: <Self::OutboundProtocol as OutboundUpgrade<TSubstream>>::Output,
		_: Self::OutboundOpenInfo
	) {
		self.inject_fully_negotiated(proto);
	}

	fn inject_event(&mut self, message: CustomProtosHandlerIn<TMessage>) {
		match message {
			CustomProtosHandlerIn::Disable => self.disable(),
			CustomProtosHandlerIn::Enable(endpoint) => self.enable(endpoint),
			CustomProtosHandlerIn::SendCustomMessage { protocol, message } =>
				self.send_message(protocol, message),
		}
	}

	#[inline]
	fn inject_inbound_closed(&mut self) {}

	#[inline]
	fn inject_dial_upgrade_error(&mut self, protocol_id: Self::OutboundOpenInfo, err: ProtocolsHandlerUpgrErr<io::Error>) {
		let is_severe = match err {
			ProtocolsHandlerUpgrErr::Upgrade(_) => true,
			_ => false,
		};

		self.events_queue.push(ProtocolsHandlerEvent::Custom(CustomProtosHandlerOut::ProtocolError {
			protocol_id,
			is_severe,
			error: Box::new(err),
		}));

		// If we failed to open a substream, there is little chance that we manage to open any
		// other substream ever again on this connection, and thus we disable the handler.
		self.disable();
	}

	fn connection_keep_alive(&self) -> KeepAlive {
		if self.warm_up_end >= Instant::now() {
			return KeepAlive::Until(self.warm_up_end)
		}

		let mut keep_forever = false;

		for protocol in self.protocols.iter() {
			match protocol.state {
				PerProtocolState::Init { .. } | PerProtocolState::Opening { .. } => {}
				PerProtocolState::BackCompat { .. } | PerProtocolState::Normal { .. } =>
					keep_forever = true,
				PerProtocolState::Disabled { .. } | PerProtocolState::ShuttingDown(_) |
				PerProtocolState::Poisoned => return KeepAlive::Now,
			}
		}

		if keep_forever {
			KeepAlive::Forever
		} else {
			KeepAlive::Now
		}
	}

	fn shutdown(&mut self) {
		for protocol in &mut self.protocols {
			if protocol.shutdown() {
				let event = CustomProtosHandlerOut::CustomProtocolClosed {
					protocol_id: protocol.protocol.id(),
					result: Ok(())
				};
				self.events_queue.push(ProtocolsHandlerEvent::Custom(event));
			}
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

		// Process all the substreams.
		for protocol in self.protocols.iter_mut() {
			if let Some(event) = protocol.poll() {
				return Ok(Async::Ready(event))
			}
		}

		// Shut down the node if everything is closed.
		let can_shut_down = self.protocols.iter().all(|p|
			match p.state {
				PerProtocolState::ShuttingDown(ref list) if list.is_empty() => true,
				_ => false
			});
		if can_shut_down {
			return Ok(Async::Ready(ProtocolsHandlerEvent::Shutdown))
		}

		Ok(Async::NotReady)
	}
}

impl<TMessage, TSubstream> fmt::Debug for CustomProtosHandler<TMessage, TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
{
	fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
		f.debug_struct("CustomProtosHandler")
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
