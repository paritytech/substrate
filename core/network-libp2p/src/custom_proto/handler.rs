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

use crate::custom_proto::upgrade::{CustomMessage, CustomMessageId, RegisteredProtocol};
use crate::custom_proto::upgrade::{RegisteredProtocolEvent, RegisteredProtocolSubstream};
use futures::prelude::*;
use libp2p::core::{
	PeerId, Endpoint, ProtocolsHandler, ProtocolsHandlerEvent,
	protocols_handler::IntoProtocolsHandler,
	protocols_handler::KeepAlive,
	protocols_handler::ProtocolsHandlerUpgrErr,
	upgrade::{InboundUpgrade, OutboundUpgrade}
};
use log::{debug, error, warn};
use smallvec::{smallvec, SmallVec};
use std::{error, fmt, io, marker::PhantomData, mem, time::Duration, time::Instant};
use tokio_io::{AsyncRead, AsyncWrite};
use tokio_timer::Delay;
use void::Void;

/// Implements the `IntoProtocolsHandler` trait of libp2p.
///
/// Every time a connection with a remote starts, an instance of this struct is created and
/// sent to a background task dedicated to this connection. Once the connection is established,
/// it is turned into a `CustomProtoHandler`. It then handles all communications that are specific
/// to Substrate on that connection.
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
		CustomProtoHandler {
			protocol: self.protocol,
			remote_peer_id: remote_peer_id.clone(),
			state: ProtocolState::Init {
				substreams: SmallVec::new(),
				init_deadline: Delay::new(Instant::now() + Duration::from_secs(5))
			},
			events_queue: SmallVec::new(),
			warm_up_end: Instant::now() + Duration::from_secs(5),
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

	/// We have a warm-up period after creating the handler during which we don't shut down the
	/// connection.
	warm_up_end: Instant,
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

impl<TMessage, TSubstream> PerProtocolNormalState<TMessage, TSubstream>
where TMessage: CustomMessage, TSubstream: AsyncRead + AsyncWrite {
	/// Polls for things that are new. Same API constraints as `Future::poll()`.
	/// Optionally returns the event to produce.
	/// You must pass the `protocol_id` as we need have to inject it in the returned event.
	/// API note: Ideally we wouldn't need to be passed a `ProtocolId`, and we would return a
	/// 	different enum that doesn't contain any `protocol_id`, and the caller would inject
	/// 	the ID itself, but that's a ton of code for not much gain.
	fn poll(&mut self) -> Option<CustomProtoHandlerOut<TMessage>> {
		for n in (0..self.pending_response.len()).rev() {
			let (request_id, mut substream) = self.pending_response.swap_remove(n);
			match substream.poll() {
				Ok(Async::Ready(Some(RegisteredProtocolEvent::Message(message)))) => {
					if message.request_id() == CustomMessageId::Response(request_id) {
						let event = CustomProtoHandlerOut::CustomMessage {
							message
						};
						self.shutdown.push(substream);
						return Some(event);
					} else {
						self.shutdown.push(substream);
						let event = CustomProtoHandlerOut::ProtocolError {
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
					let event = CustomProtoHandlerOut::ProtocolError {
						is_severe: false,
						error: format!("Request ID {:?} didn't receive an answer", request_id).into(),
					};
					return Some(event);
				}
				Err(err) => {
					self.shutdown.push(substream);
					let event = CustomProtoHandlerOut::ProtocolError {
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
					return match message.request_id() {
						CustomMessageId::Request(id) => {
							self.pending_send_back.push((id, substream));
							Some(CustomProtoHandlerOut::CustomMessage {
								message
							})
						}
						CustomMessageId::OneWay => {
							self.shutdown.push(substream);
							Some(CustomProtoHandlerOut::CustomMessage {
								message
							})
						}
						_ => {
							self.shutdown.push(substream);
							Some(CustomProtoHandlerOut::ProtocolError {
								is_severe: true,
								error: format!("Received response in new substream").into(),
							})
						}
					}
				},
				Ok(Async::Ready(Some(RegisteredProtocolEvent::Clogged { .. }))) =>
					unreachable!("Cannot receive Clogged message with new protocol version; QED"),
				Ok(Async::NotReady) =>
					self.incoming_substreams.push(substream),
				Ok(Async::Ready(None)) => {}
				Err(err) => {
					self.shutdown.push(substream);
					return Some(CustomProtoHandlerOut::ProtocolError {
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
		/// Reason why the substream closed. If `Ok`, then it's a graceful exit (EOF).
		result: io::Result<()>,
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
							upgrade: self.protocol.clone(),
							info: (),
						});
					}
					ProtocolState::Opening {
						deadline: Delay::new(Instant::now() + Duration::from_secs(60))
					}

				} else if incoming.iter().any(|s| s.is_multiplex()) {
					let event = CustomProtoHandlerOut::CustomProtocolOpen {
						version: incoming[0].protocol_version()
					};
					self.events_queue.push(ProtocolsHandlerEvent::Custom(event));
					ProtocolState::Normal(PerProtocolNormalState {
						outgoing_substream: None,
						incoming_substreams: incoming.into_iter().collect(),
						pending_response: SmallVec::new(),
						pending_send_back: SmallVec::new(),
						pending_messages: SmallVec::new(),
						shutdown: SmallVec::new(),
					})

				} else {
					let event = CustomProtoHandlerOut::CustomProtocolOpen {
						version: incoming[0].protocol_version()
					};
					self.events_queue.push(ProtocolsHandlerEvent::Custom(event));
					ProtocolState::BackCompat {
						substream: incoming.into_iter().next()
							.expect("We have a check above that incoming isn't empty; QED"),
						shutdown: SmallVec::new()
					}
				}
			}

			st @ ProtocolState::Opening { .. } => st,
			st @ ProtocolState::BackCompat { .. } => st,
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

			ProtocolState::Opening { .. } => {
				ProtocolState::Disabled { shutdown: SmallVec::new(), reenable: false }
			}

			ProtocolState::BackCompat { mut substream, mut shutdown } => {
				substream.shutdown();
				shutdown.push(substream);
				let event = CustomProtoHandlerOut::CustomProtocolClosed {
					result: Ok(())
				};
				self.events_queue.push(ProtocolsHandlerEvent::Custom(event));
				ProtocolState::Disabled {
					shutdown: shutdown.into_iter().collect(),
					reenable: false
				}
			}

			ProtocolState::Normal(state) => {
				let mut out: SmallVec<[_; 6]> = SmallVec::new();
				out.extend(state.outgoing_substream.into_iter());
				out.extend(state.incoming_substreams.into_iter());
				out.extend(state.pending_response.into_iter().map(|(_, s)| s));
				out.extend(state.pending_send_back.into_iter().map(|(_, s)| s));
				for s in &mut out {
					s.shutdown();
				}
				out.extend(state.shutdown.into_iter());
				let event = CustomProtoHandlerOut::CustomProtocolClosed {
					result: Ok(())
				};
				self.events_queue.push(ProtocolsHandlerEvent::Custom(event));
				ProtocolState::Disabled { shutdown: out, reenable: false }
			}

			ProtocolState::Disabled { shutdown, .. } =>
				ProtocolState::Disabled { shutdown, reenable: false },
		};
	}

	/// Polls the state for events. Optionally returns an event to produce.
	#[must_use]
	fn poll_state(&mut self)
		-> Option<ProtocolsHandlerEvent<RegisteredProtocol<TMessage>, (), CustomProtoHandlerOut<TMessage>>> {
		let return_value;
		self.state = match mem::replace(&mut self.state, ProtocolState::Poisoned) {
			ProtocolState::Poisoned => {
				error!(target: "sub-libp2p", "Handler with {:?} is in poisoned state",
					self.remote_peer_id);
				return_value = None;
				ProtocolState::Poisoned
			}

			ProtocolState::Init { substreams, mut init_deadline } => {
				match init_deadline.poll() {
					Ok(Async::Ready(())) =>
						error!(target: "sub-libp2p", "Handler initialization process is too long \
							with {:?}", self.remote_peer_id),
					Ok(Async::NotReady) => {}
					Err(_) => error!(target: "sub-libp2p", "Tokio timer has errored")
				}

				return_value = None;
				ProtocolState::Init { substreams, init_deadline }
			}

			ProtocolState::Opening { mut deadline } => {
				match deadline.poll() {
					Ok(Async::Ready(())) => {
						deadline.reset(Instant::now() + Duration::from_secs(60));
						let event = CustomProtoHandlerOut::ProtocolError {
							is_severe: false,
							error: "Timeout when opening protocol".to_string().into(),
						};
						return_value = Some(ProtocolsHandlerEvent::Custom(event));
						ProtocolState::Opening { deadline }
					},
					Ok(Async::NotReady) => {
						return_value = None;
						ProtocolState::Opening { deadline }
					},
					Err(_) => {
						error!(target: "sub-libp2p", "Tokio timer has errored");
						deadline.reset(Instant::now() + Duration::from_secs(60));
						return_value = None;
						ProtocolState::Opening { deadline }
					},
				}
			}

			ProtocolState::BackCompat { mut substream, shutdown } => {
				match substream.poll() {
					Ok(Async::Ready(Some(RegisteredProtocolEvent::Message(message)))) => {
						let event = CustomProtoHandlerOut::CustomMessage {
							message
						};
						return_value = Some(ProtocolsHandlerEvent::Custom(event));
						ProtocolState::BackCompat { substream, shutdown }
					},
					Ok(Async::Ready(Some(RegisteredProtocolEvent::Clogged { messages }))) => {
						let event = CustomProtoHandlerOut::Clogged {
							messages,
						};
						return_value = Some(ProtocolsHandlerEvent::Custom(event));
						ProtocolState::BackCompat { substream, shutdown }
					}
					Ok(Async::NotReady) => {
						return_value = None;
						ProtocolState::BackCompat { substream, shutdown }
					}
					Ok(Async::Ready(None)) => {
						let event = CustomProtoHandlerOut::CustomProtocolClosed {
							result: Ok(())
						};
						return_value = Some(ProtocolsHandlerEvent::Custom(event));
						ProtocolState::Disabled {
							shutdown: shutdown.into_iter().collect(),
							reenable: false
						}
					}
					Err(err) => {
						let event = CustomProtoHandlerOut::CustomProtocolClosed {
							result: Err(err),
						};
						return_value = Some(ProtocolsHandlerEvent::Custom(event));
						ProtocolState::Disabled {
							shutdown: shutdown.into_iter().collect(),
							reenable: false
						}
					}
				}
			}

			ProtocolState::Normal(mut norm_state) => {
				if let Some(event) = norm_state.poll() {
					return_value = Some(ProtocolsHandlerEvent::Custom(event));
				} else {
					return_value = None;
				}

				ProtocolState::Normal(norm_state)
			}

			ProtocolState::Disabled { mut shutdown, reenable } => {
				shutdown_list(&mut shutdown);
				// If `reenable` is `true`, that means we should open the substreams system again
				// after all the substreams are closed.
				if reenable && shutdown.is_empty() {
					return_value = Some(ProtocolsHandlerEvent::OutboundSubstreamRequest {
						upgrade: self.protocol.clone(),
						info: (),
					});
					ProtocolState::Opening {
						deadline: Delay::new(Instant::now() + Duration::from_secs(60))
					}
				} else {
					return_value = None;
					ProtocolState::Disabled { shutdown, reenable }
				}
			}
		};

		return_value
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

				match (substream.endpoint(), substream.is_multiplex()) {
					(Endpoint::Dialer, true) => {
						ProtocolState::Normal(PerProtocolNormalState {
							outgoing_substream: Some(substream),
							incoming_substreams: SmallVec::new(),
							pending_response: SmallVec::new(),
							pending_send_back: SmallVec::new(),
							pending_messages: SmallVec::new(),
							shutdown: SmallVec::new(),
						})
					},
					(Endpoint::Listener, true) => {
						ProtocolState::Normal(PerProtocolNormalState {
							outgoing_substream: None,
							incoming_substreams: smallvec![substream],
							pending_response: SmallVec::new(),
							pending_send_back: SmallVec::new(),
							pending_messages: SmallVec::new(),
							shutdown: SmallVec::new(),
						})
					},
					(_, false) => {
						ProtocolState::BackCompat {
							substream,
							shutdown: SmallVec::new()
						}
					},
				}
			}

			ProtocolState::BackCompat { substream: existing, mut shutdown } => {
				warn!(target: "sub-libp2p", "Received extra substream after having already one \
					open in backwards-compatibility mode with {:?}", self.remote_peer_id);
				substream.shutdown();
				shutdown.push(substream);
				ProtocolState::BackCompat { substream: existing, shutdown }
			}

			ProtocolState::Normal(mut state) => {
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
					debug!(target: "sub-libp2p", "Opened spurious outbound substream with {:?}",
						self.remote_peer_id);
					substream.shutdown();
					state.shutdown.push(substream);
				}

				ProtocolState::Normal(state)
			}

			ProtocolState::Disabled { mut shutdown, .. } => {
				substream.shutdown();
				shutdown.push(substream);
				ProtocolState::Disabled { shutdown, reenable: false }
			}
		};
	}

	/// Sends a message to the remote.
	fn send_message(&mut self, message: TMessage) {
		match self.state {
			ProtocolState::BackCompat { ref mut substream, .. } =>
				substream.send_message(message),

			ProtocolState::Normal(ref mut state) => {
				if let CustomMessageId::Request(request_id) = message.request_id() {
					if let Some(mut outgoing_substream) = state.outgoing_substream.take() {
						outgoing_substream.send_message(message);
						state.pending_response.push((request_id, outgoing_substream));
					} else {
						if state.pending_messages.len() >= 2048 {
							let event = CustomProtoHandlerOut::Clogged {
								messages: Vec::new(),
							};
							self.events_queue.push(ProtocolsHandlerEvent::Custom(event));
						}
						state.pending_messages.push(message);
						self.events_queue.push(ProtocolsHandlerEvent::OutboundSubstreamRequest {
							upgrade: self.protocol.clone(),
							info: ()
						});
					}
				} else if let CustomMessageId::Response(request_id) = message.request_id() {
					if let Some(pos) = state.pending_send_back.iter().position(|(id, _)| *id == request_id) {
						let (_, mut substream) = state.pending_send_back.remove(pos);
						substream.send_message(message);
						state.shutdown.push(substream);
					} else {
						warn!(target: "sub-libp2p", "Libp2p layer received response to a \
							non-existing request ID {:?} with {:?}", request_id, self.remote_peer_id);
					}
				} else if let Some(mut outgoing_substream) = state.outgoing_substream.take() {
					outgoing_substream.send_message(message);
					state.shutdown.push(outgoing_substream);
				} else {
					if state.pending_messages.len() >= 2048 {
						let event = CustomProtoHandlerOut::Clogged {
							messages: Vec::new(),
						};
						self.events_queue.push(ProtocolsHandlerEvent::Custom(event));
					}
					state.pending_messages.push(message);
					self.events_queue.push(ProtocolsHandlerEvent::OutboundSubstreamRequest {
						upgrade: self.protocol.clone(),
						info: ()
					});
				}
			}

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
	type Error = Void;
	type InboundProtocol = RegisteredProtocol<TMessage>;
	type OutboundProtocol = RegisteredProtocol<TMessage>;
	type OutboundOpenInfo = ();

	fn listen_protocol(&self) -> Self::InboundProtocol {
		self.protocol.clone()
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
		if self.warm_up_end >= Instant::now() {
			return KeepAlive::Until(self.warm_up_end)
		}

		let mut keep_forever = false;

		match self.state {
			ProtocolState::Init { .. } | ProtocolState::Opening { .. } => {}
			ProtocolState::BackCompat { .. } | ProtocolState::Normal { .. } =>
				keep_forever = true,
			ProtocolState::Disabled { .. } | ProtocolState::Poisoned => return KeepAlive::Now,
		}

		if keep_forever {
			KeepAlive::Forever
		} else {
			KeepAlive::Now
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
