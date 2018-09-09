// Copyright 2018 Parity Technologies (UK) Ltd.
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

use bytes::Bytes;
use custom_proto::{RegisteredProtocols, RegisteredProtocolOutput};
use futures::{prelude::*, future, task};
use libp2p::core::{ConnectionUpgrade, Endpoint, PeerId, PublicKey, upgrade};
use libp2p::kad::{KadConnecConfig, KadFindNodeRespond, KadIncomingRequest, KadConnecController};
use libp2p::{identify, ping};
use parking_lot::Mutex;
use std::error::Error;
use std::io::{Error as IoError, ErrorKind as IoErrorKind};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio_io::{AsyncRead, AsyncWrite};
use tokio_timer::{Delay, Interval, Timeout, timeout::Error as TimeoutError};
use {Multiaddr, PacketId, ProtocolId};

/// Duration after which we consider that a ping failed.
const PING_TIMEOUT: Duration = Duration::from_secs(30);
/// After a ping succeeded, wait this long before the next ping.
const DELAY_TO_NEXT_PING: Duration = Duration::from_secs(15);
/// Period at which we identify the remote.
const PERIOD_IDENTIFY: Duration = Duration::from_secs(5 * 60);
/// Delay between the moment we connect and the first time we ping.
const DELAY_TO_FIRST_PING: Duration = Duration::from_secs(5);
/// Delay between the moment we connect and the first time we identify.
const DELAY_TO_FIRST_IDENTIFY: Duration = Duration::from_secs(2);

/// This struct handles the open substreams of a specific node.
///
/// It doesn't handle opening the substreams, but only what to do with substreams that have been
/// opened.
///
/// The node will be pinged at a regular interval to determine whether it's still alive. We will
/// also regularly query the remote for identification information, for statistics purposes.
pub struct NodeHandler<TSubstream, TUserData> {
	/// List of registered custom protocols.
	registered_custom: Arc<RegisteredProtocols<TUserData>>,
	/// Substreams open for "custom" protocols (eg. dot).
	custom_protocols_substreams: Vec<RegisteredProtocolOutput<TUserData>>,

	/// Substream open for Kademlia, if any.
	kademlia_substream: Option<(KadConnecController, Box<Stream<Item = KadIncomingRequest, Error = IoError> + Send>)>,

	/// Substream open for sending pings, if any.
	ping_out_substream: Option<(ping::Pinger, Box<Future<Item = (), Error = IoError> + Send>)>,
	/// Active pinging attempt. Includes the moment when we started the ping.
	active_ping_out: Option<(Instant, Box<Future<Item = (), Error = TimeoutError<Box<Error + Send + Sync>>> + Send>)>,
	/// Substreams open for receiving pings.
	ping_in_substreams: Vec<Box<Future<Item = (), Error = IoError> + Send>>,
	/// Future that fires when we need to ping the node again.
	///
	/// Every time we receive a pong, we reset the timer to the next time.
	next_ping: Delay,

	/// Substreams for sending back our identify info to the remote.
	///
	/// This is in an `Arc` in order to avoid borrowing issues with the future.
	identify_send_back: Arc<Mutex<Vec<Box<Future<Item = (), Error = IoError> + Send>>>>,
	/// Stream that fires when we need to identify the node again.
	next_identify: Interval,

	/// Substreams being upgraded on the listening side.
	upgrades_in_progress_listen: Vec<Box<Future<Item = FinalUpgrade<TSubstream, TUserData>, Error = IoError> + Send>>,
	/// Substreams being upgraded on the dialing side. Contrary to `upgrades_in_progress_listen`,
	/// these have a known purpose.
	upgrades_in_progress_dial: Vec<(UpgradePurpose, Box<Future<Item = FinalUpgrade<TSubstream, TUserData>, Error = IoError> + Send>)>,
	/// The substreams we want to open.
	queued_dial_upgrades: Vec<UpgradePurpose>,
	/// Number of outbound substreams that the user should open.
	/// While this is non-zero, polling the handler will produce `OutboundSubstreamRequested`.
	num_out_user_must_open: usize,

	/// Task to notify if we add an element to one of the lists from the public API.
	to_notify: Option<task::Task>,
}

/// Purpose of an upgrade in progress on the dialing side.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum UpgradePurpose {
	Custom(ProtocolId),
	Kad,
	Identify,
	Ping,
}

/// Event that can happen on the `NodeHandler`.
pub enum NodeEvent<TSubstream> {
	/// The node has been determined to be unresponsive.
	Unresponsive,

	/// The node works but we can't do anything useful with it.
	Useless,

	/// Started pinging the remote. This can be used to print a diagnostic message in the logs.
	PingStart,

	/// The node has successfully responded to a ping.
	PingSuccess(Duration),

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
		result: Result<(), IoError>,
	},

	/// Receives a message on a custom protocol substream.
	CustomMessage {
		/// Protocol which generated the message.
		protocol_id: ProtocolId,
		/// Identifier of the packet.
		packet_id: u8,
		/// Data that has been received.
		data: Bytes,
	},

	/// We obtained identification information from the remote
	Identified {
		/// Information of the remote.
		info: identify::IdentifyInfo,
		/// Address the remote observes us as.
		observed_addr: Multiaddr,
	},

	/// The remote wants us to send back identification information.
	///
	/// The `IdentificationRequest` object should be used to send the information.
	IdentificationRequest(IdentificationRequest<TSubstream>),

	/// The emitter wants a new outbound substream to be opened.
	///
	/// In the future, the user should answer that request by calling `inject_substream` with
	/// `endpoint` set to `Dialer`.
	/// If multiple such events are produced, the user should open a new substream once per event.
	OutboundSubstreamRequested,

	/// Opened a Kademlia substream with the node.
	KadOpen(KadConnecController),

	/// The remote wants us to answer a Kademlia `FIND_NODE` request.
	///
	/// The `responder` should be used to answer that query.
	// TODO: this API with the "responder" is bad, but changing it requires modifications in libp2p
	KadFindNode {
		/// The value being searched.
		searched: PeerId,
		/// Object to use to respond to the request.
		responder: KadFindNodeRespond,
	},

	/// The Kademlia substream has been closed.
	///
	/// The parameter contains the reason why it has been closed. `Ok` means that it's been closed
	/// gracefully.
	KadClosed(Result<(), IoError>),

	/// An error happened while upgrading a substream.
	///
	/// This can be used to print a diagnostic message.
	SubstreamUpgradeFail(IoError),
}

/// The remote wants us to send back information.
pub struct IdentificationRequest<TSubstream> {
	/// Where to store the future that sends back the information.
	identify_send_back: Arc<Mutex<Vec<Box<Future<Item = (), Error = IoError> + Send>>>>,
	/// Object that sends back the information.
	sender: identify::IdentifySender<TSubstream>,
	/// Protocol names that we support, to send back.
	protocols: Vec<String>,
}

impl<TSubstream> IdentificationRequest<TSubstream> {
	/// Responds to the request.
	///
	/// - `local_key` must contain our local public key.
	/// - `listen_addrs` must contain the list of addresses we're listening on (preferably after
	///	  NAT traversal).
	/// - `remote_addr` must be the address of the remote from our local point of view.
	///
	pub fn respond(
		self,
		local_key: PublicKey,
		listen_addrs: Vec<Multiaddr>,
		remote_addr: &Multiaddr
	) where TSubstream: AsyncRead + AsyncWrite + Send + 'static {
		// TODO: what to return for `protocol_version` and `agent_version`?
		let sender = self.sender.send(
			identify::IdentifyInfo {
				public_key: local_key,
				protocol_version: concat!("substrate/", env!("CARGO_PKG_VERSION")).to_owned(),
				agent_version: concat!("substrate/", env!("CARGO_PKG_VERSION")).to_owned(),
				listen_addrs,
				protocols: self.protocols,
			},
			remote_addr
		);

		self.identify_send_back.lock().push(sender);
	}
}

/// Ideally we would have a method on `NodeHandler` that builds this type, but in practice it's a
/// bit tedious to express, even with the `impl Trait` syntax.
/// Therefore we simply use a macro instead.
macro_rules! listener_upgrade {
	($self:expr) => (
		upgrade::or(upgrade::or(upgrade::or(
			upgrade::map((*$self.registered_custom).clone(), move |c| FinalUpgrade::Custom(c)),
			upgrade::map(KadConnecConfig::new(), move |(c, s)| FinalUpgrade::Kad(c, s))),
			upgrade::map(ping::Ping, move |p| FinalUpgrade::from(p))),
			upgrade::map(identify::IdentifyProtocolConfig, move |i| FinalUpgrade::from(i)))
			// TODO: meh for cloning a Vec here
	)
}

impl<TSubstream, TUserData> NodeHandler<TSubstream, TUserData>
where TSubstream: AsyncRead + AsyncWrite + Send + 'static,
	  TUserData: Clone + Send + 'static,
{
	/// Creates a new node handler.
	#[inline]
	pub fn new(registered_custom: Arc<RegisteredProtocols<TUserData>>) -> Self {
		let registered_custom_len = registered_custom.len();
		let queued_dial_upgrades = registered_custom.0
			.iter()
			.map(|proto| UpgradePurpose::Custom(proto.id()))
			.collect();

		NodeHandler {
			custom_protocols_substreams: Vec::with_capacity(registered_custom_len),
			kademlia_substream: None,
			identify_send_back: Arc::new(Mutex::new(Vec::with_capacity(1))),
			ping_in_substreams: Vec::with_capacity(1),
			ping_out_substream: None,
			active_ping_out: None,
			registered_custom,
			upgrades_in_progress_listen: Vec::with_capacity(registered_custom_len + 3),
			upgrades_in_progress_dial: Vec::with_capacity(registered_custom_len + 3),
			next_ping: Delay::new(Instant::now() + DELAY_TO_FIRST_PING),
			next_identify: Interval::new(Instant::now() + DELAY_TO_FIRST_IDENTIFY, PERIOD_IDENTIFY),
			queued_dial_upgrades,
			num_out_user_must_open: registered_custom_len,
			to_notify: None,
		}
	}

	/// Closes the node and returns all the events that should be produced by gracefully closing
	/// everything.
	// TODO: stronger return type
	pub fn close(self) -> Vec<NodeEvent<TSubstream>> {
		let mut events = Vec::new();

		if let Some(_) = self.kademlia_substream {
			events.push(NodeEvent::KadClosed(Ok(())));
		}

		for proto in self.custom_protocols_substreams {
			events.push(NodeEvent::CustomProtocolClosed {
				protocol_id: proto.protocol_id,
				result: Ok(()),
			});
		}

		events
	}

	/// Sends a message on a custom protocol substream.
	pub fn send_custom_message(
		&mut self,
		protocol: ProtocolId,
		packet_id: PacketId,
		data: Vec<u8>,
	) {
		debug_assert!(self.registered_custom.has_protocol(protocol),
			"invalid protocol id requested in the API of the libp2p networking");
		let proto = match self.custom_protocols_substreams.iter().find(|p| p.protocol_id == protocol) {
			Some(proto) => proto,
			None => return, // TODO: diagnostic message?
		};

		let mut message = Bytes::with_capacity(1 + data.len());
		message.extend_from_slice(&[packet_id]);
		message.extend_from_slice(&data);

		// TODO: report error?
		let _ = proto.outgoing.unbounded_send(message);
	}

	/// Injects a substream that has been successfully opened with this node.
	///
	/// If `endpoint` is `Listener`, the remote opened the substream. If `endpoint` is `Dialer`,
	/// our node opened it.
	pub fn inject_substream(&mut self, substream: TSubstream, endpoint: Endpoint) {
		// For listeners, propose all the possible upgrades.
		if endpoint == Endpoint::Listener {
			let listener_upgrade = listener_upgrade!(self);
			// TODO: shouldn't be future::empty() ; requires a change in libp2p
			let upgrade = upgrade::apply(substream, listener_upgrade, Endpoint::Listener, future::empty())
				.map(|(out, _)| out);
			self.upgrades_in_progress_listen.push(Box::new(upgrade) as Box<_>);
			// Since we pushed to `upgrades_in_progress_listen`, we have to notify the task.
			if let Some(task) = self.to_notify.take() {
				task.notify();
			}
			return;
		}

		// If we're the dialer, we have to decide which upgrade we want.
		let purpose = if self.queued_dial_upgrades.is_empty() {
			error!(target: "sub-libp2p", "Logic error: opened an outgoing substream \
				with no purpose");
			return;
		} else {
			self.queued_dial_upgrades.remove(0)
		};

		match purpose {
			UpgradePurpose::Custom(id) => {
				let wanted = if let Some(proto) = self.registered_custom.find_protocol(id) {
					// TODO: meh for cloning
					upgrade::map(proto.clone(), move |c| FinalUpgrade::Custom(c))
				} else {
					error!(target: "sub-libp2p", "Logic error: wrong custom protocol id for \
						opened substream");
					return;
				};

				// TODO: shouldn't be future::empty() ; requires a change in libp2p
				let upgrade = upgrade::apply(substream, wanted, Endpoint::Dialer, future::empty())
					.map(|(out, _)| out);
				self.upgrades_in_progress_dial.push((purpose, Box::new(upgrade) as Box<_>));
			}
			UpgradePurpose::Kad => {
				let wanted = upgrade::map(KadConnecConfig::new(), move |(c, s)| FinalUpgrade::Kad(c, s));
				// TODO: shouldn't be future::empty() ; requires a change in libp2p
				let upgrade = upgrade::apply(substream, wanted, Endpoint::Dialer, future::empty::<Multiaddr, IoError>())
					.map(|(out, _)| out);
				self.upgrades_in_progress_dial.push((purpose, Box::new(upgrade) as Box<_>));
			}
			UpgradePurpose::Identify => {
				let wanted = upgrade::map(identify::IdentifyProtocolConfig, move |i| FinalUpgrade::from(i));
				// TODO: shouldn't be future::empty() ; requires a change in libp2p
				let upgrade = upgrade::apply(substream, wanted, Endpoint::Dialer, future::empty())
					.map(|(out, _)| out);
				self.upgrades_in_progress_dial.push((purpose, Box::new(upgrade) as Box<_>));
			}
			UpgradePurpose::Ping => {
				let wanted = upgrade::map(ping::Ping, move |p| FinalUpgrade::from(p));
				// TODO: shouldn't be future::empty() ; requires a change in libp2p
				let upgrade = upgrade::apply(substream, wanted, Endpoint::Dialer, future::empty::<Multiaddr, IoError>())
					.map(|(out, _): (FinalUpgrade<TSubstream, TUserData>, _)| out);
				self.upgrades_in_progress_dial.push((purpose, Box::new(upgrade) as Box<_>));
			}
		};

		// Since we pushed to `upgrades_in_progress_dial`, we have to notify the task.
		if let Some(task) = self.to_notify.take() {
			task.notify();
		}
	}

	/// If we have a Kademlia substream open, returns a copy of the controller. Otherwise, the node
	/// will try to open a Kademlia substream and produce a `KadOpen` event containing the
	/// controller.
	pub fn open_kademlia(&mut self) -> Option<KadConnecController> {
		if let Some((ref ctrl, _)) = self.kademlia_substream {
			Some(ctrl.clone())
		} else if self.has_upgrade_purpose(&UpgradePurpose::Kad) {
			// We are currently upgrading a substream to Kademlia ; nothing more to do except wait.
			None
		} else {
			// Opening a new substream for Kademlia.
			self.queued_dial_upgrades.push(UpgradePurpose::Kad);
			self.num_out_user_must_open += 1;
			None
		}
	}

	/// Returns true if we are currently upgrading to the given protocol.
	fn has_upgrade_purpose(&self, purpose: &UpgradePurpose) -> bool {
		self.upgrades_in_progress_dial.iter().any(|&(ref p, _)| p == purpose) ||
			self.queued_dial_upgrades.iter().any(|p| p == purpose)
	}

	/// Cancels a dialing upgrade in progress.
	///
	/// Useful when the listener opened the protocol we wanted.
	fn cancel_dial_upgrade(&mut self, purpose: &UpgradePurpose) {
		self.upgrades_in_progress_dial.retain(|&(purp, _)| &purp != purpose);
		self.queued_dial_upgrades.retain(|u| u != purpose);
	}

	/// Returns the names of the protocols that we supporitt.
	fn supported_protocol_names(&self) -> Vec<String> {
		let list = listener_upgrade!(self);
		ConnectionUpgrade::<TSubstream, future::Empty<Multiaddr, IoError>>::protocol_names(&list)
			.filter_map(|(n, _)| String::from_utf8(n.to_vec()).ok())
			.collect()
	}

	/// Inject a fully negotiated substream into the state.
	///
	/// Optionally produces an event to dispatch.
	fn inject_fully_negotiated(
		&mut self,
		upgrade: FinalUpgrade<TSubstream, TUserData>
	) -> Option<NodeEvent<TSubstream>> {
		match upgrade {
			FinalUpgrade::IdentifyListener(sender) =>
				Some(NodeEvent::IdentificationRequest(IdentificationRequest {
					sender,
					identify_send_back: self.identify_send_back.clone(),
					protocols: self.supported_protocol_names(),
				})),
			FinalUpgrade::IdentifyDialer(info, observed_addr) => {
				self.cancel_dial_upgrade(&UpgradePurpose::Identify);
				Some(NodeEvent::Identified { info, observed_addr })
			},
			FinalUpgrade::PingDialer(pinger, ping_process) => {
				self.cancel_dial_upgrade(&UpgradePurpose::Ping);
				// We always open the ping substream for a reason, which is to immediately ping.
				self.ping_out_substream = Some((pinger, ping_process));
				if self.ping_remote() {
					Some(NodeEvent::PingStart)
				} else {
					None
				}
			},
			FinalUpgrade::PingListener(ping_listener) => {
				self.ping_in_substreams.push(ping_listener);
				None
			},
			FinalUpgrade::Kad(controller, stream) => {
				// Remove all upgrades in the progress for Kademlia.
				self.cancel_dial_upgrade(&UpgradePurpose::Kad);
				// Refuse the substream if we already have Kademlia substream open.
				if self.kademlia_substream.is_none() {
					self.kademlia_substream = Some((controller.clone(), stream));
					Some(NodeEvent::KadOpen(controller))
				} else {
					None
				}
			},
			FinalUpgrade::Custom(proto) => {
				self.cancel_dial_upgrade(&UpgradePurpose::Custom(proto.protocol_id));
				if self.custom_protocols_substreams.iter().any(|p| p.protocol_id == proto.protocol_id) {
					// Skipping protocol that's already open.
					return None;
				}

				let event = NodeEvent::CustomProtocolOpen {
					protocol_id: proto.protocol_id,
					version: proto.protocol_version,
				};

				self.custom_protocols_substreams.push(proto);
				Some(event)
			},
		}
	}

	/// Start the process of identifying the remote.
	fn identify_remote(&mut self) {
		if !self.has_upgrade_purpose(&UpgradePurpose::Identify) {
			self.queued_dial_upgrades.push(UpgradePurpose::Identify);
			self.num_out_user_must_open += 1;
		}
	}

	/// Start the process of pinging the remote.
	///
	/// Doesn't do anything if a ping attempt is already in progress.
	///
	/// Returns true if this actually starts a ping, false is this just opens a substream or does
	/// nothing.
	fn ping_remote(&mut self) -> bool {
		// Ignore if we are already actively pinging.
		if self.active_ping_out.is_some() {
			return false;
		}

		// If we have a ping open, ping it!
		if let Some((ref mut pinger, _)) = self.ping_out_substream {
			let future = Timeout::new(pinger.ping(), PING_TIMEOUT);
			self.active_ping_out = Some((Instant::now(), Box::new(future) as Box<_>));
			return true;
		}

		// Otherwise, ensure we have an upgrade for a ping substream in queue.
		if !self.has_upgrade_purpose(&UpgradePurpose::Ping) {
			self.queued_dial_upgrades.push(UpgradePurpose::Ping);
			self.num_out_user_must_open += 1;
		}

		false
	}

	/// Polls the upgrades in progress.
	fn poll_upgrades_in_progress(&mut self) -> Poll<Option<NodeEvent<TSubstream>>, IoError> {
		// Continue negotiation of newly-opened substreams on the listening side.
		// We remove each element from `upgrades_in_progress_listen` one by one and add them back
		// if not ready.
		for n in (0 .. self.upgrades_in_progress_listen.len()).rev() {
			let mut in_progress = self.upgrades_in_progress_listen.swap_remove(n);
			match in_progress.poll() {
				Ok(Async::Ready(upgrade)) => {
					if let Some(event) = self.inject_fully_negotiated(upgrade) {
						return Ok(Async::Ready(Some(event)));
					}
				},
				Ok(Async::NotReady) => {
					self.upgrades_in_progress_listen.push(in_progress);
				},
				Err(err) => {
					return Ok(Async::Ready(Some(NodeEvent::SubstreamUpgradeFail(err))));
				},
			}
		}

		// Continue negotiation of newly-opened substreams.
		// We remove each element from `upgrades_in_progress_dial` one by one and add them back if
		// not ready.
		for n in (0 .. self.upgrades_in_progress_dial.len()).rev() {
			let (purpose, mut in_progress) = self.upgrades_in_progress_dial.swap_remove(n);
			match in_progress.poll() {
				Ok(Async::Ready(upgrade)) => {
					if let Some(event) = self.inject_fully_negotiated(upgrade) {
						return Ok(Async::Ready(Some(event)));
					}
				},
				Ok(Async::NotReady) =>
					self.upgrades_in_progress_dial.push((purpose, in_progress)),
				Err(err) => {
					// TODO: dispatch depending on actual error ; right now we assume that
					// error == not supported, which is not necessarily true in theory
					if let UpgradePurpose::Custom(_) = purpose {
						return Ok(Async::Ready(Some(NodeEvent::Useless)));
					} else {
						let msg = format!("While upgrading to {:?}: {:?}", purpose, err);
						let err = IoError::new(IoErrorKind::Other, msg);
						return Ok(Async::Ready(Some(NodeEvent::SubstreamUpgradeFail(err))));
					}
				},
			}
		}

		Ok(Async::NotReady)
	}

	/// Polls the upgrades in progress.
	fn poll_custom_protocols(&mut self) -> Poll<Option<NodeEvent<TSubstream>>, IoError> {
		// Poll for messages on the custom protocol stream.
		for n in (0 .. self.custom_protocols_substreams.len()).rev() {
			let mut custom_proto = self.custom_protocols_substreams.swap_remove(n);
			match custom_proto.incoming.poll() {
				Ok(Async::NotReady) => self.custom_protocols_substreams.push(custom_proto),
				Ok(Async::Ready(Some((packet_id, data)))) => {
					let protocol_id = custom_proto.protocol_id;
					self.custom_protocols_substreams.push(custom_proto);
					return Ok(Async::Ready(Some(NodeEvent::CustomMessage {
						protocol_id,
						packet_id,
						data,
					})));
				},
				Ok(Async::Ready(None)) => {
					// Trying to reopen the protocol.
					self.queued_dial_upgrades.push(UpgradePurpose::Custom(custom_proto.protocol_id));
					self.num_out_user_must_open += 1;
					return Ok(Async::Ready(Some(NodeEvent::CustomProtocolClosed {
						protocol_id: custom_proto.protocol_id,
						result: Ok(()),
					})))
				},
				Err(err) => {
					// Trying to reopen the protocol.
					self.queued_dial_upgrades.push(UpgradePurpose::Custom(custom_proto.protocol_id));
					self.num_out_user_must_open += 1;
					return Ok(Async::Ready(Some(NodeEvent::CustomProtocolClosed {
						protocol_id: custom_proto.protocol_id,
						result: Err(err),
					})))
				},
			}
		}

		Ok(Async::NotReady)
	}

	/// Polls the open Kademlia substream, if any.
	fn poll_kademlia(&mut self) -> Poll<Option<NodeEvent<TSubstream>>, IoError> {
		// Poll for Kademlia events.
		if let Some((controller, mut stream)) = self.kademlia_substream.take() {
			match stream.poll() {
				Ok(Async::Ready(Some(KadIncomingRequest::FindNode { searched, responder }))) => {
					return Ok(Async::Ready(Some(NodeEvent::KadFindNode { searched, responder })));
				},
				// We don't care about Kademlia pings, they are unused.
				Ok(Async::Ready(Some(KadIncomingRequest::PingPong))) => {},
				Ok(Async::NotReady) => self.kademlia_substream = Some((controller, stream)),
				Ok(Async::Ready(None)) => return Ok(Async::Ready(Some(NodeEvent::KadClosed(Ok(()))))),
				Err(err) => return Ok(Async::Ready(Some(NodeEvent::KadClosed(Err(err))))),
			}
		}

		Ok(Async::NotReady)
	}

	/// Polls the ping substreams.
	fn poll_ping(&mut self) -> Poll<Option<NodeEvent<TSubstream>>, IoError> {
		// Poll for answering pings.
		for n in (0 .. self.ping_in_substreams.len()).rev() {
			let mut ping = self.ping_in_substreams.swap_remove(n);
			match ping.poll() {
				Ok(Async::Ready(())) => {},
				Ok(Async::NotReady) => self.ping_in_substreams.push(ping),
				Err(err) => warn!(target: "sub-libp2p", "Remote ping substream errored:  {:?}", err),
			}
		}

		// Poll the ping substream.
		// TODO: the pinging API would benefit from some improvements on the side of libp2p.
		if let Some((pinger, mut future)) = self.ping_out_substream.take() {
			match future.poll() {
				Ok(Async::Ready(())) => {},
				Ok(Async::NotReady) => self.ping_out_substream = Some((pinger, future)),
				Err(_) => {},
			}
		}

		// Poll the active ping attempt.
		if let Some((started, mut ping_attempt)) = self.active_ping_out.take() {
			match ping_attempt.poll() {
				Ok(Async::Ready(())) => {
					self.next_ping.reset(Instant::now() + DELAY_TO_NEXT_PING);
					return Ok(Async::Ready(Some(NodeEvent::PingSuccess(started.elapsed()))));
				},
				Ok(Async::NotReady) => self.active_ping_out = Some((started, ping_attempt)),
				Err(_) => return Ok(Async::Ready(Some(NodeEvent::Unresponsive))),
			}
		}

		// Poll the future that fires when we need to ping the node again.
		match self.next_ping.poll() {
			Ok(Async::NotReady) => {},
			Ok(Async::Ready(())) => {
				// We reset `next_ping` to a very long time in the future so that we can poll
				// it again without having an accident.
				self.next_ping.reset(Instant::now() + Duration::from_secs(5 * 60));
				if self.ping_remote() {
					return Ok(Async::Ready(Some(NodeEvent::PingStart)));
				}
			},
			Err(err) => {
				warn!(target: "sub-libp2p", "Ping timer errored: {:?}", err);
				return Err(IoError::new(IoErrorKind::Other, err));
			}
		}

		Ok(Async::NotReady)
	}

	/// Polls the identify substreams.
	fn poll_identify(&mut self) -> Poll<Option<NodeEvent<TSubstream>>, IoError> {
		// Poll the future that fires when we need to identify the node again.
		loop {
			match self.next_identify.poll() {
				Ok(Async::NotReady) => break,
				Ok(Async::Ready(Some(_))) => self.identify_remote(),
				Ok(Async::Ready(None)) => {
					warn!(target: "sub-libp2p", "Identify timer closed unexpectedly");
					return Ok(Async::Ready(None));
				}
				Err(err) => {
					warn!(target: "sub-libp2p", "Identify timer errored: {:?}", err);
					return Err(IoError::new(IoErrorKind::Other, err));
				}
			}
		}

		// Poll for sending identify information to the remote.
		let mut identify_send_back = self.identify_send_back.lock();
		for n in (0 .. identify_send_back.len()).rev() {
			let mut id_send_back = identify_send_back.swap_remove(n);
			match id_send_back.poll() {
				Ok(Async::Ready(())) => {},
				Ok(Async::NotReady) => identify_send_back.push(id_send_back),
				Err(err) => warn!(target: "sub-libp2p", "Sending back identify info errored: {:?}", err),
			}
		}

		Ok(Async::NotReady)
	}
}

impl<TSubstream, TUserData> Stream for NodeHandler<TSubstream, TUserData>
where TSubstream: AsyncRead + AsyncWrite + Send + 'static,
	  TUserData: Clone + Send + 'static,
{
	type Item = NodeEvent<TSubstream>;
	type Error = IoError;

	fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
		// Request new outbound substreams from the user if necessary.
		if self.num_out_user_must_open >= 1 {
			self.num_out_user_must_open -= 1;
			return Ok(Async::Ready(Some(NodeEvent::OutboundSubstreamRequested)));
		}

		match self.poll_upgrades_in_progress()? {
			Async::Ready(value) => return Ok(Async::Ready(value)),
			Async::NotReady => (),
		};

		match self.poll_custom_protocols()? {
			Async::Ready(value) => return Ok(Async::Ready(value)),
			Async::NotReady => (),
		};

		match self.poll_kademlia()? {
			Async::Ready(value) => return Ok(Async::Ready(value)),
			Async::NotReady => (),
		};

		match self.poll_ping()? {
			Async::Ready(value) => return Ok(Async::Ready(value)),
			Async::NotReady => (),
		};

		match self.poll_identify()? {
			Async::Ready(value) => return Ok(Async::Ready(value)),
			Async::NotReady => (),
		};

		// Nothing happened. Register our task to be notified and return.
		self.to_notify = Some(task::current());
		Ok(Async::NotReady)
	}
}

/// Enum of all the possible protocols our service handles.
enum FinalUpgrade<TSubstream, TUserData> {
	Kad(KadConnecController, Box<Stream<Item = KadIncomingRequest, Error = IoError> + Send>),
	IdentifyListener(identify::IdentifySender<TSubstream>),
	IdentifyDialer(identify::IdentifyInfo, Multiaddr),
	PingDialer(ping::Pinger, Box<Future<Item = (), Error = IoError> + Send>),
	PingListener(Box<Future<Item = (), Error = IoError> + Send>),
	Custom(RegisteredProtocolOutput<TUserData>),
}

impl<TSubstream, TUserData> From<ping::PingOutput> for FinalUpgrade<TSubstream, TUserData> {
	fn from(out: ping::PingOutput) -> Self {
		match out {
			ping::PingOutput::Ponger(processing) =>
				FinalUpgrade::PingListener(processing),
			ping::PingOutput::Pinger { pinger, processing } =>
				FinalUpgrade::PingDialer(pinger, processing),
		}
	}
}

impl<TSubstream, TUserData> From<identify::IdentifyOutput<TSubstream>> for FinalUpgrade<TSubstream, TUserData> {
	fn from(out: identify::IdentifyOutput<TSubstream>) -> Self {
		match out {
			identify::IdentifyOutput::RemoteInfo { info, observed_addr } =>
				FinalUpgrade::IdentifyDialer(info, observed_addr),
			identify::IdentifyOutput::Sender { sender } =>
				FinalUpgrade::IdentifyListener(sender),
		}
	}
}
