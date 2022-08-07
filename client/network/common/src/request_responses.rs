// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Collection of generic data structures for request-response protocols.

use futures::channel::{mpsc, oneshot};
use libp2p::PeerId;
use sc_peerset::ReputationChange;
use std::{borrow::Cow, time::Duration};

/// Configuration for a single request-response protocol.
#[derive(Debug, Clone)]
pub struct ProtocolConfig {
	/// Name of the protocol on the wire. Should be something like `/foo/bar`.
	pub name: Cow<'static, str>,

	/// Fallback on the wire protocol names to support.
	pub fallback_names: Vec<Cow<'static, str>>,

	/// Maximum allowed size, in bytes, of a request.
	///
	/// Any request larger than this value will be declined as a way to avoid allocating too
	/// much memory for it.
	pub max_request_size: u64,

	/// Maximum allowed size, in bytes, of a response.
	///
	/// Any response larger than this value will be declined as a way to avoid allocating too
	/// much memory for it.
	pub max_response_size: u64,

	/// Duration after which emitted requests are considered timed out.
	///
	/// If you expect the response to come back quickly, you should set this to a smaller duration.
	pub request_timeout: Duration,

	/// Channel on which the networking service will send incoming requests.
	///
	/// Every time a peer sends a request to the local node using this protocol, the networking
	/// service will push an element on this channel. The receiving side of this channel then has
	/// to pull this element, process the request, and send back the response to send back to the
	/// peer.
	///
	/// The size of the channel has to be carefully chosen. If the channel is full, the networking
	/// service will discard the incoming request send back an error to the peer. Consequently,
	/// the channel being full is an indicator that the node is overloaded.
	///
	/// You can typically set the size of the channel to `T / d`, where `T` is the
	/// `request_timeout` and `d` is the expected average duration of CPU and I/O it takes to
	/// build a response.
	///
	/// Can be `None` if the local node does not support answering incoming requests.
	/// If this is `None`, then the local node will not advertise support for this protocol towards
	/// other peers. If this is `Some` but the channel is closed, then the local node will
	/// advertise support for this protocol, but any incoming request will lead to an error being
	/// sent back.
	pub inbound_queue: Option<mpsc::Sender<IncomingRequest>>,
}

/// A single request received by a peer on a request-response protocol.
#[derive(Debug)]
pub struct IncomingRequest {
	/// Who sent the request.
	pub peer: PeerId,

	/// Request sent by the remote. Will always be smaller than
	/// [`ProtocolConfig::max_request_size`].
	pub payload: Vec<u8>,

	/// Channel to send back the response.
	///
	/// There are two ways to indicate that handling the request failed:
	///
	/// 1. Drop `pending_response` and thus not changing the reputation of the peer.
	///
	/// 2. Sending an `Err(())` via `pending_response`, optionally including reputation changes for
	/// the given peer.
	pub pending_response: oneshot::Sender<OutgoingResponse>,
}

/// Response for an incoming request to be send by a request protocol handler.
#[derive(Debug)]
pub struct OutgoingResponse {
	/// The payload of the response.
	///
	/// `Err(())` if none is available e.g. due an error while handling the request.
	pub result: Result<Vec<u8>, ()>,

	/// Reputation changes accrued while handling the request. To be applied to the reputation of
	/// the peer sending the request.
	pub reputation_changes: Vec<ReputationChange>,

	/// If provided, the `oneshot::Sender` will be notified when the request has been sent to the
	/// peer.
	///
	/// > **Note**: Operating systems typically maintain a buffer of a few dozen kilobytes of
	/// >			outgoing data for each TCP socket, and it is not possible for a user
	/// >			application to inspect this buffer. This channel here is not actually notified
	/// >			when the response has been fully sent out, but rather when it has fully been
	/// >			written to the buffer managed by the operating system.
	pub sent_feedback: Option<oneshot::Sender<()>>,
}
