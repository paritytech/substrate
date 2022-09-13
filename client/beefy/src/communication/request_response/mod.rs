// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Request/response protocol for syncing BEEFY justifications.

pub mod incoming_handler;
pub(crate) mod outgoing_request;

use futures::{
	channel::{mpsc, oneshot},
	StreamExt,
};
use std::time::Duration;

use codec::{Decode, Encode, Error as CodecError};
use sc_network::{config as netconfig, config::RequestResponseConfig, PeerId, ReputationChange};
use sp_runtime::traits::{Block, NumberFor};

use crate::communication::beefy_protocol_name::justifications_protocol_name;

// 10 seems reasonable, considering justifs are explicitly requested only
// for mandatory blocks, by nodes that are syncing/catching-up.
const JUSTIF_CHANNEL_SIZE: usize = 10;

const MAX_RESPONSE_SIZE: u64 = 1024 * 1024;
const JUSTIF_REQUEST_TIMEOUT: Duration = Duration::from_secs(3);

/// Get the configuration for the BEEFY justifications Request/response protocol.
///
/// Returns a receiver for messages received on this protocol and the requested
/// `ProtocolConfig`.
pub(crate) fn justif_protocol_config<Hash: AsRef<[u8]>>(
	genesis_hash: Hash,
	fork_id: Option<&str>,
) -> (IncomingRequestReceiver, RequestResponseConfig) {
	let name = justifications_protocol_name(genesis_hash, fork_id);
	let fallback_names = vec![];
	let (tx, rx) = mpsc::channel(JUSTIF_CHANNEL_SIZE);
	let rx = IncomingRequestReceiver { raw: rx };
	let cfg = RequestResponseConfig {
		name,
		fallback_names,
		max_request_size: 32,
		max_response_size: MAX_RESPONSE_SIZE,
		// We are connected to all validators:
		request_timeout: JUSTIF_REQUEST_TIMEOUT,
		inbound_queue: Some(tx),
	};
	(rx, cfg)
}

/// BEEFY justification request.
#[derive(Debug, Clone, Encode, Decode)]
pub struct JustificationRequest<B: Block> {
	/// Start collecting proofs from this block.
	pub begin: NumberFor<B>,
}

/// A request coming in, including a sender for sending responses.
#[derive(Debug)]
pub(crate) struct IncomingRequest<B: Block> {
	/// `PeerId` of sending peer.
	pub peer: PeerId,
	/// The sent request.
	pub payload: JustificationRequest<B>,
	/// Sender for sending response back.
	pub pending_response: oneshot::Sender<netconfig::OutgoingResponse>,
}

impl<B: Block> IncomingRequest<B> {
	/// Create new `IncomingRequest`.
	pub fn new(
		peer: PeerId,
		payload: JustificationRequest<B>,
		pending_response: oneshot::Sender<netconfig::OutgoingResponse>,
	) -> Self {
		Self { peer, payload, pending_response }
	}

	/// Try building from raw network request.
	///
	/// This function will fail if the request cannot be decoded and will apply passed in
	/// reputation changes in that case.
	///
	/// Params:
	/// 		- The raw request to decode
	/// 		- Reputation changes to apply for the peer in case decoding fails.
	fn try_from_raw(
		raw: netconfig::IncomingRequest,
		reputation_changes: Vec<ReputationChange>,
	) -> std::result::Result<Self, Error> {
		let netconfig::IncomingRequest { payload, peer, pending_response } = raw;
		let payload = match JustificationRequest::decode(&mut payload.as_ref()) {
			Ok(payload) => payload,
			Err(err) => {
				let response = netconfig::OutgoingResponse {
					result: Err(()),
					reputation_changes,
					sent_feedback: None,
				};
				if let Err(_) = pending_response.send(response) {
					return Err(Error::DecodingErrorNoReputationChange(peer, err))
				}
				return Err(Error::DecodingError(peer, err))
			},
		};
		Ok(Self::new(peer, payload, pending_response))
	}
}

/// Receiver for incoming BEEFY justifications requests.
///
/// Takes care of decoding and handling of invalid encoded requests.
pub(crate) struct IncomingRequestReceiver {
	raw: mpsc::Receiver<netconfig::IncomingRequest>,
}

impl IncomingRequestReceiver {
	/// Try to receive the next incoming request.
	///
	/// Any received request will be decoded, on decoding errors the provided reputation changes
	/// will be applied and an error will be reported.
	pub async fn recv<B, F>(&mut self, reputation_changes: F) -> Result<IncomingRequest<B>>
	where
		B: Block,
		F: FnOnce() -> Vec<ReputationChange>,
	{
		let req = match self.raw.next().await {
			None => return Err(Error::RequestChannelExhausted),
			Some(raw) => IncomingRequest::<B>::try_from_raw(raw, reputation_changes())?,
		};
		Ok(req)
	}
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
	#[error(transparent)]
	Client(#[from] sp_blockchain::Error),

	#[error(transparent)]
	RuntimeApi(#[from] sp_api::ApiError),

	#[error("BEEFY pallet not available.")]
	Pallet,

	/// Decoding failed, we were able to change the peer's reputation accordingly.
	#[error("Decoding request failed for peer {0}.")]
	DecodingError(PeerId, #[source] CodecError),

	/// Decoding failed, but sending reputation change failed.
	#[error("Decoding request failed for peer {0}, and changing reputation failed.")]
	DecodingErrorNoReputationChange(PeerId, #[source] CodecError),

	/// Incoming request stream exhausted. Should only happen on shutdown.
	#[error("Incoming request channel got closed.")]
	RequestChannelExhausted,

	#[error("Failed to send response.")]
	SendResponse,

	#[error("Failed to send response.")]
	TodoError,
}

/// General result based on above `Error`.
pub type Result<T> = std::result::Result<T, Error>;
