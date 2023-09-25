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

//! Request/response protocol for syncing BEEFY justifications.

mod incoming_requests_handler;
pub(crate) mod outgoing_requests_engine;

pub use incoming_requests_handler::BeefyJustifsRequestHandler;

use std::time::Duration;

use codec::{Decode, Encode, Error as CodecError};
use sc_network::{config::RequestResponseConfig, PeerId};
use sp_runtime::traits::{Block, NumberFor};

use crate::communication::{beefy_protocol_name::justifications_protocol_name, peers::PeerReport};
use incoming_requests_handler::IncomingRequestReceiver;

// 10 seems reasonable, considering justifs are explicitly requested only
// for mandatory blocks, by nodes that are syncing/catching-up.
const JUSTIF_CHANNEL_SIZE: usize = 10;

const MAX_RESPONSE_SIZE: u64 = 1024 * 1024;
const JUSTIF_REQUEST_TIMEOUT: Duration = Duration::from_secs(3);

const BEEFY_SYNC_LOG_TARGET: &str = "beefy::sync";

/// Get the configuration for the BEEFY justifications Request/response protocol.
///
/// Returns a receiver for messages received on this protocol and the requested
/// `ProtocolConfig`.
///
/// Consider using [`BeefyJustifsRequestHandler`] instead of this low-level function.
pub(crate) fn on_demand_justifications_protocol_config<Hash: AsRef<[u8]>>(
	genesis_hash: Hash,
	fork_id: Option<&str>,
) -> (IncomingRequestReceiver, RequestResponseConfig) {
	let name = justifications_protocol_name(genesis_hash, fork_id);
	let fallback_names = vec![];
	let (tx, rx) = async_channel::bounded(JUSTIF_CHANNEL_SIZE);
	let rx = IncomingRequestReceiver::new(rx);
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

#[derive(Debug, thiserror::Error)]
pub enum Error {
	#[error(transparent)]
	Client(#[from] sp_blockchain::Error),

	#[error(transparent)]
	RuntimeApi(#[from] sp_api::ApiError),

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

	#[error("Received invalid response.")]
	InvalidResponse(PeerReport),

	#[error("Internal error while getting response.")]
	ResponseError,

	#[error("On-demand requests receiver stream terminated.")]
	RequestsReceiverStreamClosed,
}
