// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Helper for handling (i.e. answering) finality requests from a remote peer via the
//! [`crate::request_responses::RequestResponsesBehaviour`].

use codec::Decode;
use crate::chain::FinalityProofProvider;
use crate::config::ProtocolId;
use crate::request_responses::{IncomingRequest, ProtocolConfig};
use crate::schema::v1::finality::{FinalityProofRequest, FinalityProofResponse};
use futures::channel::{mpsc, oneshot};
use futures::stream::StreamExt;
use log::debug;
use prost::Message;
use sp_runtime::{traits::Block as BlockT};
use std::sync::{Arc};
use std::time::Duration;

const LOG_TARGET: &str = "finality-request-handler";

// TODO: Document that this is for clients not reponding only.
pub fn generate_protocol_config(protocol_id: ProtocolId) -> ProtocolConfig {
	ProtocolConfig {
		name: generate_protocol_name(protocol_id).into(),
		max_request_size: 1024 * 1024,
		max_response_size: 1024 * 1024,
		// TODO: What is a sane value here?
		request_timeout: Duration::from_secs(10),
		inbound_queue: None,
	}
}

/// Generate the finality proof protocol name from chain specific protocol identifier.
fn generate_protocol_name(protocol_id: ProtocolId) -> String {
	let mut s = String::new();
	s.push_str("/");
	s.push_str(protocol_id.as_ref());
	s.push_str("/finality-proof/1");
	s
}

/// Handler for incoming finality requests from a remote peer.
pub struct FinalityRequestHandler<B> {
	proof_provider: Arc<dyn FinalityProofProvider<B>>,
	request_receiver: mpsc::Receiver<IncomingRequest>,
}

impl<B: BlockT> FinalityRequestHandler<B> {
	/// Create a new [`FinalityRequestHandler`].
	pub fn new(
		protocol_id: ProtocolId,
		proof_provider: Arc<dyn FinalityProofProvider<B>>,
	) -> (Self, ProtocolConfig){
		// TODO: Likeley we want to allow more than 0 buffered requests. Rethink this value.
		let (tx, rx) = mpsc::channel(0);

		let mut protocol_config = generate_protocol_config(protocol_id);
		protocol_config.inbound_queue = Some(tx);

		let handler = FinalityRequestHandler {
			proof_provider,
			request_receiver: rx,
		};

		(handler, protocol_config)
	}

	fn handle_request(
		&self,
		payload: Vec<u8>,
		pending_response: oneshot::Sender<Vec<u8>>
	) -> Result<(), HandleRequestError<B>> {
		// Decode request.
		let request = FinalityProofRequest::decode(&payload[..])?;
		let block_hash = Decode::decode(&mut request.block_hash.as_ref())?;

		// Proof.
		let finality_proof = self.proof_provider.prove_finality(block_hash, &request.request)
			.map_err(|e| HandleRequestError::ProofFinality(block_hash, e))?
			.unwrap_or_default();

		// Encode response.
		let resp = FinalityProofResponse { proof: finality_proof };
		let mut data = Vec::with_capacity(resp.encoded_len());
		resp.encode(&mut data)
			.map_err(|e| HandleRequestError::EncodeProto(block_hash, e))?;

		// Respond.
		pending_response.send(data)
			.map_err(|_| HandleRequestError::SendResponse)
	}

	/// Run [`FinalityRequestHandler`].
	pub async fn run(mut self) {
		while let Some(request) = self.request_receiver.next().await {
			let IncomingRequest { peer, payload, pending_response } = request;

			match self.handle_request(payload, pending_response) {
				Ok(()) => debug!(target: LOG_TARGET, "Handled finality proof request from {}.", peer),
				Err(e) => debug!(
					target: LOG_TARGET,
					"Failed to handle finality proof request from {}: {}",
					peer, e,
				),
			}
		}
	}
}

#[derive(derive_more::Display, derive_more::From)]
enum HandleRequestError<B: BlockT> {
	#[display(fmt = "Failed to decode request: {}.", _0)]
	DecodeProto(prost::DecodeError),
	#[display(fmt = "Failed to encode response for {}: {}.", _0, _1)]
	EncodeProto(B::Hash, prost::EncodeError),
	#[display(fmt = "Failed to decode block hash: {}.", _0)]
	DecodeScale(codec::Error),
	#[display(fmt = "Failed to proof finality for {}: {}.", _0, _1)]
	ProofFinality(B::Hash, sp_blockchain::Error),
	#[display(fmt = "Failed to send response.")]
	SendResponse,
}
