// Copyright 2022 Parity Technologies (UK) Ltd.
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

//! Helper for handling (i.e. answering) BEEFY justifications requests from a remote peer.

use beefy_primitives::BEEFY_ENGINE_ID;
use log::debug;
use sc_client_api::BlockBackend;
use sc_network::{config as netconfig, config::RequestResponseConfig};
use sp_runtime::{generic::BlockId, traits::Block};
use std::{marker::PhantomData, sync::Arc};

use crate::communication::request_response::{
	justif_protocol_config, Error, IncomingRequest, IncomingRequestReceiver,
};

/// Handler for incoming BEEFY justifications requests from a remote peer.
pub struct BeefyJustifsRequestHandler<B, Client> {
	request_receiver: IncomingRequestReceiver,
	/// Blockchain client.
	client: Arc<Client>,
	_block: PhantomData<B>,
}

impl<B, Client> BeefyJustifsRequestHandler<B, Client>
where
	B: Block,
	Client: BlockBackend<B> + Send + Sync + 'static,
{
	/// Create a new [`BeefyJustifsRequestHandler`].
	pub fn new(fork_id: Option<&str>, client: Arc<Client>) -> (Self, RequestResponseConfig) {
		let genesis_hash = client
			.block_hash(0u32.into())
			.ok()
			.flatten()
			.expect("Genesis block exists; qed");
		let (request_receiver, config) = justif_protocol_config(genesis_hash, fork_id);

		(Self { client, request_receiver, _block: PhantomData }, config)
	}

	async fn handle_request(&self, request: IncomingRequest<B>) -> Result<(), Error> {
		// TODO: validate `request.begin` and change peer reputation for invalid requests.

		let encoded_proof = self
			.client
			.justifications(&BlockId::Number(request.payload.begin))
			.map_err(Error::Client)?
			.map(|justifs| justifs.get(BEEFY_ENGINE_ID).cloned())
			.flatten()
			// No BEEFY justification present.
			.ok_or(());

		request
			.pending_response
			.send(netconfig::OutgoingResponse {
				result: encoded_proof,
				reputation_changes: Vec::new(),
				sent_feedback: None,
			})
			.map_err(|_| Error::SendResponse)
	}

	/// Run [`BeefyJustifsRequestHandler`].
	pub async fn run(mut self) {
		while let Ok(request) = self.request_receiver.recv(|| vec![]).await {
			let peer = request.peer;
			match self.handle_request(request).await {
				Ok(()) => {
					debug!(
						target: "beefy::sync",
						"Handled BEEFY justification request from {}.", peer
					)
				},
				Err(e) => {
					// TODO: handle reputation changes here
					debug!(
						target: "beefy::sync",
						"Failed to handle BEEFY justification request from {}: {}", peer, e,
					)
				},
			}
		}
	}
}
