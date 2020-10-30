use crate::request_responses::ProtocolConfig;
use futures::channel::mpsc;
use futures::stream::StreamExt;
use std::sync::{Arc};
pub use crate::{
	config::ProtocolId,
	chain::{Client, FinalityProofProvider}};
use sp_runtime::{traits::Block as BlockT};
use crate::request_responses::IncomingRequest;
use prost::Message;

pub fn generate_protocol_name(protocol_id: ProtocolId) -> String {
	let mut s = String::new();
	s.push_str("/");
	s.push_str(protocol_id.as_ref());
	s.push_str("/finality-proof/1");
	s
}

pub struct FinalityRequestHandler<B> {
	proof_provider: Arc<dyn FinalityProofProvider<B>>,
	request_receiver: mpsc::Receiver<IncomingRequest>,
}

impl<B: BlockT> FinalityRequestHandler<B> {
	pub fn new(protocol_id: ProtocolId, proof_provider: Arc<dyn FinalityProofProvider<B>>) -> (Self, ProtocolConfig){
		let (tx, rx) = mpsc::channel(0);

		let protocol_config = ProtocolConfig {
			name: generate_protocol_name(protocol_id).into(),
			// TODO: Change.
			max_request_size: 4096,
			// TODO: Change.
			max_response_size: 4096,
			request_timeout: std::time::Duration::from_secs(10),
			inbound_queue: Some(tx),
		};

		let handler = FinalityRequestHandler {
			proof_provider,
			request_receiver: rx,
		};

		(handler, protocol_config)
	}

	pub async fn run(mut self) {
		while let Some(crate::request_responses::IncomingRequest { peer, payload, pending_response }) = self.request_receiver.next().await {
			let req = crate::schema::v1::finality::FinalityProofRequest::decode(&payload[..]).unwrap();

			let block_hash = codec::Decode::decode(&mut req.block_hash.as_ref()).unwrap();

			log::trace!(target: "sync", "Finality proof request from {} for {}", peer, block_hash);

			let finality_proof = self.proof_provider
				.prove_finality(block_hash, &req.request)
				.unwrap()
				.unwrap_or_default();

			let resp = crate::schema::v1::finality::FinalityProofResponse { proof: finality_proof };
			let mut data = Vec::with_capacity(resp.encoded_len());
			resp.encode(&mut data).unwrap();

			pending_response.send(data).unwrap();
		}
	}
}
