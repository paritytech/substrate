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

//! Helper for handling (i.e. answering) block requests from a remote peer via the
//! [`crate::request_responses::RequestResponsesBehaviour`].

use crate::request_responses::ProtocolConfig;
use futures::channel::mpsc;
use futures::stream::StreamExt;
use std::sync::{Arc};
pub use crate::{
	protocol::{message::{self, BlockAttributes}},
	chain::{Client, FinalityProofProvider},
	config::ProtocolId,
};
use sp_runtime::{traits::Block as BlockT};
use crate::request_responses::IncomingRequest;
use prost::Message;
use codec::{Encode, Decode};
use sp_runtime::{generic::BlockId, traits::{Header, One, Zero}};

/// Generate the block protocol name from chain specific protocol identifier.
pub fn generate_protocol_name(protocol_id: ProtocolId) -> String {
	let mut s = String::new();
	s.push_str("/");
	s.push_str(protocol_id.as_ref());
	s.push_str("/sync/2");
	s
}

/// Handler for incoming block requests from a remote peer.
pub struct BlockRequestHandler<B> {
	// TODO: Rename?
	chain: Arc<dyn Client<B>>,
	request_receiver: mpsc::Receiver<IncomingRequest>,
}

impl <B: BlockT> BlockRequestHandler<B> {
	/// Create a new [`BlockRequestHandler`].
	pub fn new(protocol_id: ProtocolId, client: Arc<dyn Client<B>>) -> (Self, ProtocolConfig) {
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

		let handler = Self {
			chain: client,
			request_receiver: rx,
		};

		(handler, protocol_config)
	}

	/// Run [`BlockRequestHandler`].
	pub async fn run(mut self) {
		while let Some(crate::request_responses::IncomingRequest { peer: _, payload, pending_response }) = self.request_receiver.next().await {

			let request = crate::schema::v1::BlockRequest::decode(&payload[..]).unwrap();



			let from_block_id =	match request.from_block {
				Some(crate::schema::v1::block_request::FromBlock::Hash(ref h)) => {
					let h = Decode::decode(&mut h.as_ref()).unwrap();
					BlockId::<B>::Hash(h)
				}
				Some(crate::schema::v1::block_request::FromBlock::Number(ref n)) => {
					let n = Decode::decode(&mut n.as_ref()).unwrap();
					BlockId::<B>::Number(n)
				}
				None => {
					panic!();
					// let msg = "missing `BlockRequest::from_block` field";
					// return Err(io::Error::new(io::ErrorKind::Other, msg).into())
				}
			};

			// let max_blocks =
			// 	if request.max_blocks == 0 {
			// 		self.config.max_block_data_response
			// 	} else {
			// 		min(request.max_blocks, self.config.max_block_data_response)
			// 	};

			let direction =
				if request.direction == crate::schema::v1::Direction::Ascending as i32 {
					crate::schema::v1::Direction::Ascending
				} else if request.direction == crate::schema::v1::Direction::Descending as i32 {
					crate::schema::v1::Direction::Descending
				} else {
					panic!();
					// let msg = format!("invalid `BlockRequest::direction` value: {}", request.direction);
					// return Err(io::Error::new(io::ErrorKind::Other, msg).into())
				};

			let attributes = BlockAttributes::from_be_u32(request.fields).unwrap();
			let get_header = attributes.contains(BlockAttributes::HEADER);
			let get_body = attributes.contains(BlockAttributes::BODY);
			let get_justification = attributes.contains(BlockAttributes::JUSTIFICATION);

			let mut blocks = Vec::new();
			let mut block_id = from_block_id;
			// TODO: Still needed?
			// let mut total_size = 0;
			while let Some(header) = self.chain.header(block_id).unwrap_or(None) {
				// if blocks.len() >= max_blocks as usize
				// 	|| (blocks.len() >= 1 && total_size > self.config.max_block_body_bytes)
				// {
				// 	break
				// }

				let number = *header.number();
				let hash = header.hash();
				let parent_hash = *header.parent_hash();
				let justification = if get_justification {
					self.chain.justification(&BlockId::Hash(hash)).unwrap()
				} else {
					None
				};
				let is_empty_justification = justification.as_ref().map(|j| j.is_empty()).unwrap_or(false);

				let body = if get_body {
					match self.chain.block_body(&BlockId::Hash(hash)).unwrap() {
						Some(mut extrinsics) => extrinsics.iter_mut()
							.map(|extrinsic| extrinsic.encode())
							.collect(),
						None => {
							log::trace!(target: "sync", "Missing data for block request.");
							break;
						}
					}
				} else {
					Vec::new()
				};

				let block_data = crate::schema::v1::BlockData {
					hash: hash.encode(),
					header: if get_header {
						header.encode()
					} else {
						Vec::new()
					},
					body,
					receipt: Vec::new(),
					message_queue: Vec::new(),
					justification: justification.unwrap_or_default(),
					is_empty_justification,
				};

				// TODO: Still needed?
				// total_size += block_data.body.len();
				blocks.push(block_data);

				match direction {
					crate::schema::v1::Direction::Ascending => {
						block_id = BlockId::Number(number + One::one())
					}
					crate::schema::v1::Direction::Descending => {
						if number.is_zero() {
							break
						}
						block_id = BlockId::Hash(parent_hash)
					}
				}
			}

			let res = crate::schema::v1::BlockResponse { blocks };

			let mut data = Vec::with_capacity(res.encoded_len());
			res.encode(&mut data).unwrap();
			// log::debug!(
			// 	target: "sync",
			// 	"Error encoding block response for peer {}: {}",
			// 	peer, e
			// )

			pending_response.send(data).unwrap();
		}
	}
}
