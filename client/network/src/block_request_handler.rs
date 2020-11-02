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

use codec::{Encode, Decode};
use crate::chain::Client;
use crate::config::ProtocolId;
use crate::protocol::{message::BlockAttributes};
use crate::request_responses::{IncomingRequest, ProtocolConfig};
use crate::schema::v1::block_request::FromBlock;
use crate::schema::v1::{BlockResponse, Direction};
use futures::channel::{mpsc, oneshot};
use futures::stream::StreamExt;
use log::debug;
use prost::Message;
use sp_runtime::{traits::Block as BlockT, generic::BlockId, traits::{Header, One, Zero}};
use std::cmp::min;
use std::sync::{Arc};
use std::time::Duration;

const LOG_TARGET: &str = "block-request-handler";
const MAX_BLOCKS_IN_RESPONSE: usize = 128;
const MAX_BODY_BYTES: usize = 8 * 1024 * 1024;

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
	client: Arc<dyn Client<B>>,
	request_receiver: mpsc::Receiver<IncomingRequest>,
}

impl <B: BlockT> BlockRequestHandler<B> {
	/// Create a new [`BlockRequestHandler`].
	pub fn new(protocol_id: ProtocolId, client: Arc<dyn Client<B>>) -> (Self, ProtocolConfig) {
		// TODO: Likeley we want to allow more than 0 buffered requests. Rethink this value.
		let (tx, request_receiver) = mpsc::channel(0);

		let protocol_config = ProtocolConfig {
			name: generate_protocol_name(protocol_id).into(),
			max_request_size: 1024 * 1024,
			max_response_size: 16 * 1024 * 1024,
			request_timeout: Duration::from_secs(40),
			inbound_queue: Some(tx),
		};

		(Self { client, request_receiver }, protocol_config)
	}

	fn handle_request(
		&self,
		payload: Vec<u8>,
		pending_response: oneshot::Sender<Vec<u8>>
	) -> Result<(), HandleRequestError> {
		let request = crate::schema::v1::BlockRequest::decode(&payload[..])?;

		let from_block_id =	match request.from_block.ok_or(HandleRequestError::MissingFromField)? {
			FromBlock::Hash(ref h) => {
				let h = Decode::decode(&mut h.as_ref())?;
				BlockId::<B>::Hash(h)
			}
			FromBlock::Number(ref n) => {
				let n = Decode::decode(&mut n.as_ref())?;
				BlockId::<B>::Number(n)
			}
		};

		let max_blocks = if request.max_blocks == 0 {
			MAX_BLOCKS_IN_RESPONSE
		} else {
			min(request.max_blocks as usize, MAX_BLOCKS_IN_RESPONSE)
		};

		let direction = Direction::from_i32(request.direction)
			.ok_or(HandleRequestError::ParseDirection)?;
		let attributes = BlockAttributes::from_be_u32(request.fields)?;
		let get_header = attributes.contains(BlockAttributes::HEADER);
		let get_body = attributes.contains(BlockAttributes::BODY);
		let get_justification = attributes.contains(BlockAttributes::JUSTIFICATION);

		let mut blocks = Vec::new();
		let mut block_id = from_block_id;

		let mut total_size: usize = 0;
		while let Some(header) = self.client.header(block_id).unwrap_or(None) {
			let number = *header.number();
			let hash = header.hash();
			let parent_hash = *header.parent_hash();
			let justification = if get_justification {
				self.client.justification(&BlockId::Hash(hash))?
			} else {
				None
			};
			let is_empty_justification = justification.as_ref().map(|j| j.is_empty()).unwrap_or(false);

			let body = if get_body {
				match self.client.block_body(&BlockId::Hash(hash))? {
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

			total_size += block_data.body.len();
			blocks.push(block_data);

			if blocks.len() >= max_blocks as usize || total_size > MAX_BODY_BYTES {
				break
			}

			match direction {
				Direction::Ascending => {
					block_id = BlockId::Number(number + One::one())
				}
				Direction::Descending => {
					if number.is_zero() {
						break
					}
					block_id = BlockId::Hash(parent_hash)
				}
			}
		}

		let res = BlockResponse { blocks };

		let mut data = Vec::with_capacity(res.encoded_len());
		res.encode(&mut data)?;

		pending_response.send(data)
			.map_err(|_| HandleRequestError::SendResponse)
	}

	/// Run [`BlockRequestHandler`].
	pub async fn run(mut self) {
		while let Some(request) = self.request_receiver.next().await {
			let IncomingRequest { peer, payload, pending_response } = request;

			match self.handle_request(payload, pending_response) {
				Ok(()) => debug!(target: LOG_TARGET, "Handled block request from {}.", peer),
				Err(e) => debug!(
					target: LOG_TARGET,
					"Failed to handle block request from {}: {}",
					peer, e,
				),
			}
		}
	}
}

#[derive(derive_more::Display, derive_more::From)]
enum HandleRequestError {
	#[display(fmt = "Failed to decode request: {}.", _0)]
	DecodeProto(prost::DecodeError),
	#[display(fmt = "Failed to encode response: {}.", _0)]
	EncodeProto(prost::EncodeError),
	#[display(fmt = "Failed to decode block hash: {}.", _0)]
	DecodeScale(codec::Error),
	#[display(fmt = "Missing `BlockRequest::from_block` field.")]
	MissingFromField,
	#[display(fmt = "Failed to parse BlockRequest::direction.")]
	ParseDirection,
	Client(sp_blockchain::Error),
	#[display(fmt = "Failed to send response.")]
	SendResponse,
}
