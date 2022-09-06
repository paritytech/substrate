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

//! Bitswap server for substrate.
//!
//! Allows querying transactions by hash over standard bitswap protocol
//! Only supports bitswap 1.2.0.
//! CID is expected to reference 256-bit Blake2b transaction hash.

// #![allow(unused)]
use cid::Version;
use futures::{channel::mpsc, StreamExt};
use libp2p::core::PeerId;
use log::{debug, error, trace};
use prost::Message;
use sc_client_api::BlockBackend;
use sc_network_common::{
	protocol::ProtocolName,
	request_responses::{IncomingRequest, OutgoingResponse, ProtocolConfig},
};
use schema::bitswap::{
	message::{wantlist::WantType, Block as MessageBlock, BlockPresence, BlockPresenceType},
	Message as BitswapMessage,
};
use sp_runtime::traits::Block as BlockT;
use std::{io, marker::PhantomData, sync::Arc, time::Duration};
use unsigned_varint::encode as varint_encode;

mod schema;

const LOG_TARGET: &str = "bitswap";

// Undocumented, but according to JS the bitswap messages have a max size of 512*1024 bytes
// https://github.com/ipfs/js-ipfs-bitswap/blob/
// d8f80408aadab94c962f6b88f343eb9f39fa0fcc/src/decision-engine/index.js#L16
// We set it to the same value as max substrate protocol message
const MAX_PACKET_SIZE: u64 = 16 * 1024 * 1024;

/// Max number of queued responses before denying requests.
const MAX_REQUEST_QUEUE: usize = 20;

/// Max number of blocks per wantlist
const MAX_WANTED_BLOCKS: usize = 16;

/// Bitswap protocol name
const PROTOCOL_NAME: &'static str = "/ipfs/bitswap/1.2.0";

/// Prefix represents all metadata of a CID, without the actual content.
#[derive(PartialEq, Eq, Clone, Debug)]
struct Prefix {
	/// The version of CID.
	pub version: Version,
	/// The codec of CID.
	pub codec: u64,
	/// The multihash type of CID.
	pub mh_type: u64,
	/// The multihash length of CID.
	pub mh_len: u8,
}

impl Prefix {
	/// Convert the prefix to encoded bytes.
	pub fn to_bytes(&self) -> Vec<u8> {
		let mut res = Vec::with_capacity(4);
		let mut buf = varint_encode::u64_buffer();
		let version = varint_encode::u64(self.version.into(), &mut buf);
		res.extend_from_slice(version);
		let mut buf = varint_encode::u64_buffer();
		let codec = varint_encode::u64(self.codec, &mut buf);
		res.extend_from_slice(codec);
		let mut buf = varint_encode::u64_buffer();
		let mh_type = varint_encode::u64(self.mh_type, &mut buf);
		res.extend_from_slice(mh_type);
		let mut buf = varint_encode::u64_buffer();
		let mh_len = varint_encode::u64(self.mh_len as u64, &mut buf);
		res.extend_from_slice(mh_len);
		res
	}
}

/// Network behaviour that handles sending and receiving IPFS blocks.
pub struct BitswapRequestHandler<B, Client> {
	client: Arc<Client>,
	request_receiver: mpsc::Receiver<IncomingRequest>,
	_block: PhantomData<B>,
}

impl<B: BlockT, Client: BlockBackend<B>> BitswapRequestHandler<B, Client> {
	/// Create a new [`BitswapRequestHandler`].
	pub fn new(client: Arc<Client>) -> (Self, ProtocolConfig) {
		let (tx, request_receiver) = mpsc::channel(MAX_REQUEST_QUEUE);

		let config = ProtocolConfig {
			name: ProtocolName::from(PROTOCOL_NAME),
			fallback_names: vec![],
			max_request_size: MAX_PACKET_SIZE,
			max_response_size: MAX_PACKET_SIZE,
			request_timeout: Duration::from_secs(15),
			inbound_queue: Some(tx),
		};

		(Self { client, _block: PhantomData::default(), request_receiver }, config)
	}

	/// Run [`BitswapRequestHandler`].
	pub async fn run(mut self) {
		while let Some(request) = self.request_receiver.next().await {
			let IncomingRequest { peer, payload, pending_response } = request;

			match self.handle_message(&peer, &payload) {
				Ok(response) => {
					let response = OutgoingResponse {
						result: Ok(response),
						reputation_changes: Vec::new(),
						sent_feedback: None,
					};

					match pending_response.send(response) {
						Ok(()) =>
							trace!(target: LOG_TARGET, "Handled bitswap request from {peer}.",),
						Err(_) => debug!(
							target: LOG_TARGET,
							"Failed to handle light client request from {peer}: {}",
							BitswapError::SendResponse,
						),
					}
				},
				Err(err) => {
					error!(target: LOG_TARGET, "Failed to process request from {peer}: {err}");

					let response = OutgoingResponse {
						result: Err(()),
						reputation_changes: vec![],
						sent_feedback: None,
					};

					if pending_response.send(response).is_err() {
						debug!(
							target: LOG_TARGET,
							"Failed to handle bitswap request from {peer}: {}",
							BitswapError::SendResponse,
						);
					}
				},
			}
		}
	}

	/// Handle received Bitswap request
	fn handle_message(
		&mut self,
		peer: &PeerId,
		payload: &Vec<u8>,
	) -> Result<Vec<u8>, BitswapError> {
		let request = schema::bitswap::Message::decode(&payload[..])?;

		trace!(target: LOG_TARGET, "Received request: {:?} from {}", request, peer);

		let mut response = BitswapMessage::default();

		let wantlist = match request.wantlist {
			Some(wantlist) => wantlist,
			None => {
				debug!(target: LOG_TARGET, "Unexpected bitswap message from {}", peer);
				return Err(BitswapError::InvalidWantList)
			},
		};

		if wantlist.entries.len() > MAX_WANTED_BLOCKS {
			trace!(target: LOG_TARGET, "Ignored request: too many entries");
			return Err(BitswapError::TooManyEntries)
		}

		for entry in wantlist.entries {
			let cid = match cid::Cid::read_bytes(entry.block.as_slice()) {
				Ok(cid) => cid,
				Err(e) => {
					trace!(target: LOG_TARGET, "Bad CID {:?}: {:?}", entry.block, e);
					continue
				},
			};

			if cid.version() != cid::Version::V1 ||
				cid.hash().code() != u64::from(cid::multihash::Code::Blake2b256) ||
				cid.hash().size() != 32
			{
				debug!(target: LOG_TARGET, "Ignoring unsupported CID {}: {}", peer, cid);
				continue
			}

			let mut hash = B::Hash::default();
			hash.as_mut().copy_from_slice(&cid.hash().digest()[0..32]);
			let transaction = match self.client.indexed_transaction(&hash) {
				Ok(ex) => ex,
				Err(e) => {
					error!(target: LOG_TARGET, "Error retrieving transaction {}: {}", hash, e);
					None
				},
			};

			match transaction {
				Some(transaction) => {
					trace!(target: LOG_TARGET, "Found CID {:?}, hash {:?}", cid, hash);

					if entry.want_type == WantType::Block as i32 {
						let prefix = Prefix {
							version: cid.version(),
							codec: cid.codec(),
							mh_type: cid.hash().code(),
							mh_len: cid.hash().size(),
						};
						response
							.payload
							.push(MessageBlock { prefix: prefix.to_bytes(), data: transaction });
					} else {
						response.block_presences.push(BlockPresence {
							r#type: BlockPresenceType::Have as i32,
							cid: cid.to_bytes(),
						});
					}
				},
				None => {
					trace!(target: LOG_TARGET, "Missing CID {:?}, hash {:?}", cid, hash);

					if entry.send_dont_have {
						response.block_presences.push(BlockPresence {
							r#type: BlockPresenceType::DontHave as i32,
							cid: cid.to_bytes(),
						});
					}
				},
			}
		}

		Ok(response.encode_to_vec())
	}
}

/// Bitswap protocol error.
#[derive(Debug, thiserror::Error)]
pub enum BitswapError {
	/// Protobuf decoding error.
	#[error("Failed to decode request: {0}.")]
	DecodeProto(#[from] prost::DecodeError),

	/// Protobuf encoding error.
	#[error("Failed to encode response: {0}.")]
	EncodeProto(#[from] prost::EncodeError),

	/// Client backend error.
	#[error(transparent)]
	Client(#[from] sp_blockchain::Error),

	/// Error parsing CID
	#[error(transparent)]
	BadCid(#[from] cid::Error),

	/// Packet read error.
	#[error(transparent)]
	Read(#[from] io::Error),

	/// Error sending response.
	#[error("Failed to send response.")]
	SendResponse,

	/// Message contains an empty WANT list.
	#[error("Invalid WANT list.")]
	InvalidWantList,

	/// Too many blocks requested.
	#[error("Too many block entries in the request.")]
	TooManyEntries,
}
