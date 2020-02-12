// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.
//
// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! `NetworkBehaviour` implementation which handles incoming block requests.
//!
//! Every request is coming in on a separate connection substream which gets
//! closed after we have sent the response back. Incoming requests are encoded
//! as protocol buffers (cf. `api.v1.proto`).

#![allow(unused)]

use bytes::Bytes;
use codec::{Encode, Decode};
use crate::{
	chain::Client,
	config::ProtocolId,
	protocol::{api, message::BlockAttributes}
};
use futures::{future::BoxFuture, prelude::*, stream::FuturesUnordered};
use libp2p::{
	core::{
		ConnectedPoint,
		Multiaddr,
		PeerId,
		upgrade::{InboundUpgrade, ReadOneError, UpgradeInfo, Negotiated},
		upgrade::{DeniedUpgrade, read_one, write_one}
	},
	swarm::{NetworkBehaviour, NetworkBehaviourAction, OneShotHandler, PollParameters, SubstreamProtocol}
};
use prost::Message;
use sp_runtime::{generic::BlockId, traits::{Block, Header, One, Zero}};
use std::{
	cmp::min,
	io,
	iter,
	sync::Arc,
	time::Duration,
	task::{Context, Poll}
};
use void::{Void, unreachable};

// Type alias for convenience.
pub type Error = Box<dyn std::error::Error + 'static>;

/// Configuration options for `BlockRequests`.
#[derive(Debug, Clone)]
pub struct Config {
	max_block_data_response: u32,
	max_request_len: usize,
	inactivity_timeout: Duration,
	protocol: Bytes,
}

impl Config {
	/// Create a fresh configuration with the following options:
	///
	/// - max. block data in response = 128
	/// - max. request size = 1 MiB
	/// - inactivity timeout = 15s
	pub fn new(id: &ProtocolId) -> Self {
		let mut c = Config {
			max_block_data_response: 128,
			max_request_len: 1024 * 1024,
			inactivity_timeout: Duration::from_secs(15),
			protocol: Bytes::new(),
		};
		c.set_protocol(id);
		c
	}

	/// Limit the max. number of block data in a response.
	pub fn set_max_block_data_response(&mut self, v: u32) -> &mut Self {
		self.max_block_data_response = v;
		self
	}

	/// Limit the max. length of incoming block request bytes.
	pub fn set_max_request_len(&mut self, v: usize) -> &mut Self {
		self.max_request_len = v;
		self
	}

	/// Limit the max. duration the substream may remain inactive before closing it.
	pub fn set_inactivity_timeout(&mut self, v: Duration) -> &mut Self {
		self.inactivity_timeout = v;
		self
	}

	/// Set protocol to use for upgrade negotiation.
	pub fn set_protocol(&mut self, id: &ProtocolId) -> &mut Self {
		let mut v = Vec::new();
		v.extend_from_slice(b"/");
		v.extend_from_slice(id.as_bytes());
		v.extend_from_slice(b"/sync/1");
		self.protocol = v.into();
		self
	}
}

/// The block request handling behaviour.
pub struct BlockRequests<T, B: Block> {
	/// This behaviour's configuration.
	config: Config,
	/// Blockchain client.
	chain: Arc<dyn Client<B>>,
	/// Futures sending back the block request response.
	outgoing: FuturesUnordered<BoxFuture<'static, ()>>,
	/// Type witness term.
	_marker: std::marker::PhantomData<T>
}

impl<T, B> BlockRequests<T, B>
where
	T: AsyncRead + AsyncWrite + Unpin + Send + 'static,
	B: Block,
{
	pub fn new(cfg: Config, chain: Arc<dyn Client<B>>) -> Self {
		BlockRequests {
			config: cfg,
			chain,
			outgoing: FuturesUnordered::new(),
			_marker: std::marker::PhantomData
		}
	}

	/// Callback, invoked when a new block request has been received from remote.
	fn on_block_request
		( &mut self
		, peer: &PeerId
		, request: &api::v1::BlockRequest
		) -> Result<api::v1::BlockResponse, Error>
	{
		log::trace!("block request {} from peer {}: from block {:?} to block {:?}, max blocks {:?}",
			request.id,
			peer,
			request.from_block,
			request.to_block,
			request.max_blocks);

		let from_block_id =
			match request.from_block {
				Some(api::v1::block_request::FromBlock::Hash(ref h)) => {
					let h = Decode::decode(&mut h.as_ref())?;
					BlockId::<B>::Hash(h)
				}
				Some(api::v1::block_request::FromBlock::Number(ref n)) => {
					let n = Decode::decode(&mut n.as_ref())?;
					BlockId::<B>::Number(n)
				}
				None => {
					let msg = "missing `BlockRequest::from_block` field";
					return Err(io::Error::new(io::ErrorKind::Other, msg).into())
				}
			};

		let max_blocks =
			if request.max_blocks == 0 {
				self.config.max_block_data_response
			} else {
				min(request.max_blocks, self.config.max_block_data_response)
			};

		let direction =
			if request.direction == api::v1::Direction::Ascending as i32 {
				api::v1::Direction::Ascending
			} else if request.direction == api::v1::Direction::Descending as i32 {
				api::v1::Direction::Descending
			} else {
				let msg = format!("invalid `BlockRequest::direction` value: {}", request.direction);
				return Err(io::Error::new(io::ErrorKind::Other, msg).into())
			};

		let attributes = BlockAttributes::decode(&mut request.fields.to_be_bytes().as_ref())?;
		let get_header = attributes.contains(BlockAttributes::HEADER);
		let get_body = attributes.contains(BlockAttributes::BODY);
		let get_justification = attributes.contains(BlockAttributes::JUSTIFICATION);

		let mut blocks = Vec::new();
		let mut block_id = from_block_id;
		while let Some(header) = self.chain.header(&block_id).unwrap_or(None) {
			if blocks.len() >= max_blocks as usize {
				break
			}

			let number = header.number().clone();
			let hash = header.hash();
			let parent_hash = header.parent_hash().clone();

			let block_data = api::v1::BlockData {
				hash: hash.encode(),
				header: if get_header {
					header.encode()
				} else {
					Vec::new()
				},
				body: if get_body {
					self.chain.body(&BlockId::Hash(hash))?
						.unwrap_or(Vec::new())
						.iter_mut()
						.map(|extrinsic| extrinsic.encode())
						.collect()
				} else {
					Vec::new()
				},
				receipt: Vec::new(),
				message_queue: Vec::new(),
				justification: if get_justification {
					self.chain.justification(&BlockId::Hash(hash))?.unwrap_or(Vec::new())
				} else {
					Vec::new()
				}
			};

			blocks.push(block_data);

			match direction {
				api::v1::Direction::Ascending => {
					block_id = BlockId::Number(number + One::one())
				}
				api::v1::Direction::Descending => {
					if number.is_zero() {
						break
					}
					block_id = BlockId::Hash(parent_hash)
				}
			}
		}

		Ok(api::v1::BlockResponse { id: request.id, blocks })
	}
}

impl<T, B> NetworkBehaviour for BlockRequests<T, B>
where
	T: AsyncRead + AsyncWrite + Unpin + Send + 'static,
	B: Block
{
	type ProtocolsHandler = OneShotHandler<T, Protocol, DeniedUpgrade, Request<Negotiated<T>>>;
	type OutEvent = Void;

	fn new_handler(&mut self) -> Self::ProtocolsHandler {
		let p = Protocol {
			max_request_len: self.config.max_request_len,
			protocol: self.config.protocol.clone(),
		};
		OneShotHandler::new(SubstreamProtocol::new(p), self.config.inactivity_timeout)
	}

	fn addresses_of_peer(&mut self, _: &PeerId) -> Vec<Multiaddr> {
		Vec::new()
	}

	fn inject_connected(&mut self, _peer: PeerId, _info: ConnectedPoint) {
	}

	fn inject_disconnected(&mut self, _peer: &PeerId, _info: ConnectedPoint) {
	}

	fn inject_node_event(&mut self, peer: PeerId, Request(request, mut stream): Request<Negotiated<T>>) {
		match self.on_block_request(&peer, &request) {
			Ok(res) => {
				log::trace!("enqueueing block response {} for peer {} with {} blocks", res.id, peer, res.blocks.len());
				let mut data = Vec::with_capacity(res.encoded_len());
				if let Err(e) = res.encode(&mut data) {
					log::debug!("error encoding block response {} for peer {}: {}", res.id, peer, e)
				} else {
					let future = async move {
						if let Err(e) = write_one(&mut stream, data).await {
							log::debug!("error writing block response: {}", e)
						}
					};
					self.outgoing.push(future.boxed())
				}
			}
			Err(e) => log::debug!("error handling block request {} from peer {}: {}", request.id, peer, e)
		}
	}

	fn poll(&mut self, cx: &mut Context, _: &mut impl PollParameters) -> Poll<NetworkBehaviourAction<DeniedUpgrade, Void>> {
		while let Poll::Ready(Some(_)) = self.outgoing.poll_next_unpin(cx) {}
		Poll::Pending
	}
}

/// The incoming block request.
///
/// Holds the protobuf value and the connection substream which made the
/// request and over which to send the response.
#[derive(Debug)]
pub struct Request<T>(api::v1::BlockRequest, T);

impl<T> From<Void> for Request<T> {
	fn from(v: Void) -> Self {
		unreachable(v)
	}
}

/// Substream upgrade protocol.
///
/// We attempt to parse an incoming protobuf encoded request (cf. `Request`)
/// which will be handled by the `BlockRequests` behaviour, i.e. the request
/// will become visible via `inject_node_event` which then dispatches to the
/// relevant callback to process the message and prepare a response.
#[derive(Debug, Clone)]
pub struct Protocol {
	/// The max. request length in bytes.
	max_request_len: usize,
	/// The protocol to use during upgrade negotiation.
	protocol: Bytes,
}

impl UpgradeInfo for Protocol {
    type Info = Bytes;
    type InfoIter = iter::Once<Self::Info>;

    fn protocol_info(&self) -> Self::InfoIter {
        iter::once(self.protocol.clone())
    }
}

impl<T> InboundUpgrade<T> for Protocol
where
	T: AsyncRead + AsyncWrite + Unpin + Send + 'static
{
    type Output = Request<T>;
    type Error = ReadOneError;
    type Future = BoxFuture<'static, Result<Self::Output, Self::Error>>;

    fn upgrade_inbound(self, mut s: T, _: Self::Info) -> Self::Future {
		let future = async move {
			let len = self.max_request_len;
			let vec = read_one(&mut s, len).await?;
			match api::v1::BlockRequest::decode(&vec[..]) {
				Ok(r) => Ok(Request(r, s)),
				Err(e) => Err(ReadOneError::Io(io::Error::new(io::ErrorKind::Other, e)))
			}
		};
		future.boxed()
	}
}

