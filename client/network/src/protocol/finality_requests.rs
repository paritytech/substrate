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

//! `NetworkBehaviour` implementation which handles incoming finality proof requests.
//!
//! Every request is coming in on a separate connection substream which gets
//! closed after we have sent the response back. Incoming requests are encoded
//! as protocol buffers (cf. `finality.v1.proto`).

#![allow(unused)]

use bytes::Bytes;
use codec::{Encode, Decode};
use crate::{
	chain::FinalityProofProvider,
	config::ProtocolId,
	protocol::{api, message::BlockAttributes}
};
use futures::{future::BoxFuture, prelude::*, stream::FuturesUnordered};
use libp2p::{
	core::{
		ConnectedPoint,
		Multiaddr,
		PeerId,
		connection::ConnectionId,
		upgrade::{InboundUpgrade, ReadOneError, UpgradeInfo, Negotiated},
		upgrade::{DeniedUpgrade, read_one, write_one}
	},
	swarm::{
		NegotiatedSubstream,
		NetworkBehaviour,
		NetworkBehaviourAction,
		OneShotHandler,
		OneShotHandlerConfig,
		PollParameters,
		SubstreamProtocol
	}
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

/// Configuration options for `FinalityProofRequests`.
#[derive(Debug, Clone)]
pub struct Config {
	max_request_len: usize,
	inactivity_timeout: Duration,
	protocol: Bytes,
}

impl Config {
	/// Create a fresh configuration with the following options:
	///
	/// - max. request size = 1 MiB
	/// - inactivity timeout = 15s
	pub fn new(id: &ProtocolId) -> Self {
		let mut c = Config {
			max_request_len: 1024 * 1024,
			inactivity_timeout: Duration::from_secs(15),
			protocol: Bytes::new(),
		};
		c.set_protocol(id);
		c
	}

	/// Limit the max. length of incoming finality proof request bytes.
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
		v.extend_from_slice(b"/finality-proof/1");
		self.protocol = v.into();
		self
	}
}

/// The finality proof request handling behaviour.
pub struct FinalityProofRequests<B: Block> {
	/// This behaviour's configuration.
	config: Config,
	/// How to construct finality proofs.
	finality_proof_provider: Arc<dyn FinalityProofProvider<B>>,
	/// Futures sending back the finality proof request responses.
	outgoing: FuturesUnordered<BoxFuture<'static, ()>>,
}

impl<B> FinalityProofRequests<B>
where
	B: Block,
{
	/// Initializes the behaviour.
	pub fn new(cfg: Config, finality_proof_provider: Arc<dyn FinalityProofProvider<B>>) -> Self {
		FinalityProofRequests {
			config: cfg,
			finality_proof_provider,
			outgoing: FuturesUnordered::new(),
		}
	}

	/// Callback, invoked when a new finality request has been received from remote.
	fn on_finality_request(&mut self, peer: &PeerId, request: &api::v1::finality::FinalityProofRequest)
		-> Result<api::v1::finality::FinalityProofResponse, Error>
	{
		let block_hash = Decode::decode(&mut request.block_hash.as_ref())?;

		log::trace!(target: "sync", "Finality proof request from {} for {}", peer, block_hash);

		let finality_proof = self.finality_proof_provider
			.prove_finality(block_hash, &request.request)?
			.unwrap_or(Vec::new());
		// Note that an empty Vec is sent if no proof is available.

		Ok(api::v1::finality::FinalityProofResponse { proof: finality_proof })
	}
}

impl<B> NetworkBehaviour for FinalityProofRequests<B>
where
	B: Block
{
	type ProtocolsHandler = OneShotHandler<Protocol, DeniedUpgrade, Request<NegotiatedSubstream>>;
	type OutEvent = Void;

	fn new_handler(&mut self) -> Self::ProtocolsHandler {
		let p = Protocol {
			max_request_len: self.config.max_request_len,
			protocol: self.config.protocol.clone(),
		};
		let mut cfg = OneShotHandlerConfig::default();
		cfg.inactive_timeout = self.config.inactivity_timeout;
		OneShotHandler::new(SubstreamProtocol::new(p), cfg)
	}

	fn addresses_of_peer(&mut self, _: &PeerId) -> Vec<Multiaddr> {
		Vec::new()
	}

	fn inject_connected(&mut self, _peer: &PeerId) {
	}

	fn inject_disconnected(&mut self, _peer: &PeerId) {
	}

	fn inject_event(
		&mut self,
		peer: PeerId,
		connection: ConnectionId,
		Request(request, mut stream): Request<NegotiatedSubstream>
	) {
		match self.on_finality_request(&peer, &request) {
			Ok(res) => {
				log::trace!("enqueueing finality response for peer {}", peer);
				let mut data = Vec::with_capacity(res.encoded_len());
				if let Err(e) = res.encode(&mut data) {
					log::debug!("error encoding finality response for peer {}: {}", peer, e)
				} else {
					let future = async move {
						if let Err(e) = write_one(&mut stream, data).await {
							log::debug!("error writing finality response: {}", e)
						}
					};
					self.outgoing.push(future.boxed())
				}
			}
			Err(e) => log::debug!("error handling finality request from peer {}: {}", peer, e)
		}
	}

	fn poll(&mut self, cx: &mut Context, _: &mut impl PollParameters) -> Poll<NetworkBehaviourAction<DeniedUpgrade, Void>> {
		while let Poll::Ready(Some(_)) = self.outgoing.poll_next_unpin(cx) {}
		Poll::Pending
	}
}

/// The incoming finality proof request.
///
/// Holds the protobuf value and the connection substream which made the
/// request and over which to send the response.
#[derive(Debug)]
pub struct Request<T>(api::v1::finality::FinalityProofRequest, T);

impl<T> From<Void> for Request<T> {
	fn from(v: Void) -> Self {
		unreachable(v)
	}
}

/// Substream upgrade protocol.
///
/// We attempt to parse an incoming protobuf encoded request (cf. `Request`)
/// which will be handled by the `FinalityProofRequests` behaviour, i.e. the request
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
		async move {
			let len = self.max_request_len;
			let vec = read_one(&mut s, len).await?;
			match api::v1::finality::FinalityProofRequest::decode(&vec[..]) {
				Ok(r) => Ok(Request(r, s)),
				Err(e) => Err(ReadOneError::Io(io::Error::new(io::ErrorKind::Other, e)))
			}
		}.boxed()
	}
}

