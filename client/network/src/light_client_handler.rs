// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! [`NetworkBehaviour`] implementation which handles light client requests.
//!
//! Every request is coming in on a separate connection substream which gets
//! closed after we have sent the response back. Requests and responses are
//! encoded as protocol buffers (cf. `api.v1.proto`).
//!
//! For every outgoing request we likewise open a separate substream.

#![allow(unused)]

use bytes::Bytes;
use codec::{self, Encode, Decode};
use crate::{
	chain::Client,
	config::ProtocolId,
	protocol::message::{BlockAttributes, Direction, FromBlock},
	schema,
};
use crate::request_responses::{IncomingRequest, ProtocolConfig, RequestFailure};
use futures::{channel::{mpsc, oneshot}, future::BoxFuture, prelude::*, stream::FuturesUnordered};
use libp2p::{
	core::{
		ConnectedPoint,
		Multiaddr,
		PeerId,
		connection::ConnectionId,
		upgrade::{InboundUpgrade, ReadOneError, UpgradeInfo, Negotiated},
		upgrade::{OutboundUpgrade, read_one, write_one}
	},
	swarm::{
		AddressRecord,
		NegotiatedSubstream,
		NetworkBehaviour,
		NetworkBehaviourAction,
		NotifyHandler,
		OneShotHandler,
		OneShotHandlerConfig,
		PollParameters,
		SubstreamProtocol,
	}
};
use nohash_hasher::IntMap;
use prost::Message;
use sc_client_api::{
	StorageProof,
	light::{
		self, RemoteReadRequest, RemoteBodyRequest, ChangesProof,
		RemoteCallRequest, RemoteChangesRequest, RemoteHeaderRequest,
	}
};
use sc_peerset::{PeersetHandle, ReputationChange};
use sp_core::{
	storage::{ChildInfo, ChildType,StorageKey, PrefixedStorageKey},
	hexdisplay::HexDisplay,
};
use smallvec::SmallVec;
use sp_blockchain::{Error as ClientError};
use sp_runtime::{
	traits::{Block, Header, NumberFor, Zero},
	generic::BlockId,
};
use std::{
	collections::{BTreeMap, VecDeque, HashMap},
	io,
	iter,
	pin::Pin,
	sync::Arc,
	task::{Context, Poll},
	time::Duration,
};
use log::debug;
use void::Void;
use wasm_timer::Instant;

/// Reputation change for a peer when a request timed out.
pub(crate) const TIMEOUT_REPUTATION_CHANGE: i32 = -(1 << 8);
const LOG_TARGET: &str = "light-client-request-handler";

/// Configuration options for `LightClientRequestClient` behaviour.
#[derive(Debug, Clone)]
pub struct Config {
	max_request_size: usize,
	max_response_size: usize,
	max_pending_requests: usize,
	inactivity_timeout: Duration,
	request_timeout: Duration,
	light_protocol: String,
	block_protocol: String,
}

impl Config {
	/// Create a fresh configuration with the following options:
	///
	/// - max. request size = 1 MiB
	/// - max. response size = 16 MiB
	/// - max. pending requests = 128
	/// - inactivity timeout = 15s
	/// - request timeout = 15s
	pub fn new(id: &ProtocolId) -> Self {
		let mut c = Config {
			max_request_size: 1 * 1024 * 1024,
			max_response_size: 16 * 1024 * 1024,
			max_pending_requests: 128,
			inactivity_timeout: Duration::from_secs(15),
			request_timeout: Duration::from_secs(15),
			light_protocol: String::new(),
			block_protocol: String::new(),
		};
		c.set_protocol(id);
		c
	}

	/// Limit the max. length in bytes of a request.
	pub fn set_max_request_size(&mut self, v: usize) -> &mut Self {
		self.max_request_size = v;
		self
	}

	/// Limit the max. length in bytes of a response.
	pub fn set_max_response_size(&mut self, v: usize) -> &mut Self {
		self.max_response_size = v;
		self
	}

	/// Limit the max. number of pending requests.
	pub fn set_max_pending_requests(&mut self, v: usize) -> &mut Self {
		self.max_pending_requests = v;
		self
	}

	/// Limit the max. duration the connection may remain inactive before closing it.
	pub fn set_inactivity_timeout(&mut self, v: Duration) -> &mut Self {
		self.inactivity_timeout = v;
		self
	}

	/// Limit the max. request duration.
	pub fn set_request_timeout(&mut self, v: Duration) -> &mut Self {
		self.request_timeout = v;
		self
	}

	// TODO: Unify this with LightClientRequestHandler.
	/// Set protocol to use for upgrade negotiation.
	pub fn set_protocol(&mut self, id: &ProtocolId) -> &mut Self {
		self.light_protocol = {
			let mut s = String::new();
			s.push_str("/");
			s.push_str(id.as_ref());
			s.push_str("/light/2");
			s
		};

		self.block_protocol = {
			let mut s = String::new();
			s.push_str("/");
			s.push_str(id.as_ref());
			s.push_str("/sync/2");
			s
		};

		self
	}
}

/// The possible light client requests we support.
///
/// The associated `oneshot::Sender` will be used to convey the result of
/// their request back to them (cf. `Reply`).
//
// This is modeled after light_dispatch.rs's `RequestData` which is not
// used because we currently only support a subset of those.
#[derive(Debug)]
pub enum Request<B: Block> {
	Body {
		request: RemoteBodyRequest<B::Header>,
		sender: oneshot::Sender<Result<Vec<B::Extrinsic>, ClientError>>
	},
	Header {
		request: light::RemoteHeaderRequest<B::Header>,
		sender: oneshot::Sender<Result<B::Header, ClientError>>
	},
	Read {
		request: light::RemoteReadRequest<B::Header>,
		sender: oneshot::Sender<Result<HashMap<Vec<u8>, Option<Vec<u8>>>, ClientError>>
	},
	ReadChild {
		request: light::RemoteReadChildRequest<B::Header>,
		sender: oneshot::Sender<Result<HashMap<Vec<u8>, Option<Vec<u8>>>, ClientError>>
	},
	Call {
		request: light::RemoteCallRequest<B::Header>,
		sender: oneshot::Sender<Result<Vec<u8>, ClientError>>
	},
	Changes {
		request: light::RemoteChangesRequest<B::Header>,
		sender: oneshot::Sender<Result<Vec<(NumberFor<B>, u32)>, ClientError>>
	}
}

/// The data to send back to the light client over the oneshot channel.
//
// It is unified here in order to be able to return it as a function
// result instead of delivering it to the client as a side effect of
// response processing.
#[derive(Debug)]
enum Reply<B: Block> {
	VecU8(Vec<u8>),
	VecNumberU32(Vec<(<B::Header as Header>::Number, u32)>),
	MapVecU8OptVecU8(HashMap<Vec<u8>, Option<Vec<u8>>>),
	Header(B::Header),
	Extrinsics(Vec<B::Extrinsic>),
}

/// Augments a light client request with metadata.
#[derive(Debug)]
struct RequestWrapper<B: Block> {
	/// Time when this value was created.
	timestamp: Instant,
	/// Remaining retries.
	retries: usize,
	/// The actual request.
	request: Request<B>,
	/// The peer that the request is send to.
	peer: Option<PeerId>,
}

/// Information we have about some peer.
#[derive(Debug)]
struct PeerInfo<B: Block> {
	best_block: Option<NumberFor<B>>,
	status: PeerStatus,
}

impl<B: Block> Default for PeerInfo<B> {
	fn default() -> Self {
		PeerInfo {
			best_block: None,
			status: PeerStatus::Idle,
		}
	}
}

// TODO: Is the whole concept of request ids still needed?
type RequestId = u64;

/// A peer is either idle or busy processing a request from us.
#[derive(Debug, Clone, PartialEq, Eq)]
enum PeerStatus {
	/// The peer is available.
	Idle,
	/// We wait for the peer to return us a response for the given request ID.
	BusyWith(RequestId),
}

/// Generates a [`ProtocolConfig`] for the light client request protocol, refusing incoming requests.
pub fn generate_protocol_config(protocol_id: ProtocolId) -> ProtocolConfig {
	ProtocolConfig {
		name: generate_protocol_name(protocol_id).into(),
		max_request_size: 1024 * 1024,
		max_response_size: 16 * 1024 * 1024,
		request_timeout: Duration::from_secs(40),
		inbound_queue: None,
	}
}

/// Generate the light client protocol name from chain specific protocol identifier.
fn generate_protocol_name(protocol_id: ProtocolId) -> String {
	let mut s = String::new();
	s.push_str("/");
	s.push_str(protocol_id.as_ref());
	s.push_str("/light/2");
	s
}

pub struct LightClientRequestHandler<B: Block> {
	request_receiver: mpsc::Receiver<IncomingRequest>,
	/// Blockchain client.
	client: Arc<dyn Client<B>>,
	/// Handle to use for reporting misbehaviour of peers.
	peerset: PeersetHandle,
}

impl<B: Block> LightClientRequestHandler<B> {
	/// Create a new [`BlockRequestHandler`].
	pub fn new(protocol_id: ProtocolId, client: Arc<dyn Client<B>>, peerset: PeersetHandle) -> (Self, ProtocolConfig) {
		// TODO: justify 20.
		let (tx, request_receiver) = mpsc::channel(20);

		let mut protocol_config = generate_protocol_config(protocol_id);
		protocol_config.inbound_queue = Some(tx);

		(Self { client, request_receiver, peerset }, protocol_config)
	}

	fn handle_request(
		&mut self,
		peer: PeerId,
		payload: Vec<u8>,
		pending_response: oneshot::Sender<Vec<u8>>
	) -> Result<(), HandleRequestError> {
		let request = schema::v1::light::Request::decode(&payload[..])?;

		let response = match &request.request {
			Some(schema::v1::light::request::Request::RemoteCallRequest(r)) =>
				self.on_remote_call_request(&peer, r)?,
			Some(schema::v1::light::request::Request::RemoteReadRequest(r)) =>
				self.on_remote_read_request(&peer, r)?,
			Some(schema::v1::light::request::Request::RemoteHeaderRequest(r)) =>
				self.on_remote_header_request(&peer, r)?,
			Some(schema::v1::light::request::Request::RemoteReadChildRequest(r)) =>
				self.on_remote_read_child_request(&peer, r)?,
			Some(schema::v1::light::request::Request::RemoteChangesRequest(r)) =>
				self.on_remote_changes_request(&peer, r)?,
			None => {
				log::debug!("ignoring request without request data from peer {}", peer);
				return Ok(())
			}
		};

		log::trace!("enqueueing response for peer {}", peer);
		let mut data = Vec::new();
		response.encode(&mut data)?;
		pending_response.send(data)
			.map_err(|_| HandleRequestError::SendResponse)
	}

	fn on_remote_call_request
		( &mut self
		, peer: &PeerId
		, request: &schema::v1::light::RemoteCallRequest
		) -> Result<schema::v1::light::Response, HandleRequestError>
	{
		log::trace!("remote call request from {} ({} at {:?})",
			peer,
			request.method,
			request.block,
		);

		let block = Decode::decode(&mut request.block.as_ref())?;

		let proof = match self.client.execution_proof(&BlockId::Hash(block), &request.method, &request.data) {
			Ok((_, proof)) => proof,
			Err(e) => {
				log::trace!("remote call request from {} ({} at {:?}) failed with: {}",
					peer,
					request.method,
					request.block,
					e,
				);
				StorageProof::empty()
			}
		};

		let response = {
			let r = schema::v1::light::RemoteCallResponse { proof: proof.encode() };
			schema::v1::light::response::Response::RemoteCallResponse(r)
		};

		Ok(schema::v1::light::Response { response: Some(response) })
	}

	fn on_remote_read_request
		( &mut self
		, peer: &PeerId
		, request: &schema::v1::light::RemoteReadRequest
		) -> Result<schema::v1::light::Response, HandleRequestError>
	{
		if request.keys.is_empty() {
			log::debug!("invalid remote read request sent by {}", peer);
			return Err(HandleRequestError::BadRequest("remote read request without keys"))
		}

		log::trace!("remote read request from {} ({} at {:?})",
			peer,
			fmt_keys(request.keys.first(), request.keys.last()),
			request.block);

		let block = Decode::decode(&mut request.block.as_ref())?;

		let proof = match self.client.read_proof(&BlockId::Hash(block), &mut request.keys.iter().map(AsRef::as_ref)) {
			Ok(proof) => proof,
			Err(error) => {
				log::trace!("remote read request from {} ({} at {:?}) failed with: {}",
					peer,
					fmt_keys(request.keys.first(), request.keys.last()),
					request.block,
					error);
				StorageProof::empty()
			}
		};

		let response = {
			let r = schema::v1::light::RemoteReadResponse { proof: proof.encode() };
			schema::v1::light::response::Response::RemoteReadResponse(r)
		};

		Ok(schema::v1::light::Response { response: Some(response) })
	}

	fn on_remote_read_child_request
		( &mut self
		, peer: &PeerId
		, request: &schema::v1::light::RemoteReadChildRequest
		) -> Result<schema::v1::light::Response, HandleRequestError>
	{
		if request.keys.is_empty() {
			log::debug!("invalid remote child read request sent by {}", peer);
			return Err(HandleRequestError::BadRequest("remove read child request without keys"))
		}

		log::trace!("remote read child request from {} ({} {} at {:?})",
			peer,
			HexDisplay::from(&request.storage_key),
			fmt_keys(request.keys.first(), request.keys.last()),
			request.block);

		let block = Decode::decode(&mut request.block.as_ref())?;

		let prefixed_key = PrefixedStorageKey::new_ref(&request.storage_key);
		let child_info = match ChildType::from_prefixed_key(prefixed_key) {
			Some((ChildType::ParentKeyId, storage_key)) => Ok(ChildInfo::new_default(storage_key)),
			None => Err(sp_blockchain::Error::InvalidChildStorageKey),
		};
		let proof = match child_info.and_then(|child_info| self.client.read_child_proof(
			&BlockId::Hash(block),
			&child_info,
			&mut request.keys.iter().map(AsRef::as_ref)
		)) {
			Ok(proof) => proof,
			Err(error) => {
				log::trace!("remote read child request from {} ({} {} at {:?}) failed with: {}",
					peer,
					HexDisplay::from(&request.storage_key),
					fmt_keys(request.keys.first(), request.keys.last()),
					request.block,
					error);
				StorageProof::empty()
			}
		};

		let response = {
			let r = schema::v1::light::RemoteReadResponse { proof: proof.encode() };
			schema::v1::light::response::Response::RemoteReadResponse(r)
		};

		Ok(schema::v1::light::Response { response: Some(response) })
	}

	fn on_remote_header_request
		( &mut self
		, peer: &PeerId
		, request: &schema::v1::light::RemoteHeaderRequest
		) -> Result<schema::v1::light::Response, HandleRequestError>
	{
		log::trace!("remote header proof request from {} ({:?})", peer, request.block);

		let block = Decode::decode(&mut request.block.as_ref())?;
		let (header, proof) = match self.client.header_proof(&BlockId::Number(block)) {
			Ok((header, proof)) => (header.encode(), proof),
			Err(error) => {
				log::trace!("remote header proof request from {} ({:?}) failed with: {}",
					peer,
					request.block,
					error);
				(Default::default(), StorageProof::empty())
			}
		};

		let response = {
			let r = schema::v1::light::RemoteHeaderResponse { header, proof: proof.encode() };
			schema::v1::light::response::Response::RemoteHeaderResponse(r)
		};

		Ok(schema::v1::light::Response { response: Some(response) })
	}

	fn on_remote_changes_request
		( &mut self
		, peer: &PeerId
		, request: &schema::v1::light::RemoteChangesRequest
		) -> Result<schema::v1::light::Response, HandleRequestError>
	{
		log::trace!("remote changes proof request from {} for key {} ({:?}..{:?})",
			peer,
			if !request.storage_key.is_empty() {
				format!("{} : {}", HexDisplay::from(&request.storage_key), HexDisplay::from(&request.key))
			} else {
				HexDisplay::from(&request.key).to_string()
			},
			request.first,
			request.last);

		let first = Decode::decode(&mut request.first.as_ref())?;
		let last = Decode::decode(&mut request.last.as_ref())?;
		let min = Decode::decode(&mut request.min.as_ref())?;
		let max = Decode::decode(&mut request.max.as_ref())?;
		let key = StorageKey(request.key.clone());
		let storage_key = if request.storage_key.is_empty() {
			None
		} else {
			Some(PrefixedStorageKey::new_ref(&request.storage_key))
		};

		let proof = match self.client.key_changes_proof(first, last, min, max, storage_key, &key) {
			Ok(proof) => proof,
			Err(error) => {
				log::trace!("remote changes proof request from {} for key {} ({:?}..{:?}) failed with: {}",
					peer,
					format!("{} : {}", HexDisplay::from(&request.storage_key), HexDisplay::from(&key.0)),
					request.first,
					request.last,
					error);

				light::ChangesProof::<B::Header> {
					max_block: Zero::zero(),
					proof: Vec::new(),
					roots: BTreeMap::new(),
					roots_proof: StorageProof::empty(),
				}
			}
		};

		let response = {
			let r = schema::v1::light::RemoteChangesResponse {
				max: proof.max_block.encode(),
				proof: proof.proof,
				roots: proof.roots.into_iter()
					.map(|(k, v)| schema::v1::light::Pair { fst: k.encode(), snd: v.encode() })
					.collect(),
				roots_proof: proof.roots_proof.encode(),
			};
			schema::v1::light::response::Response::RemoteChangesResponse(r)
		};

		Ok(schema::v1::light::Response { response: Some(response) })
	}

	pub async fn run(mut self) {
		while let Some(request) = self.request_receiver.next().await {
			let IncomingRequest { peer, payload, pending_response } = request;

			match self.handle_request(peer, payload, pending_response) {
				Ok(()) => debug!(target: LOG_TARGET, "Handled light client request from {}.", peer),
				Err(e) => {
					match e {
						HandleRequestError::BadRequest(_) => {
							self.peerset.report_peer(peer, ReputationChange::new(-(1 << 12), "bad request"))

						}
						_ => {},
					}
					debug!(
						target: LOG_TARGET,
						"Failed to handle light client request from {}: {}",
						peer, e,
					);
				},
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
	#[display(fmt = "Failed to send response.")]
	SendResponse,
	/// A bad request has been received.
	#[display(fmt = "bad request: {}", _0)]
	BadRequest(&'static str),

	// TODO: All of these needed?
	/// Encoding or decoding of some data failed.
	#[display(fmt = "codec error: {}", _0)]
	Codec(codec::Error),
	/// The chain client errored.
	#[display(fmt = "client error: {}", _0)]
	Client(ClientError),
}

#[derive(derive_more::Display, derive_more::From)]
pub enum SendRequestError {
	/// There are currently too many pending request.
	#[display(fmt = "too many pending requests")]
	TooManyRequests,
	/// The response type does not correspond to the issued request.
	#[display(fmt = "unexpected response")]
	UnexpectedResponse,
	/// Encoding or decoding of some data failed.
	#[display(fmt = "codec error: {}", _0)]
	Codec(codec::Error),
	/// The chain client errored.
	#[display(fmt = "client error: {}", _0)]
	Client(ClientError),
}


/// Possible errors while handling light clients.
#[derive(Debug, thiserror::Error)]
pub enum Error {
}

/// The light client handler behaviour.
pub struct LightClientRequestClient<B: Block> {
	/// This behaviour's configuration.
	config: Config,
	/// Verifies that received responses are correct.
	checker: Arc<dyn light::FetchChecker<B>>,
	/// Peer information (addresses, their best block, etc.)
	peers: HashMap<PeerId, PeerInfo<B>>,
	/// Futures sending back response to remote clients.
	responses: FuturesUnordered<BoxFuture<'static, ()>>,
	/// Pending (local) requests.
	pending_requests: VecDeque<RequestWrapper<B>>,
	/// Requests on their way to remote peers.
	//
	// TODO: Consider renaming to requests_pending_response.
	outstanding: FuturesUnordered<BoxFuture<'static, (ExpectedResponseTy, RequestId, RequestWrapper<B>, Result<Vec<u8>, RequestFailure>)>>,
	/// (Local) Request ID counter
	next_request_id: RequestId,
	/// Handle to use for reporting misbehaviour of peers.
	peerset: sc_peerset::PeersetHandle,
}

impl<B: Block> Unpin for LightClientRequestClient<B> {}

impl<B> LightClientRequestClient<B>
where
	B: Block,
{
	/// Construct a new light client handler.
	pub fn new(
		cfg: Config,
		checker: Arc<dyn light::FetchChecker<B>>,
		peerset: sc_peerset::PeersetHandle,
	) -> Self {
		LightClientRequestClient {
			config: cfg,
			checker,
			peers: Default::default(),
			responses: Default::default(),
			pending_requests: Default::default(),
			outstanding: Default::default(),
			next_request_id: 1,
			peerset,
		}
	}

	/// We rely on external information about peers best blocks as we lack the
	/// means to determine it ourselves.
	pub fn update_best_block(&mut self, peer: &PeerId, num: NumberFor<B>) {
		if let Some(info) = self.peers.get_mut(peer) {
			log::trace!("new best block for {:?}: {:?}", peer, num);
			info.best_block = Some(num)
		}
	}

	/// Issue a new light client request.
	pub fn request(&mut self, req: Request<B>) -> Result<(), SendRequestError> {
		if self.pending_requests.len() >= self.config.max_pending_requests {
			return Err(SendRequestError::TooManyRequests)
		}
		let rw = RequestWrapper {
			timestamp: Instant::now(),
			retries: retries(&req),
			request: req,
			peer: None, // we do not know the peer yet
		};
		self.pending_requests.push_back(rw);
		Ok(())
	}

	fn next_request_id(&mut self) -> RequestId {
		let id = self.next_request_id;
		self.next_request_id += 1;
		id
	}

	/// Remove the given peer.
	///
	/// In-flight requests to the given peer might fail and be retried. See
	/// [`<LightClientRequestClient as Stream>::poll_next`].
	fn remove_peer(&mut self, peer: PeerId) {
		self.peers.remove(&peer);
	}

	/// Prepares a request by selecting a suitable peer and connection to send it to.
	///
	/// If there is currently no suitable peer for the request, the given request
	/// is returned as `Err`.
	fn prepare_request(&self, req: RequestWrapper<B>)
		-> Result<(PeerId, RequestWrapper<B>), RequestWrapper<B>>
	{
		let number = required_block(&req.request);

		let mut peer = None;
		for (peer_id, peer_info) in self.peers.iter() {
			if peer_info.status == PeerStatus::Idle {
				match peer_info.best_block {
					Some(n) => if n >= number {
						peer = Some((peer_id, peer_info));
						break
					},
					None => peer = Some((peer_id, peer_info))
				}
			}
		}

		if let Some((peer_id, peer_info)) = peer {
			let rw = RequestWrapper {
				timestamp: req.timestamp,
				retries: req.retries,
				request: req.request,
				peer: Some(*peer_id),
			};
			Ok((*peer_id, rw))
		} else {
			Err(req)
		}
	}

	/// Process a local request's response from remote.
	///
	/// If successful, this will give us the actual, checked data we should be
	/// sending back to the client, otherwise an error.
	fn on_response
		( &mut self
		, peer: PeerId
		, request: &Request<B>
		, response: Response
		) -> Result<Reply<B>, SendRequestError>
	{
		log::trace!("response from {}", peer);
		match response {
			Response::Light(r) => self.on_response_light(peer, request, r),
			Response::Block(r) => self.on_response_block(peer, request, r),
		}
	}

	fn on_response_light
		( &mut self
		, peer: PeerId
		, request: &Request<B>
		, response: schema::v1::light::Response
		) -> Result<Reply<B>, SendRequestError>
	{
		use schema::v1::light::response::Response;
		match response.response {
			Some(Response::RemoteCallResponse(response)) =>
				if let Request::Call { request , .. } = request {
					let proof = Decode::decode(&mut response.proof.as_ref())?;
					let reply = self.checker.check_execution_proof(request, proof)?;
					Ok(Reply::VecU8(reply))
				} else {
					Err(SendRequestError::UnexpectedResponse)
				}
			Some(Response::RemoteReadResponse(response)) =>
				match request {
					Request::Read { request, .. } => {
						let proof = Decode::decode(&mut response.proof.as_ref())?;
						let reply = self.checker.check_read_proof(&request, proof)?;
						Ok(Reply::MapVecU8OptVecU8(reply))
					}
					Request::ReadChild { request, .. } => {
						let proof = Decode::decode(&mut response.proof.as_ref())?;
						let reply = self.checker.check_read_child_proof(&request, proof)?;
						Ok(Reply::MapVecU8OptVecU8(reply))
					}
					_ => Err(SendRequestError::UnexpectedResponse)
				}
			Some(Response::RemoteChangesResponse(response)) =>
				if let Request::Changes { request, .. } = request {
					let max_block = Decode::decode(&mut response.max.as_ref())?;
					let roots_proof = Decode::decode(&mut response.roots_proof.as_ref())?;
					let roots = {
						let mut r = BTreeMap::new();
						for pair in response.roots {
							let k = Decode::decode(&mut pair.fst.as_ref())?;
							let v = Decode::decode(&mut pair.snd.as_ref())?;
							r.insert(k, v);
						}
						r
					};
					let reply = self.checker.check_changes_proof(&request, light::ChangesProof {
						max_block,
						proof: response.proof,
						roots,
						roots_proof,
					})?;
					Ok(Reply::VecNumberU32(reply))
				} else {
					Err(SendRequestError::UnexpectedResponse)
				}
			Some(Response::RemoteHeaderResponse(response)) =>
				if let Request::Header { request, .. } = request {
					let header =
						if response.header.is_empty() {
							None
						} else {
							Some(Decode::decode(&mut response.header.as_ref())?)
						};
					let proof = Decode::decode(&mut response.proof.as_ref())?;
					let reply = self.checker.check_header_proof(&request, header, proof)?;
					Ok(Reply::Header(reply))
				} else {
					Err(SendRequestError::UnexpectedResponse)
				}
			None => Err(SendRequestError::UnexpectedResponse)
		}
	}

	fn on_response_block
		( &mut self
		, peer: PeerId
		, request: &Request<B>
		, response: schema::v1::BlockResponse
		) -> Result<Reply<B>, SendRequestError>
	{
		let request = if let Request::Body { request , .. } = &request {
			request
		} else {
			return Err(SendRequestError::UnexpectedResponse);
		};

		let body: Vec<_> = match response.blocks.into_iter().next() {
			Some(b) => b.body,
			None => return Err(SendRequestError::UnexpectedResponse),
		};

		let body = body.into_iter()
			.map(|mut extrinsic| B::Extrinsic::decode(&mut &extrinsic[..]))
			.collect::<Result<_, _>>()?;

		let body = self.checker.check_body_proof(&request, body)?;
		Ok(Reply::Extrinsics(body))
	}

}

impl<B> LightClientRequestClient<B>
where
	B: Block
{
	pub fn inject_connected(&mut self, peer: PeerId) {
		let prev_entry = self.peers.insert(peer, Default::default());
		debug_assert!(
			prev_entry.is_none(),
			"Expect `inject_connected` to be called for disconnected peer.",
		);
	}

	pub fn inject_disconnected(&mut self, peer: PeerId) {
		self.remove_peer(peer)
	}
}

pub enum OutEvent {
	Request {
		target: PeerId,
		request: Vec<u8>,
		pending_response: oneshot::Sender<Result<Vec<u8>, RequestFailure>>,
		protocol_name: String,
	}
}


impl<B: Block> Stream for LightClientRequestClient<B> {
	type Item = OutEvent;

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
		// Process response sending futures.
		while let Poll::Ready(Some(_)) = self.responses.poll_next_unpin(cx) {}

		// If we have a pending request to send, try to find an available peer and send it.
		let now = Instant::now();
		while let Some(mut request) = self.pending_requests.pop_front() {
			if now > request.timestamp + self.config.request_timeout {
				if request.retries == 0 {
					send_reply(Err(ClientError::RemoteFetchFailed), request.request);
					continue
				}
				request.timestamp = Instant::now();
				request.retries -= 1
			}


			match self.prepare_request(request) {
				Err(request) => {
					self.pending_requests.push_front(request);
					log::debug!("no peer available to send request to");
					break
				}
				Ok((peer, request)) => {
					let request_bytes = match serialize_request(&request.request) {
						Ok(bytes) => bytes,
						Err(error) => {
							log::debug!("failed to serialize request: {}", error);
							send_reply(Err(ClientError::RemoteFetchFailed), request.request);
							continue
						}
					};

					let (expected, protocol) = match request.request {
						Request::Body { .. } =>
							(ExpectedResponseTy::Block, self.config.block_protocol.clone()),
						_ =>
							(ExpectedResponseTy::Light, self.config.light_protocol.clone()),
					};

					let (tx, rx) = oneshot::channel();

					let request_id = self.next_request_id();
					if let Some(p) = self.peers.get_mut(&peer) {
						p.status = PeerStatus::BusyWith(request_id);
					}

					self.outstanding.push(async move {
						(expected, request_id, request, rx.await.unwrap())
					}.boxed());

					return Poll::Ready(Some(OutEvent::Request {
						target: peer,
						request: request_bytes,
						pending_response: tx,
						protocol_name: protocol,
					}));
				}
			}
		}

		while let Poll::Ready(Some((expected, id, request_wrapper, response))) = self.outstanding.poll_next_unpin(cx) {
			let peer = request_wrapper.peer;
			// TODO: handle unwrap. Or is it needed in the first place?
			if let Some(info) = self.peers.get_mut(&request_wrapper.peer.unwrap()) {
				if info.status != PeerStatus::BusyWith(id) {
					// If we get here, something is wrong with our internal handling of peer
					// status information. At any time, a single peer processes at most one
					// request from us and its status should contain the request ID we are
					// expecting a response for. If a peer would send us a response with a
					// random ID, we should not have an entry for it with this peer ID in
					// our `outstanding` map, so a malicious peer should not be able to get
					// us here. It is our own fault and must be fixed!
					// TODO: handle unwrap. Or is it needed in the first place?
					panic!("unexpected peer status {:?} for {}", info.status, request_wrapper.peer.unwrap());
				}

				info.status = PeerStatus::Idle; // Make peer available again.
			}

			let response = match response {
				Ok(response) => {
					match expected {
						ExpectedResponseTy::Light => {
							schema::v1::light::Response::decode(&response[..])
								.map(|r| Response::Light(r))
								.map_err(|e| {
									ReadOneError::Io(io::Error::new(io::ErrorKind::Other, e))
								})
						},
						ExpectedResponseTy::Block => {
							schema::v1::BlockResponse::decode(&response[..])
								.map(|r| Response::Block(r))
								.map_err(|e| {
									ReadOneError::Io(io::Error::new(io::ErrorKind::Other, e))
								})
						}
					}
				}
				Err(e) => {
					unimplemented!();

					self.remove_peer(request_wrapper.peer.unwrap());
					self.peerset.report_peer(request_wrapper.peer.unwrap(),
											 ReputationChange::new(TIMEOUT_REPUTATION_CHANGE, "light request timeout"));
					if request_wrapper.retries == 0 {
						send_reply(Err(ClientError::RemoteFetchFailed), request_wrapper.request);
						continue
					}
					let request_wrapper = RequestWrapper {
						timestamp: Instant::now(),
						retries: request_wrapper.retries - 1,
						request: request_wrapper.request,
						peer: None,
					};
					self.pending_requests.push_back(request_wrapper);
					continue;
				}
			};

			match self.on_response(peer.unwrap(), &request_wrapper.request, response.unwrap()) {
				Ok(reply) => send_reply(Ok(reply), request_wrapper.request),
				Err(SendRequestError::UnexpectedResponse) => {
					log::debug!("unexpected response {} from peer {}", id, peer.unwrap());
					self.remove_peer(peer.unwrap());
					self.peerset.report_peer(peer.unwrap(), ReputationChange::new_fatal("unexpected response from peer"));
					let request_wrapper = RequestWrapper {
						timestamp: request_wrapper.timestamp,
						retries: request_wrapper.retries,
						request: request_wrapper.request,
						peer: None,
					};
					self.pending_requests.push_back(request_wrapper);
				}
				Err(other) => {
					log::debug!("error handling response {} from peer {}: {}", id, peer.unwrap(), other);
					self.remove_peer(peer.unwrap());
					self.peerset.report_peer(peer.unwrap(), ReputationChange::new_fatal("invalid response from peer"));
					if request_wrapper.retries > 0 {
						let request_wrapper = RequestWrapper {
							timestamp: request_wrapper.timestamp,
							retries: request_wrapper.retries - 1,
							request: request_wrapper.request,
							peer: None,
						};
						self.pending_requests.push_back(request_wrapper)
					} else {
						send_reply(Err(ClientError::RemoteFetchFailed), request_wrapper.request)
					}
				}
			}
		}

		Poll::Pending
	}
}

fn required_block<B: Block>(request: &Request<B>) -> NumberFor<B> {
	match request {
		Request::Body { request, .. } => *request.header.number(),
		Request::Header { request, .. } => request.block,
		Request::Read { request, .. } => *request.header.number(),
		Request::ReadChild { request, .. } => *request.header.number(),
		Request::Call { request, .. } => *request.header.number(),
		Request::Changes { request, .. } => request.max_block.0,
	}
}

fn retries<B: Block>(request: &Request<B>) -> usize {
	let rc = match request {
		Request::Body { request, .. } => request.retry_count,
		Request::Header { request, .. } => request.retry_count,
		Request::Read { request, .. } => request.retry_count,
		Request::ReadChild { request, .. } => request.retry_count,
		Request::Call { request, .. } => request.retry_count,
		Request::Changes { request, .. } => request.retry_count,
	};
	rc.unwrap_or(0)
}

fn serialize_request<B: Block>(request: &Request<B>) -> Result<Vec<u8>, prost::EncodeError> {
	let request = match request {
		Request::Body { request, .. } => {
			let rq = schema::v1::BlockRequest {
				fields: BlockAttributes::BODY.to_be_u32(),
				from_block: Some(schema::v1::block_request::FromBlock::Hash(
					request.header.hash().encode(),
				)),
				to_block: Default::default(),
				direction: schema::v1::Direction::Ascending as i32,
				max_blocks: 1,
			};

			let mut buf = Vec::with_capacity(rq.encoded_len());
			rq.encode(&mut buf)?;
			return Ok(buf);
		}
		Request::Header { request, .. } => {
			let r = schema::v1::light::RemoteHeaderRequest { block: request.block.encode() };
			schema::v1::light::request::Request::RemoteHeaderRequest(r)
		}
		Request::Read { request, .. } => {
			let r = schema::v1::light::RemoteReadRequest {
				block: request.block.encode(),
				keys: request.keys.clone(),
			};
			schema::v1::light::request::Request::RemoteReadRequest(r)
		}
		Request::ReadChild { request, .. } => {
			let r = schema::v1::light::RemoteReadChildRequest {
				block: request.block.encode(),
				storage_key: request.storage_key.clone().into_inner(),
				keys: request.keys.clone(),
			};
			schema::v1::light::request::Request::RemoteReadChildRequest(r)
		}
		Request::Call { request, .. } => {
			let r = schema::v1::light::RemoteCallRequest {
				block: request.block.encode(),
				method: request.method.clone(),
				data: request.call_data.clone(),
			};
			schema::v1::light::request::Request::RemoteCallRequest(r)
		}
		Request::Changes { request, .. } => {
			let r = schema::v1::light::RemoteChangesRequest {
				first: request.first_block.1.encode(),
				last: request.last_block.1.encode(),
				min: request.tries_roots.1.encode(),
				max: request.max_block.1.encode(),
				storage_key: request.storage_key.clone().map(|s| s.into_inner())
					.unwrap_or_default(),
				key: request.key.clone(),
			};
			schema::v1::light::request::Request::RemoteChangesRequest(r)
		}
	};

	let rq = schema::v1::light::Request { request: Some(request) };
	let mut buf = Vec::with_capacity(rq.encoded_len());
	rq.encode(&mut buf)?;
	Ok(buf)
}

fn send_reply<B: Block>(result: Result<Reply<B>, ClientError>, request: Request<B>) {
	fn send<T>(item: T, sender: oneshot::Sender<T>) {
		let _ = sender.send(item); // It is okay if the other end already hung up.
	}
	match request {
		Request::Body { request, sender } => match result {
			Err(e) => send(Err(e), sender),
			Ok(Reply::Extrinsics(x)) => send(Ok(x), sender),
			reply => log::error!("invalid reply for body request: {:?}, {:?}", reply, request),
		}
		Request::Header { request, sender } => match result {
			Err(e) => send(Err(e), sender),
			Ok(Reply::Header(x)) => send(Ok(x), sender),
			reply => log::error!("invalid reply for header request: {:?}, {:?}", reply, request),
		}
		Request::Read { request, sender } => match result {
			Err(e) => send(Err(e), sender),
			Ok(Reply::MapVecU8OptVecU8(x)) => send(Ok(x), sender),
			reply => log::error!("invalid reply for read request: {:?}, {:?}", reply, request),
		}
		Request::ReadChild { request, sender } => match result {
			Err(e) => send(Err(e), sender),
			Ok(Reply::MapVecU8OptVecU8(x)) => send(Ok(x), sender),
			reply => log::error!("invalid reply for read child request: {:?}, {:?}", reply, request),
		}
		Request::Call { request, sender } => match result {
			Err(e) => send(Err(e), sender),
			Ok(Reply::VecU8(x)) => send(Ok(x), sender),
			reply => log::error!("invalid reply for call request: {:?}, {:?}", reply, request),
		}
		Request::Changes { request, sender } => match result {
			Err(e) => send(Err(e), sender),
			Ok(Reply::VecNumberU32(x)) => send(Ok(x), sender),
			reply => log::error!("invalid reply for changes request: {:?}, {:?}", reply, request),
		}
	}
}

/// Output type of inbound and outbound substream upgrades.
#[derive(Debug)]
pub enum Event<T> {
	/// Incoming request from remote and substream to use for the response.
	Request(schema::v1::light::Request, T),
	/// Incoming response from remote.
	Response(RequestId, Response),
}

/// Incoming response from remote.
#[derive(Debug, Clone)]
pub enum Response {
	/// Incoming light response from remote.
	Light(schema::v1::light::Response),
	/// Incoming block response from remote.
	Block(schema::v1::BlockResponse),
}

/// Substream upgrade protocol.
///
/// Sends a request to remote and awaits the response.
#[derive(Debug, Clone)]
pub struct OutboundProtocol {
	/// The serialized protobuf request.
	request: Vec<u8>,
	/// Local identifier for the request. Used to associate it with a response.
	request_id: RequestId,
	/// Kind of response expected for this request.
	expected: ExpectedResponseTy,
	/// The max. response length in bytes.
	max_response_size: usize,
	/// The protocol to use for upgrade negotiation.
	protocol: Bytes,
}

/// Type of response expected from the remote for this request.
#[derive(Debug, Clone)]
enum ExpectedResponseTy {
	Light,
	Block,
}

impl UpgradeInfo for OutboundProtocol {
	type Info = Bytes;
	type InfoIter = iter::Once<Self::Info>;

	fn protocol_info(&self) -> Self::InfoIter {
		iter::once(self.protocol.clone())
	}
}


fn fmt_keys(first: Option<&Vec<u8>>, last: Option<&Vec<u8>>) -> String {
	if let (Some(first), Some(last)) = (first, last) {
		if first == last {
			HexDisplay::from(first).to_string()
		} else {
			format!("{}..{}", HexDisplay::from(first), HexDisplay::from(last))
		}
	} else {
		String::from("n/a")
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use async_std::task;
	use assert_matches::assert_matches;
	use codec::Encode;
	use crate::{
		chain::Client,
		config::ProtocolId,
		schema,
	};
	use futures::{channel::oneshot, prelude::*};
	use libp2p::{
		PeerId,
		Multiaddr,
		core::{
			ConnectedPoint,
			connection::ConnectionId,
			identity,
			muxing::{StreamMuxerBox, SubstreamRef},
			transport::{Transport, Boxed, memory::MemoryTransport},
			upgrade
		},
		noise::{self, Keypair, X25519, NoiseConfig},
		swarm::{NetworkBehaviour, NetworkBehaviourAction, PollParameters},
		yamux
	};
	use sc_client_api::{StorageProof, RemoteReadChildRequest, FetchChecker};
	use sp_blockchain::{Error as ClientError};
	use sp_core::storage::ChildInfo;
	use std::{
		collections::{HashMap, HashSet},
		io,
		iter::{self, FromIterator},
		pin::Pin,
		sync::Arc,
		task::{Context, Poll}
	};
	use sp_runtime::{generic::Header, traits::{BlakeTwo256, Block as BlockT, NumberFor}};
	use super::{Event, LightClientRequestClient, Request, Response, OutboundProtocol, PeerStatus};
	use void::Void;

	type Block = sp_runtime::generic::Block<Header<u64, BlakeTwo256>, substrate_test_runtime::Extrinsic>;
	type Handler = LightClientRequestClient<Block>;
	type Swarm = libp2p::swarm::Swarm<Handler>;

	fn empty_proof() -> Vec<u8> {
		StorageProof::empty().encode()
	}

	fn make_swarm(ok: bool, ps: sc_peerset::PeersetHandle, cf: super::Config) -> Swarm {
		let client = Arc::new(substrate_test_runtime_client::new());
		let checker = Arc::new(DummyFetchChecker { ok, _mark: std::marker::PhantomData });
		let id_key = identity::Keypair::generate_ed25519();
		let dh_key = Keypair::<X25519>::new().into_authentic(&id_key).unwrap();
		let local_peer = id_key.public().into_peer_id();
		let transport = MemoryTransport::default()
			.upgrade(upgrade::Version::V1)
			.authenticate(NoiseConfig::xx(dh_key).into_authenticated())
			.multiplex(yamux::YamuxConfig::default())
			.boxed();
		Swarm::new(transport, LightClientRequestClient::new(cf, client, checker, ps), local_peer)
	}

	struct DummyFetchChecker<B> {
		ok: bool,
		_mark: std::marker::PhantomData<B>
	}

	impl<B: BlockT> light::FetchChecker<B> for DummyFetchChecker<B> {
		fn check_header_proof(
			&self,
			_request: &RemoteHeaderRequest<B::Header>,
			header: Option<B::Header>,
			_remote_proof: StorageProof,
		) -> Result<B::Header, ClientError> {
			match self.ok {
				true if header.is_some() => Ok(header.unwrap()),
				_ => Err(ClientError::Backend("Test error".into())),
			}
		}

		fn check_read_proof(
			&self,
			request: &RemoteReadRequest<B::Header>,
			_: StorageProof,
		) -> Result<HashMap<Vec<u8>, Option<Vec<u8>>>, ClientError> {
			match self.ok {
				true => Ok(request.keys
					.iter()
					.cloned()
					.map(|k| (k, Some(vec![42])))
					.collect()
				),
				false => Err(ClientError::Backend("Test error".into())),
			}
		}

		fn check_read_child_proof(
			&self,
			request: &RemoteReadChildRequest<B::Header>,
			_: StorageProof,
		) -> Result<HashMap<Vec<u8>, Option<Vec<u8>>>, ClientError> {
			match self.ok {
				true => Ok(request.keys
					.iter()
					.cloned()
					.map(|k| (k, Some(vec![42])))
					.collect()
				),
				false => Err(ClientError::Backend("Test error".into())),
			}
		}

		fn check_execution_proof(
			&self,
			_: &RemoteCallRequest<B::Header>,
			_: StorageProof,
		) -> Result<Vec<u8>, ClientError> {
			match self.ok {
				true => Ok(vec![42]),
				false => Err(ClientError::Backend("Test error".into())),
			}
		}

		fn check_changes_proof(
			&self,
			_: &RemoteChangesRequest<B::Header>,
			_: ChangesProof<B::Header>
		) -> Result<Vec<(NumberFor<B>, u32)>, ClientError> {
			match self.ok {
				true => Ok(vec![(100u32.into(), 2)]),
				false => Err(ClientError::Backend("Test error".into())),
			}
		}

		fn check_body_proof(
			&self,
			_: &RemoteBodyRequest<B::Header>,
			body: Vec<B::Extrinsic>
		) -> Result<Vec<B::Extrinsic>, ClientError> {
			match self.ok {
				true => Ok(body),
				false => Err(ClientError::Backend("Test error".into())),
			}
		}
	}

	fn make_config() -> super::Config {
		super::Config::new(&ProtocolId::from("foo"))
	}

	fn dummy_header() -> sp_test_primitives::Header {
		sp_test_primitives::Header {
			parent_hash: Default::default(),
			number: 0,
			state_root: Default::default(),
			extrinsics_root: Default::default(),
			digest: Default::default(),
		}
	}

	struct EmptyPollParams(PeerId);

	impl PollParameters for EmptyPollParams {
		type SupportedProtocolsIter = iter::Empty<Vec<u8>>;
		type ListenedAddressesIter = iter::Empty<Multiaddr>;
		type ExternalAddressesIter = iter::Empty<AddressRecord>;

		fn supported_protocols(&self) -> Self::SupportedProtocolsIter {
			iter::empty()
		}

		fn listened_addresses(&self) -> Self::ListenedAddressesIter {
			iter::empty()
		}

		fn external_addresses(&self) -> Self::ExternalAddressesIter {
			iter::empty()
		}

		fn local_peer_id(&self) -> &PeerId {
			&self.0
		}
	}

	fn peerset() -> (sc_peerset::Peerset, sc_peerset::PeersetHandle) {
		let cfg = sc_peerset::SetConfig {
			in_peers: 128,
			out_peers: 128,
			bootnodes: Default::default(),
			reserved_only: false,
			reserved_nodes: Default::default(),
		};
		sc_peerset::Peerset::from_config(sc_peerset::PeersetConfig{ sets: vec![cfg] })
	}

	fn make_behaviour
		( ok: bool
		, ps: sc_peerset::PeersetHandle
		, cf: super::Config
		) -> LightClientRequestClient<Block>
	{
		let client = Arc::new(substrate_test_runtime_client::new());
		let checker = Arc::new(DummyFetchChecker { ok, _mark: std::marker::PhantomData });
		LightClientRequestClient::new(cf, client, checker, ps)
	}

	fn empty_dialer() -> ConnectedPoint {
		ConnectedPoint::Dialer { address: Multiaddr::empty() }
	}

	fn poll(mut b: &mut LightClientRequestClient<Block>) -> Poll<NetworkBehaviourAction<OutboundProtocol, Void>> {
		let mut p = EmptyPollParams(PeerId::random());
		match future::poll_fn(|cx| Pin::new(&mut b).poll(cx, &mut p)).now_or_never() {
			Some(a) => Poll::Ready(a),
			None    => Poll::Pending
		}
	}

	#[test]
	fn disconnects_from_peer_if_told() {
		let peer = PeerId::random();
		let pset = peerset();
		let mut behaviour = make_behaviour(true, pset.1, make_config());

		behaviour.inject_connection_established(&peer, &ConnectionId::new(1), &empty_dialer());
		behaviour.inject_connected(&peer);
		assert_eq!(1, behaviour.peers.len());

		behaviour.inject_connection_closed(&peer, &ConnectionId::new(1), &empty_dialer());
		behaviour.inject_disconnected(&peer);
		assert_eq!(0, behaviour.peers.len())
	}

	#[test]
	fn disconnects_from_peer_if_request_times_out() {
		let peer0 = PeerId::random();
		let peer1 = PeerId::random();
		let pset = peerset();
		let mut behaviour = make_behaviour(true, pset.1, make_config());

		behaviour.inject_connection_established(&peer0, &ConnectionId::new(1), &empty_dialer());
		behaviour.inject_connected(&peer0);
		behaviour.inject_connection_established(&peer1, &ConnectionId::new(2), &empty_dialer());
		behaviour.inject_connected(&peer1);

		// We now know about two peers.
		assert_eq!(HashSet::from_iter(&[peer0.clone(), peer1.clone()]), behaviour.peers.keys().collect::<HashSet<_>>());

		// No requests have been made yet.
		assert!(behaviour.pending_requests.is_empty());
		assert!(behaviour.outstanding.is_empty());

		// Issue our first request!
		let chan = oneshot::channel();
		let request = light::RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: Some(1),
		};
		behaviour.request(Request::Call { request, sender: chan.0 }).unwrap();
		assert_eq!(1, behaviour.pending_requests.len());

		// The behaviour should now attempt to send the request.
		assert_matches!(poll(&mut behaviour), Poll::Ready(NetworkBehaviourAction::NotifyHandler { peer_id, .. }) => {
			assert!(peer_id == peer0 || peer_id == peer1)
		});

		// And we should have one busy peer.
		assert!({
			let (idle, busy): (Vec<_>, Vec<_>) =
				behaviour.peers.iter().partition(|(_, info)| info.status == PeerStatus::Idle);

			idle.len() == 1 && busy.len() == 1
				&& (idle[0].0 == &peer0 || busy[0].0 == &peer0)
				&& (idle[0].0 == &peer1 || busy[0].0 == &peer1)
		});

		// No more pending requests, but one should be outstanding.
		assert_eq!(0, behaviour.pending_requests.len());
		assert_eq!(1, behaviour.outstanding.len());

		// We now set back the timestamp of the outstanding request to make it expire.
		let request = behaviour.outstanding.values_mut().next().unwrap();
		request.timestamp -= make_config().request_timeout;

		// Make progress, but do not expect some action.
		assert_matches!(poll(&mut behaviour), Poll::Pending);

		// The request should have timed out by now and the corresponding peer be removed.
		assert_eq!(1, behaviour.peers.len());
		// Since we asked for one retry, the request should be back in the pending queue.
		assert_eq!(1, behaviour.pending_requests.len());
		// No other request should be ongoing.
		assert_eq!(0, behaviour.outstanding.len());
	}

	#[test]
	fn disconnects_from_peer_on_incorrect_response() {
		let peer = PeerId::random();
		let pset = peerset();
		let mut behaviour = make_behaviour(false, pset.1, make_config());
		//                                 ^--- Making sure the response data check fails.

		let conn = ConnectionId::new(1);
		behaviour.inject_connection_established(&peer, &conn, &empty_dialer());
		behaviour.inject_connected(&peer);
		assert_eq!(1, behaviour.peers.len());

		let chan = oneshot::channel();
		let request = light::RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: Some(1),
		};
		behaviour.request(Request::Call { request, sender: chan.0 }).unwrap();

		assert_eq!(1, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len());
		poll(&mut behaviour); // Make progress
		assert_eq!(0, behaviour.pending_requests.len());
		assert_eq!(1, behaviour.outstanding.len());

		let request_id = *behaviour.outstanding.keys().next().unwrap();

		let response = {
			let r = schema::v1::light::RemoteCallResponse { proof: empty_proof() };
			schema::v1::light::Response {
				response: Some(schema::v1::light::response::Response::RemoteCallResponse(r)),
			}
		};

		behaviour.inject_event(peer.clone(), conn, Event::Response(request_id, Response::Light(response)));
		assert!(behaviour.peers.is_empty());

		poll(&mut behaviour); // More progress

		// The request should be back in the pending queue
		assert_eq!(1, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len());
	}

	#[test]
	fn disconnects_from_peer_on_unexpected_response() {
		let peer = PeerId::random();
		let pset = peerset();
		let mut behaviour = make_behaviour(true, pset.1, make_config());

		let conn = ConnectionId::new(1);
		behaviour.inject_connection_established(&peer, &conn, &empty_dialer());
		behaviour.inject_connected(&peer);
		assert_eq!(1, behaviour.peers.len());
		assert_eq!(0, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len());

		// Some unsolicited response
		let response = {
			let r = schema::v1::light::RemoteCallResponse { proof: empty_proof() };
			schema::v1::light::Response {
				response: Some(schema::v1::light::response::Response::RemoteCallResponse(r)),
			}
		};

		behaviour.inject_event(peer.clone(), conn, Event::Response(2347895932, Response::Light(response)));

		assert!(behaviour.peers.is_empty());
		poll(&mut behaviour);
		assert_eq!(0, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len());
	}

	#[test]
	fn disconnects_from_peer_on_wrong_response_type() {
		let peer = PeerId::random();
		let pset = peerset();
		let mut behaviour = make_behaviour(true, pset.1, make_config());

		let conn = ConnectionId::new(1);
		behaviour.inject_connection_established(&peer, &conn, &empty_dialer());
		behaviour.inject_connected(&peer);
		assert_eq!(1, behaviour.peers.len());

		let chan = oneshot::channel();
		let request = light::RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: Some(1),
		};
		behaviour.request(Request::Call { request, sender: chan.0 }).unwrap();

		assert_eq!(1, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len());
		poll(&mut behaviour); // Make progress
		assert_eq!(0, behaviour.pending_requests.len());
		assert_eq!(1, behaviour.outstanding.len());

		let request_id = *behaviour.outstanding.keys().next().unwrap();

		let response = {
			let r = schema::v1::light::RemoteReadResponse { proof: empty_proof() }; // Not a RemoteCallResponse!
			schema::v1::light::Response {
				response: Some(schema::v1::light::response::Response::RemoteReadResponse(r)),
			}
		};

		behaviour.inject_event(peer.clone(), conn, Event::Response(request_id, Response::Light(response)));
		assert!(behaviour.peers.is_empty());

		poll(&mut behaviour); // More progress

		// The request should be back in the pending queue
		assert_eq!(1, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len());
	}

	#[test]
	fn receives_remote_failure_after_retry_count_failures() {
		let peer1 = PeerId::random();
		let peer2 = PeerId::random();
		let peer3 = PeerId::random();
		let peer4 = PeerId::random();
		let pset = peerset();
		let mut behaviour = make_behaviour(false, pset.1, make_config());
		//                                 ^--- Making sure the response data check fails.

		let conn1 = ConnectionId::new(1);
		behaviour.inject_connection_established(&peer1, &conn1, &empty_dialer());
		behaviour.inject_connected(&peer1);
		let conn2 = ConnectionId::new(2);
		behaviour.inject_connection_established(&peer2, &conn2, &empty_dialer());
		behaviour.inject_connected(&peer2);
		let conn3 = ConnectionId::new(3);
		behaviour.inject_connection_established(&peer3, &conn3, &empty_dialer());
		behaviour.inject_connected(&peer3);
		let conn4 = ConnectionId::new(3);
		behaviour.inject_connection_established(&peer4, &conn4, &empty_dialer());
		behaviour.inject_connected(&peer4);
		assert_eq!(4, behaviour.peers.len());

		let mut chan = oneshot::channel();
		let request = light::RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: Some(3), // Attempt up to three retries.
		};
		behaviour.request(Request::Call { request, sender: chan.0 }).unwrap();

		assert_eq!(1, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len());
		assert_matches!(poll(&mut behaviour), Poll::Ready(NetworkBehaviourAction::NotifyHandler { .. }));
		assert_eq!(0, behaviour.pending_requests.len());
		assert_eq!(1, behaviour.outstanding.len());

		for i in 1 ..= 3 {
			// Construct an invalid response
			let request_id = *behaviour.outstanding.keys().next().unwrap();
			let responding_peer = behaviour.outstanding.values().next().unwrap().peer.clone();
			let response = {
				let r = schema::v1::light::RemoteCallResponse { proof: empty_proof() };
				schema::v1::light::Response {
					response: Some(schema::v1::light::response::Response::RemoteCallResponse(r))
				}
			};
			let conn = ConnectionId::new(i);
			behaviour.inject_event(responding_peer, conn, Event::Response(request_id, Response::Light(response.clone())));
			assert_matches!(poll(&mut behaviour), Poll::Ready(NetworkBehaviourAction::NotifyHandler { .. }));
			assert_matches!(chan.1.try_recv(), Ok(None))
		}
		// Final invalid response
		let request_id = *behaviour.outstanding.keys().next().unwrap();
		let responding_peer = behaviour.outstanding.values().next().unwrap().peer.clone();
		let response = {
			let r = schema::v1::light::RemoteCallResponse { proof: empty_proof() };
			schema::v1::light::Response {
				response: Some(schema::v1::light::response::Response::RemoteCallResponse(r)),
			}
		};
		behaviour.inject_event(responding_peer, conn4, Event::Response(request_id, Response::Light(response)));
		assert_matches!(poll(&mut behaviour), Poll::Pending);
		assert_matches!(chan.1.try_recv(), Ok(Some(Err(ClientError::RemoteFetchFailed))))
	}

	fn issue_request(request: Request<Block>) {
		let peer = PeerId::random();
		let pset = peerset();
		let mut behaviour = make_behaviour(true, pset.1, make_config());

		let conn = ConnectionId::new(1);
		behaviour.inject_connection_established(&peer, &conn, &empty_dialer());
		behaviour.inject_connected(&peer);
		assert_eq!(1, behaviour.peers.len());

		let response = match request {
			Request::Body { .. } => unimplemented!(),
			Request::Header{..} => {
				let r = schema::v1::light::RemoteHeaderResponse {
					header: dummy_header().encode(),
					proof: empty_proof()
				};
				schema::v1::light::Response {
					response: Some(schema::v1::light::response::Response::RemoteHeaderResponse(r)),
				}
			}
			Request::Read{..} => {
				let r = schema::v1::light::RemoteReadResponse { proof: empty_proof() };
				schema::v1::light::Response {
					response: Some(schema::v1::light::response::Response::RemoteReadResponse(r)),
				}
			}
			Request::ReadChild{..} => {
				let r = schema::v1::light::RemoteReadResponse { proof: empty_proof() };
				schema::v1::light::Response {
					response: Some(schema::v1::light::response::Response::RemoteReadResponse(r)),
				}
			}
			Request::Call{..} => {
				let r = schema::v1::light::RemoteCallResponse { proof: empty_proof() };
				schema::v1::light::Response {
					response: Some(schema::v1::light::response::Response::RemoteCallResponse(r)),
				}
			}
			Request::Changes{..} => {
				let r = schema::v1::light::RemoteChangesResponse {
					max: iter::repeat(1).take(32).collect(),
					proof: Vec::new(),
					roots: Vec::new(),
					roots_proof: empty_proof()
				};
				schema::v1::light::Response {
					response: Some(schema::v1::light::response::Response::RemoteChangesResponse(r)),
				}
			}
		};

		behaviour.request(request).unwrap();

		assert_eq!(1, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len());
		assert_matches!(poll(&mut behaviour), Poll::Ready(NetworkBehaviourAction::NotifyHandler { .. }));
		assert_eq!(0, behaviour.pending_requests.len());
		assert_eq!(1, behaviour.outstanding.len());
		assert_eq!(1, *behaviour.outstanding.keys().next().unwrap());

		behaviour.inject_event(peer.clone(), conn, Event::Response(1, Response::Light(response)));

		poll(&mut behaviour);

		assert_eq!(0, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len())
	}

	#[test]
	fn receives_remote_call_response() {
		let mut chan = oneshot::channel();
		let request = light::RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: None,
		};
		issue_request(Request::Call { request, sender: chan.0 });
		assert_matches!(chan.1.try_recv(), Ok(Some(Ok(_))))
	}

	#[test]
	fn receives_remote_read_response() {
		let mut chan = oneshot::channel();
		let request = light::RemoteReadRequest {
			header: dummy_header(),
			block: Default::default(),
			keys: vec![b":key".to_vec()],
			retry_count: None,
		};
		issue_request(Request::Read { request, sender: chan.0 });
		assert_matches!(chan.1.try_recv(), Ok(Some(Ok(_))))
	}

	#[test]
	fn receives_remote_read_child_response() {
		let mut chan = oneshot::channel();
		let child_info = ChildInfo::new_default(&b":child_storage:default:sub"[..]);
		let request = light::RemoteReadChildRequest {
			header: dummy_header(),
			block: Default::default(),
			storage_key: child_info.prefixed_storage_key(),
			keys: vec![b":key".to_vec()],
			retry_count: None,
		};
		issue_request(Request::ReadChild { request, sender: chan.0 });
		assert_matches!(chan.1.try_recv(), Ok(Some(Ok(_))))
	}

	#[test]
	fn receives_remote_header_response() {
		let mut chan = oneshot::channel();
		let request = light::RemoteHeaderRequest {
			cht_root: Default::default(),
			block: 1,
			retry_count: None,
		};
		issue_request(Request::Header { request, sender: chan.0 });
		assert_matches!(chan.1.try_recv(), Ok(Some(Ok(_))))
	}

	#[test]
	fn receives_remote_changes_response() {
		let mut chan = oneshot::channel();
		let request = light::RemoteChangesRequest {
			changes_trie_configs: vec![sp_core::ChangesTrieConfigurationRange {
				zero: (0, Default::default()),
				end: None,
				config: Some(sp_core::ChangesTrieConfiguration::new(4, 2)),
			}],
			first_block: (1, Default::default()),
			last_block: (100, Default::default()),
			max_block: (100, Default::default()),
			tries_roots: (1, Default::default(), Vec::new()),
			key: Vec::new(),
			storage_key: None,
			retry_count: None,
		};
		issue_request(Request::Changes { request, sender: chan.0 });
		assert_matches!(chan.1.try_recv(), Ok(Some(Ok(_))))
	}

	fn send_receive(request: Request<Block>) {
		// We start a swarm on the listening side which awaits incoming requests and answers them:
		let local_pset = peerset();
		let local_listen_addr: libp2p::Multiaddr = libp2p::multiaddr::Protocol::Memory(rand::random()).into();
		let mut local_swarm = make_swarm(true, local_pset.1, make_config());
		Swarm::listen_on(&mut local_swarm, local_listen_addr.clone()).unwrap();

		// We also start a swarm that makes requests and awaits responses:
		let remote_pset = peerset();
		let mut remote_swarm = make_swarm(true, remote_pset.1, make_config());

		// We now schedule a request, dial the remote and let the two swarm work it out:
		remote_swarm.request(request).unwrap();
		Swarm::dial_addr(&mut remote_swarm, local_listen_addr).unwrap();

		let future = {
			let a = local_swarm.for_each(|_| future::ready(()));
			let b = remote_swarm.for_each(|_| future::ready(()));
			future::join(a, b).map(|_| ())
		};

		task::spawn(future);
	}

	#[test]
	fn send_receive_call() {
		let chan = oneshot::channel();
		let request = light::RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: None,
		};
		send_receive(Request::Call { request, sender: chan.0 });
		assert_eq!(vec![42], task::block_on(chan.1).unwrap().unwrap());
		//              ^--- from `DummyFetchChecker::check_execution_proof`
	}

	#[test]
	fn send_receive_read() {
		let chan = oneshot::channel();
		let request = light::RemoteReadRequest {
			header: dummy_header(),
			block: Default::default(),
			keys: vec![b":key".to_vec()],
			retry_count: None
		};
		send_receive(Request::Read { request, sender: chan.0 });
		assert_eq!(Some(vec![42]), task::block_on(chan.1).unwrap().unwrap().remove(&b":key"[..]).unwrap());
		//                   ^--- from `DummyFetchChecker::check_read_proof`
	}

	#[test]
	fn send_receive_read_child() {
		let chan = oneshot::channel();
		let child_info = ChildInfo::new_default(&b":child_storage:default:sub"[..]);
		let request = light::RemoteReadChildRequest {
			header: dummy_header(),
			block: Default::default(),
			storage_key: child_info.prefixed_storage_key(),
			keys: vec![b":key".to_vec()],
			retry_count: None,
		};
		send_receive(Request::ReadChild { request, sender: chan.0 });
		assert_eq!(Some(vec![42]), task::block_on(chan.1).unwrap().unwrap().remove(&b":key"[..]).unwrap());
		//                   ^--- from `DummyFetchChecker::check_read_child_proof`
	}

	#[test]
	fn send_receive_header() {
		sp_tracing::try_init_simple();
		let chan = oneshot::channel();
		let request = light::RemoteHeaderRequest {
			cht_root: Default::default(),
			block: 1,
			retry_count: None,
		};
		send_receive(Request::Header { request, sender: chan.0 });
		// The remote does not know block 1:
		assert_matches!(task::block_on(chan.1).unwrap(), Err(ClientError::RemoteFetchFailed));
	}

	#[test]
	fn send_receive_changes() {
		let chan = oneshot::channel();
		let request = light::RemoteChangesRequest {
			changes_trie_configs: vec![sp_core::ChangesTrieConfigurationRange {
				zero: (0, Default::default()),
				end: None,
				config: Some(sp_core::ChangesTrieConfiguration::new(4, 2)),
			}],
			first_block: (1, Default::default()),
			last_block: (100, Default::default()),
			max_block: (100, Default::default()),
			tries_roots: (1, Default::default(), Vec::new()),
			key: Vec::new(),
			storage_key: None,
			retry_count: None,
		};
		send_receive(Request::Changes { request, sender: chan.0 });
		assert_eq!(vec![(100, 2)], task::block_on(chan.1).unwrap().unwrap());
		//              ^--- from `DummyFetchChecker::check_changes_proof`
	}

	#[test]
	fn body_request_fields_encoded_properly() {
		let (sender, _) = oneshot::channel();
		let serialized_request = serialize_request::<Block>(&Request::Body {
			request: RemoteBodyRequest {
				header: dummy_header(),
				retry_count: None,
			},
			sender,
		}).unwrap();
		let deserialized_request = schema::v1::BlockRequest::decode(&serialized_request[..]).unwrap();
		assert!(
			BlockAttributes::from_be_u32(deserialized_request.fields)
				.unwrap()
				.contains(BlockAttributes::BODY)
		);
	}
}
