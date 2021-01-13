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

// TODO: How about renaming this to sender instead of client?

//! Helper for outgoing light client requests.
//!
//! Call [`LightClientRequestSender::send_request`] to send out light client requests. Under the
//! hood the following will hapen:
//!
//! 1. Build the request.
//!
//! 2. Forward the request to [`crate::request_responses::RequestResponsesBehaviour`] via
//! [`OutEvent::SendRequest`].
//!
//! 3. Wait for the response and forward the response via the [`oneshot::Sender`] provided earlier
//! with [`LightClientRequestSender::send_request`].

use codec::{self, Encode, Decode};
use crate::{
	config::ProtocolId,
	protocol::message::{BlockAttributes},
	schema,
	PeerId,
};
use crate::request_responses::{RequestFailure};
use futures::{channel::{oneshot}, future::BoxFuture, prelude::*, stream::FuturesUnordered};
use prost::Message;
use sc_client_api::{
	light::{
		self, RemoteBodyRequest,
	}
};
use sc_peerset::ReputationChange;
use sp_blockchain::{Error as ClientError};
use sp_runtime::{
	traits::{Block, Header, NumberFor},
};
use std::{
	collections::{BTreeMap, VecDeque, HashMap},
	pin::Pin,
	sync::Arc,
	task::{Context, Poll},
	time::Duration,
};
use wasm_timer::Instant;

/// Reputation change for a peer when a request timed out.
pub(crate) const TIMEOUT_REPUTATION_CHANGE: i32 = -(1 << 8);

/// Configuration options for [`LightClientRequestSender`].
#[derive(Debug, Clone)]
struct Config {
	max_pending_requests: usize,
	light_protocol: String,
	block_protocol: String,
}
impl Config {
	/// Create a new [`LightClientRequestSender`] configuration.
	pub fn new(id: &ProtocolId) -> Self {
		Config {
			max_pending_requests: 128,
			light_protocol: super::generate_protocol_name(id),
			block_protocol: crate::block_request_handler::generate_protocol_name(id),
		}
	}
}

/// The light client handler behaviour.
pub struct LightClientRequestSender<B: Block> {
	/// This behaviour's configuration.
	config: Config,
	/// Verifies that received responses are correct.
	checker: Arc<dyn light::FetchChecker<B>>,
	/// Peer information (addresses, their best block, etc.)
	peers: HashMap<PeerId, PeerInfo<B>>,
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

impl<B: Block> Unpin for LightClientRequestSender<B> {}

impl<B> LightClientRequestSender<B>
where
	B: Block,
{
	/// Construct a new light client handler.
	pub fn new(
		id: &ProtocolId,
		checker: Arc<dyn light::FetchChecker<B>>,
		peerset: sc_peerset::PeersetHandle,
	) -> Self {
		LightClientRequestSender {
			config: Config::new(id),
			checker,
			peers: Default::default(),
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
	/// [`<LightClientRequestSender as Stream>::poll_next`].
	fn remove_peer(&mut self, peer: PeerId) {
		self.peers.remove(&peer);
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


impl<B: Block> Stream for LightClientRequestSender<B> {
	type Item = OutEvent;

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
		// If we have a pending request to send, try to find an available peer and send it.
		let now = Instant::now();
		while let Some(mut request) = self.pending_requests.pop_front() {
			// TODO: Consider moving 40s to a constant combined with `ProtocolConfig::request_timeout` in `handler.rs`.
			if now > request.timestamp + Duration::from_secs(40) {
				if request.retries == 0 {
					send_reply(Err(ClientError::RemoteFetchFailed), request.request);
					continue
				}
				request.timestamp = Instant::now();
				request.retries -= 1
			}

			let number = required_block(&request.request);
			let peer = match self.peers.iter().find_map(|(peer_id, peer_info)| {
				if peer_info.status == PeerStatus::Idle {
					if peer_info.best_block.map(|n| n >= number).unwrap_or(false) {
						return Some(*peer_id)
					}
				}
				None
			}) {
				Some(peer) => peer,
				None => {
					self.pending_requests.push_front(request);
					log::debug!("no peer available to send request to");

					// TODO: Double check, this was previously `break`, but there might be another
					// request with a lower block number that one of our peers might serve.
					continue
				}
			};

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

			return Poll::Ready(Some(OutEvent::SendRequest {
				target: peer,
				request: request_bytes,
				pending_response: tx,
				protocol_name: protocol,
			}));
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
						},
						ExpectedResponseTy::Block => {
							schema::v1::BlockResponse::decode(&response[..])
								.map(|r| Response::Block(r))
						}
					}
				}
				Err(e) => {
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

/// Events returned by [`LightClientRequestSender`].
pub enum OutEvent {
	/// Emit a request to be send out on the network e.g. via [`crate::request_responses`].
	SendRequest {
		target: PeerId,
		request: Vec<u8>,
		pending_response: oneshot::Sender<Result<Vec<u8>, RequestFailure>>,
		protocol_name: String,
	}
}

/// Type of response expected from the remote for this request.
#[derive(Debug, Clone)]
enum ExpectedResponseTy {
	Light,
	Block,
}

/// Incoming response from remote.
#[derive(Debug, Clone)]
pub enum Response {
	/// Incoming light response from remote.
	Light(schema::v1::light::Response),
	/// Incoming block response from remote.
	Block(schema::v1::BlockResponse),
}

// TODO: Consider renaming, given that this is not sending the request out on the wire, but instead
// sending the request up to the one that requested it.
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

// TODO: Why not make this a method?
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
