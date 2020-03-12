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
	protocol::{api, light_dispatch::TIMEOUT_REPUTATION_CHANGE}
};
use futures::{channel::oneshot, future::BoxFuture, prelude::*, stream::FuturesUnordered};
use libp2p::{
	core::{
		ConnectedPoint,
		Multiaddr,
		PeerId,
		upgrade::{InboundUpgrade, ReadOneError, UpgradeInfo, Negotiated},
		upgrade::{OutboundUpgrade, read_one, write_one}
	},
	swarm::{
		NegotiatedSubstream,
		NetworkBehaviour,
		NetworkBehaviourAction,
		OneShotHandler,
		PollParameters,
		SubstreamProtocol
	}
};
use nohash_hasher::IntMap;
use prost::Message;
use rustc_hex::ToHex;
use sc_client::light::fetcher;
use sc_client_api::StorageProof;
use sc_peerset::ReputationChange;
use sp_core::storage::{ChildInfo, StorageKey};
use sp_blockchain::{Error as ClientError};
use sp_runtime::{
	traits::{Block, Header, NumberFor, Zero},
	generic::BlockId,
};
use std::{
	collections::{BTreeMap, VecDeque, HashMap},
	iter,
	io,
	sync::Arc,
	time::Duration,
	task::{Context, Poll}
};
use void::Void;
use wasm_timer::Instant;

/// Configuration options for `LightClientHandler` behaviour.
#[derive(Debug, Clone)]
pub struct Config {
	max_data_size: usize,
	max_pending_requests: usize,
	inactivity_timeout: Duration,
	request_timeout: Duration,
	protocol: Bytes,
}

impl Config {
	/// Create a fresh configuration with the following options:
	///
	/// - max. data size = 1 MiB
	/// - max. pending requests = 128
	/// - inactivity timeout = 15s
	/// - request timeout = 15s
	pub fn new(id: &ProtocolId) -> Self {
		let mut c = Config {
			max_data_size: 1024 * 1024,
			max_pending_requests: 128,
			inactivity_timeout: Duration::from_secs(15),
			request_timeout: Duration::from_secs(15),
			protocol: Bytes::new(),
		};
		c.set_protocol(id);
		c
	}

	/// Limit the max. length of incoming request bytes.
	pub fn set_max_data_size(&mut self, v: usize) -> &mut Self {
		self.max_data_size = v;
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

	/// Set protocol to use for upgrade negotiation.
	pub fn set_protocol(&mut self, id: &ProtocolId) -> &mut Self {
		let mut v = Vec::new();
		v.extend_from_slice(b"/");
		v.extend_from_slice(id.as_bytes());
		v.extend_from_slice(b"/light/2");
		self.protocol = v.into();
		self
	}
}

/// Possible errors while handling light clients.
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// There are currently too many pending request.
	#[error("too many pending requests")]
	TooManyRequests,
	/// The response type does not correspond to the issued request.
	#[error("unexpected response")]
	UnexpectedResponse,
	/// A bad request has been received.
	#[error("bad request: {0}")]
	BadRequest(&'static str),
	/// The chain client errored.
	#[error("client error: {0}")]
	Client(#[from] ClientError),
	/// Encoding or decoding of some data failed.
	#[error("codec error: {0}")]
	Codec(#[from] codec::Error),
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
	Header {
		request: fetcher::RemoteHeaderRequest<B::Header>,
		sender: oneshot::Sender<Result<B::Header, ClientError>>
	},
	Read {
		request: fetcher::RemoteReadRequest<B::Header>,
		sender: oneshot::Sender<Result<HashMap<Vec<u8>, Option<Vec<u8>>>, ClientError>>
	},
	ReadChild {
		request: fetcher::RemoteReadChildRequest<B::Header>,
		sender: oneshot::Sender<Result<HashMap<Vec<u8>, Option<Vec<u8>>>, ClientError>>
	},
	Call {
		request: fetcher::RemoteCallRequest<B::Header>,
		sender: oneshot::Sender<Result<Vec<u8>, ClientError>>
	},
	Changes {
		request: fetcher::RemoteChangesRequest<B::Header>,
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
	Header(B::Header)
}

/// Augments a light client request with metadata.
#[derive(Debug)]
struct RequestWrapper<B: Block, P> {
	/// Time when this value was created.
	timestamp: Instant,
	/// Remaining retries.
	retries: usize,
	/// The actual request.
	request: Request<B>,
	/// Peer information, e.g. `PeerId`.
	peer: P
}

/// Information we have about some peer.
#[derive(Debug)]
struct PeerInfo<B: Block> {
	address: Multiaddr,
	best_block: Option<NumberFor<B>>,
	status: PeerStatus,
}

/// A peer is either idle or busy processing a request from us.
#[derive(Debug, Clone, PartialEq, Eq)]
enum PeerStatus {
	/// The peer is available.
	Idle,
	/// We wait for the peer to return us a response for the given request ID.
	BusyWith(u64),
}

/// The light client handler behaviour.
pub struct LightClientHandler<B: Block> {
	/// This behaviour's configuration.
	config: Config,
	/// Blockchain client.
	chain: Arc<dyn Client<B>>,
	/// Verifies that received responses are correct.
	checker: Arc<dyn fetcher::FetchChecker<B>>,
	/// Peer information (addresses, their best block, etc.)
	peers: HashMap<PeerId, PeerInfo<B>>,
	/// Futures sending back response to remote clients.
	responses: FuturesUnordered<BoxFuture<'static, ()>>,
	/// Pending (local) requests.
	pending_requests: VecDeque<RequestWrapper<B, ()>>,
	/// Requests on their way to remote peers.
	outstanding: IntMap<u64, RequestWrapper<B, PeerId>>,
	/// (Local) Request ID counter
	next_request_id: u64,
	/// Handle to use for reporting misbehaviour of peers.
	peerset: sc_peerset::PeersetHandle,
}

impl<B> LightClientHandler<B>
where
	B: Block,
{
	/// Construct a new light client handler.
	pub fn new(
		cfg: Config,
		chain: Arc<dyn Client<B>>,
		checker: Arc<dyn fetcher::FetchChecker<B>>,
		peerset: sc_peerset::PeersetHandle,
	) -> Self {
		LightClientHandler {
			config: cfg,
			chain,
			checker,
			peers: HashMap::new(),
			responses: FuturesUnordered::new(),
			pending_requests: VecDeque::new(),
			outstanding: IntMap::default(),
			next_request_id: 1,
			peerset,
		}
	}

	/// We rely on external information about peers best blocks as we lack the
	/// means to determine it ourselves.
	pub fn update_best_block(&mut self, peer: &PeerId, num: NumberFor<B>) {
		if let Some(info) = self.peers.get_mut(peer) {
			info.best_block = Some(num)
		}
	}

	/// Issue a new light client request.
	pub fn request(&mut self, req: Request<B>) -> Result<(), Error> {
		if self.pending_requests.len() >= self.config.max_pending_requests {
			return Err(Error::TooManyRequests)
		}
		let rw = RequestWrapper {
			timestamp: Instant::now(),
			retries: retries(&req),
			request: req,
			peer: (), // we do not know the peer yet
		};
		self.pending_requests.push_back(rw);
		Ok(())
	}

	fn next_request_id(&mut self) -> u64 {
		let id = self.next_request_id;
		self.next_request_id += 1;
		id
	}

	// Iterate over peers known to possess a certain block.
	fn idle_peers_with_block(&mut self, num: NumberFor<B>) -> impl Iterator<Item = PeerId> + '_ {
		self.peers.iter()
			.filter(move |(_, info)| {
				info.status == PeerStatus::Idle && info.best_block >= Some(num)
			})
			.map(|(peer, _)| peer.clone())
	}

	// Iterate over peers without a known block.
	fn idle_peers_with_unknown_block(&mut self) -> impl Iterator<Item = PeerId> + '_ {
		self.peers.iter()
			.filter(|(_, info)| {
				info.status == PeerStatus::Idle && info.best_block.is_none()
			})
			.map(|(peer, _)| peer.clone())
	}

	/// Remove the given peer.
	///
	/// If we have a request to this peer in flight, we move it back to
	/// the pending requests queue.
	fn remove_peer(&mut self, peer: &PeerId) {
		if let Some(id) = self.outstanding.iter().find(|(_, rw)| &rw.peer == peer).map(|(k, _)| *k) {
			let rw = self.outstanding.remove(&id).expect("key belongs to entry in this map");
			let rw = RequestWrapper {
				timestamp: rw.timestamp,
				retries: rw.retries,
				request: rw.request,
				peer: (), // need to find another peer
			};
			self.pending_requests.push_back(rw);
		}
		self.peers.remove(peer);
	}

	/// Process a local request's response from remote.
	///
	/// If successful, this will give us the actual, checked data we should be
	/// sending back to the client, otherwise an error.
	fn on_response
		( &mut self
		, peer: &PeerId
		, request: &Request<B>
		, response: api::v1::light::Response
		) -> Result<Reply<B>, Error>
	{
		log::trace!("response from {}", peer);
		use api::v1::light::response::Response;
		match response.response {
			Some(Response::RemoteCallResponse(response)) =>
				if let Request::Call { request , .. } = request {
					let proof = Decode::decode(&mut response.proof.as_ref())?;
					let reply = self.checker.check_execution_proof(request, proof)?;
					Ok(Reply::VecU8(reply))
				} else {
					Err(Error::UnexpectedResponse)
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
					_ => Err(Error::UnexpectedResponse)
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
					let reply = self.checker.check_changes_proof(&request, fetcher::ChangesProof {
						max_block,
						proof: response.proof,
						roots,
						roots_proof,
					})?;
					Ok(Reply::VecNumberU32(reply))
				} else {
					Err(Error::UnexpectedResponse)
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
					Err(Error::UnexpectedResponse)
				}
			None => Err(Error::UnexpectedResponse)
		}
	}

	fn on_remote_call_request
		( &mut self
		, peer: &PeerId
		, request: &api::v1::light::RemoteCallRequest
		) -> Result<api::v1::light::Response, Error>
	{
		log::trace!("remote call request from {} ({} at {:?})",
			peer,
			request.method,
			request.block,
		);

		let block = Decode::decode(&mut request.block.as_ref())?;

		let proof = match self.chain.execution_proof(&BlockId::Hash(block), &request.method, &request.data) {
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
			let r = api::v1::light::RemoteCallResponse { proof: proof.encode() };
			api::v1::light::response::Response::RemoteCallResponse(r)
		};

		Ok(api::v1::light::Response { response: Some(response) })
	}

	fn on_remote_read_request
		( &mut self
		, peer: &PeerId
		, request: &api::v1::light::RemoteReadRequest
		) -> Result<api::v1::light::Response, Error>
	{
		if request.keys.is_empty() {
			log::debug!("invalid remote read request sent by {}", peer);
			return Err(Error::BadRequest("remote read request without keys"))
		}

		log::trace!("remote read request from {} ({} at {:?})",
			peer,
			fmt_keys(request.keys.first(), request.keys.last()),
			request.block);

		let block = Decode::decode(&mut request.block.as_ref())?;

		let proof = match self.chain.read_proof(&BlockId::Hash(block), &mut request.keys.iter().map(AsRef::as_ref)) {
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
			let r = api::v1::light::RemoteReadResponse { proof: proof.encode() };
			api::v1::light::response::Response::RemoteReadResponse(r)
		};

		Ok(api::v1::light::Response { response: Some(response) })
	}

	fn on_remote_read_child_request
		( &mut self
		, peer: &PeerId
		, request: &api::v1::light::RemoteReadChildRequest
		) -> Result<api::v1::light::Response, Error>
	{
		if request.keys.is_empty() {
			log::debug!("invalid remote child read request sent by {}", peer);
			return Err(Error::BadRequest("remove read child request without keys"))
		}

		log::trace!("remote read child request from {} ({} {} at {:?})",
			peer,
			request.storage_key.to_hex::<String>(),
			fmt_keys(request.keys.first(), request.keys.last()),
			request.block);

		let block = Decode::decode(&mut request.block.as_ref())?;

		let proof =
			if let Some(info) = ChildInfo::resolve_child_info(request.child_type, &request.child_info[..]) {
				match self.chain.read_child_proof(
					&BlockId::Hash(block),
					&request.storage_key,
					info,
					&mut request.keys.iter().map(AsRef::as_ref)
				) {
					Ok(proof) => proof,
					Err(error) => {
						log::trace!("remote read child request from {} ({} {} at {:?}) failed with: {}",
							peer,
							request.storage_key.to_hex::<String>(),
							fmt_keys(request.keys.first(), request.keys.last()),
							request.block,
							error);
						StorageProof::empty()
					}
				}
			} else {
				log::trace!("remote read child request from {} ({} {} at {:?}) failed with: {}",
					peer,
					request.storage_key.to_hex::<String>(),
					fmt_keys(request.keys.first(), request.keys.last()),
					request.block,
					"invalid child info and type"
				);
				StorageProof::empty()
			};

		let response = {
			let r = api::v1::light::RemoteReadResponse { proof: proof.encode() };
			api::v1::light::response::Response::RemoteReadResponse(r)
		};

		Ok(api::v1::light::Response { response: Some(response) })
	}

	fn on_remote_header_request
		( &mut self
		, peer: &PeerId
		, request: &api::v1::light::RemoteHeaderRequest
		) -> Result<api::v1::light::Response, Error>
	{
		log::trace!("remote header proof request from {} ({:?})", peer, request.block);

		let block = Decode::decode(&mut request.block.as_ref())?;
		let (header, proof) = match self.chain.header_proof(&BlockId::Number(block)) {
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
			let r = api::v1::light::RemoteHeaderResponse { header, proof: proof.encode() };
			api::v1::light::response::Response::RemoteHeaderResponse(r)
		};

		Ok(api::v1::light::Response { response: Some(response) })
	}

	fn on_remote_changes_request
		( &mut self
		, peer: &PeerId
		, request: &api::v1::light::RemoteChangesRequest
		) -> Result<api::v1::light::Response, Error>
	{
		log::trace!("remote changes proof request from {} for key {} ({:?}..{:?})",
			peer,
			if !request.storage_key.is_empty() {
				format!("{} : {}", request.storage_key.to_hex::<String>(), request.key.to_hex::<String>())
			} else {
				request.key.to_hex::<String>()
			},
			request.first,
			request.last);

		let first = Decode::decode(&mut request.first.as_ref())?;
		let last = Decode::decode(&mut request.last.as_ref())?;
		let min = Decode::decode(&mut request.min.as_ref())?;
		let max = Decode::decode(&mut request.max.as_ref())?;
		let key = StorageKey(request.key.clone());
		let storage_key =
			if request.storage_key.is_empty() {
				None
			} else {
				Some(StorageKey(request.storage_key.clone()))
			};

		let proof = match self.chain.key_changes_proof(first, last, min, max, storage_key.as_ref(), &key) {
			Ok(proof) => proof,
			Err(error) => {
				log::trace!("remote changes proof request from {} for key {} ({:?}..{:?}) failed with: {}",
					peer,
					if let Some(sk) = storage_key {
						format!("{} : {}", sk.0.to_hex::<String>(), key.0.to_hex::<String>())
					} else {
						key.0.to_hex::<String>()
					},
					request.first,
					request.last,
					error);

				fetcher::ChangesProof::<B::Header> {
					max_block: Zero::zero(),
					proof: Vec::new(),
					roots: BTreeMap::new(),
					roots_proof: StorageProof::empty(),
				}
			}
		};

		let response = {
			let r = api::v1::light::RemoteChangesResponse {
				max: proof.max_block.encode(),
				proof: proof.proof,
				roots: proof.roots.into_iter()
					.map(|(k, v)| api::v1::light::Pair { fst: k.encode(), snd: v.encode() })
					.collect(),
				roots_proof: proof.roots_proof.encode(),
			};
			api::v1::light::response::Response::RemoteChangesResponse(r)
		};

		Ok(api::v1::light::Response { response: Some(response) })
	}
}

impl<B> NetworkBehaviour for LightClientHandler<B>
where
	B: Block
{
	type ProtocolsHandler = OneShotHandler<InboundProtocol, OutboundProtocol, Event<NegotiatedSubstream>>;
	type OutEvent = Void;

	fn new_handler(&mut self) -> Self::ProtocolsHandler {
		let p = InboundProtocol {
			max_data_size: self.config.max_data_size,
			protocol: self.config.protocol.clone(),
		};
		OneShotHandler::new(SubstreamProtocol::new(p), self.config.inactivity_timeout)
	}

	fn addresses_of_peer(&mut self, peer: &PeerId) -> Vec<Multiaddr> {
		self.peers.get(peer)
			.map(|info| vec![info.address.clone()])
			.unwrap_or_default()
	}

	fn inject_connected(&mut self, peer: PeerId, info: ConnectedPoint) {
		let peer_address = match info {
			ConnectedPoint::Listener { send_back_addr, .. } => send_back_addr,
			ConnectedPoint::Dialer { address } => address
		};

		log::trace!("peer {} connected with address {}", peer, peer_address);

		let info = PeerInfo {
			address: peer_address,
			best_block: None,
			status: PeerStatus::Idle,
		};

		self.peers.insert(peer, info);
	}

	fn inject_disconnected(&mut self, peer: &PeerId, _: ConnectedPoint) {
		log::trace!("peer {} disconnected", peer);
		self.remove_peer(peer)
	}

	fn inject_node_event(&mut self, peer: PeerId, event: Event<NegotiatedSubstream>) {
		match event {
			// An incoming request from remote has been received.
			Event::Request(request, mut stream) => {
				log::trace!("incoming request from {}", peer);
				let result = match &request.request {
					Some(api::v1::light::request::Request::RemoteCallRequest(r)) =>
						self.on_remote_call_request(&peer, r),
					Some(api::v1::light::request::Request::RemoteReadRequest(r)) =>
						self.on_remote_read_request(&peer, r),
					Some(api::v1::light::request::Request::RemoteHeaderRequest(r)) =>
						self.on_remote_header_request(&peer, r),
					Some(api::v1::light::request::Request::RemoteReadChildRequest(r)) =>
						self.on_remote_read_child_request(&peer, r),
					Some(api::v1::light::request::Request::RemoteChangesRequest(r)) =>
						self.on_remote_changes_request(&peer, r),
					None => {
						log::debug!("ignoring request without request data from peer {}", peer);
						return
					}
				};
				match result {
					Ok(response) => {
						log::trace!("enqueueing response for peer {}", peer);
						let mut data = Vec::new();
						if let Err(e) = response.encode(&mut data) {
							log::debug!("error encoding response for peer {}: {}", peer, e)
						} else {
							let future = async move {
								if let Err(e) = write_one(&mut stream, data).await {
									log::debug!("error writing response: {}", e)
								}
							};
							self.responses.push(future.boxed())
						}
					}
					Err(Error::BadRequest(_)) => {
						self.remove_peer(&peer);
						self.peerset.report_peer(peer, ReputationChange::new(-(1 << 12), "bad request"))
					}
					Err(e) => log::debug!("error handling request from peer {}: {}", peer, e)
				}
			}
			// A response to one of our own requests has been received.
			Event::Response(id, response) => {
				if let Some(request) = self.outstanding.remove(&id) {
					// We first just check if the response originates from the expected peer.
					if request.peer != peer {
						log::debug!("was expecting response from {} instead of {}", request.peer, peer);
						self.outstanding.insert(id, request);
						self.remove_peer(&peer);
						self.peerset.report_peer(peer, ReputationChange::new_fatal("response from unexpected peer"));
						return
					}

					if let Some(info) = self.peers.get_mut(&peer) {
						if info.status != PeerStatus::BusyWith(id) {
							// If we get here, something is wrong with our internal handling of peer
							// status information. At any time, a single peer processes at most one
							// request from us and its status should contain the request ID we are
							// expecting a response for. If a peer would send us a response with a
							// random ID, we should not have an entry for it with this peer ID in
							// our `outstanding` map, so a malicious peer should not be able to get
							// us here. It is our own fault and must be fixed!
							panic!("unexpected peer status {:?} for {}", info.status, peer);
						}

						info.status = PeerStatus::Idle; // Make peer available again.

						match self.on_response(&peer, &request.request, response) {
							Ok(reply) => send_reply(Ok(reply), request.request),
							Err(Error::UnexpectedResponse) => {
								log::debug!("unexpected response {} from peer {}", id, peer);
								self.remove_peer(&peer);
								self.peerset.report_peer(peer, ReputationChange::new_fatal("unexpected response from peer"));
								let rw = RequestWrapper {
									timestamp: request.timestamp,
									retries: request.retries,
									request: request.request,
									peer: (),
								};
								self.pending_requests.push_back(rw);
							}
							Err(other) => {
								log::debug!("error handling response {} from peer {}: {}", id, peer, other);
								self.remove_peer(&peer);
								self.peerset.report_peer(peer, ReputationChange::new_fatal("invalid response from peer"));
								if request.retries > 0 {
									let rw = RequestWrapper {
										timestamp: request.timestamp,
										retries: request.retries - 1,
										request: request.request,
										peer: (),
									};
									self.pending_requests.push_back(rw)
								} else {
									send_reply(Err(ClientError::RemoteFetchFailed), request.request)
								}
							}
						}
					} else {
						// If we get here, something is wrong with our internal handling of peers.
						// We apparently have an entry in our `outstanding` map and the peer is the one we
						// expected. So, if we can not find an entry for it in our peer information table,
						// then these two collections are out of sync which must not happen and is a clear
						// programmer error that must be fixed!
						panic!("missing peer information for {}; response {}", peer, id);
					}
				} else {
					log::debug!("unexpected response {} from peer {}", id, peer);
					self.remove_peer(&peer);
					self.peerset.report_peer(peer, ReputationChange::new_fatal("response from unexpected peer"));
				}
			}
		}
	}

	fn poll(&mut self, cx: &mut Context, _: &mut impl PollParameters) -> Poll<NetworkBehaviourAction<OutboundProtocol, Void>> {
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
			let number = required_block(&request.request);
			let available_peer = {
				let p = self.idle_peers_with_block(number).next();
				if p.is_none() {
					self.idle_peers_with_unknown_block().next()
				} else {
					p
				}
			};
			if let Some(peer) = available_peer {
				let rq = serialize_request(&request.request);
				let mut buf = Vec::with_capacity(rq.encoded_len());
				if let Err(e) = rq.encode(&mut buf) {
					log::debug!("failed to serialize request: {}", e);
					send_reply(Err(ClientError::RemoteFetchFailed), request.request)
				} else {
					let id = self.next_request_id();
					log::trace!("sending request {} to peer {}", id, peer);
					let protocol = OutboundProtocol {
						request: buf,
						request_id: id,
						max_data_size: self.config.max_data_size,
						protocol: self.config.protocol.clone(),
					};
					self.peers.get_mut(&peer).map(|info| info.status = PeerStatus::BusyWith(id));
					let rw = RequestWrapper {
						timestamp: request.timestamp,
						retries: request.retries,
						request: request.request,
						peer: peer.clone(),
					};
					self.outstanding.insert(id, rw);
					return Poll::Ready(NetworkBehaviourAction::SendEvent { peer_id: peer, event: protocol })
				}
			} else {
				self.pending_requests.push_front(request);
				log::debug!("no peer available to send request to");
				break
			}
		}

		// Look for ongoing requests that have timed out.
		let mut expired = Vec::new();
		for (id, rw) in &self.outstanding {
			if now > rw.timestamp + self.config.request_timeout {
				log::debug!("request {} timed out", id);
				expired.push(*id)
			}
		}
		for id in expired {
			if let Some(rw) = self.outstanding.remove(&id) {
				self.remove_peer(&rw.peer);
				self.peerset.report_peer(rw.peer.clone(),
					ReputationChange::new(TIMEOUT_REPUTATION_CHANGE, "light request timeout"));
				if rw.retries == 0 {
					send_reply(Err(ClientError::RemoteFetchFailed), rw.request);
					continue
				}
				let rw = RequestWrapper {
					timestamp: Instant::now(),
					retries: rw.retries - 1,
					request: rw.request,
					peer: (),
				};
				self.pending_requests.push_back(rw)
			}
		}

		Poll::Pending
	}
}

fn required_block<B: Block>(request: &Request<B>) -> NumberFor<B> {
	match request {
		Request::Header { request, .. } => request.block,
		Request::Read { request, .. } => *request.header.number(),
		Request::ReadChild { request, .. } => *request.header.number(),
		Request::Call { request, .. } => *request.header.number(),
		Request::Changes { request, .. } => request.max_block.0,
	}
}

fn retries<B: Block>(request: &Request<B>) -> usize {
	let rc = match request {
		Request::Header { request, .. } => request.retry_count,
		Request::Read { request, .. } => request.retry_count,
		Request::ReadChild { request, .. } => request.retry_count,
		Request::Call { request, .. } => request.retry_count,
		Request::Changes { request, .. } => request.retry_count,
	};
	rc.unwrap_or(0)
}

fn serialize_request<B: Block>(request: &Request<B>) -> api::v1::light::Request {
	let request = match request {
		Request::Header { request, .. } => {
			let r = api::v1::light::RemoteHeaderRequest { block: request.block.encode() };
			api::v1::light::request::Request::RemoteHeaderRequest(r)
		}
		Request::Read { request, .. } => {
			let r = api::v1::light::RemoteReadRequest {
				block: request.block.encode(),
				keys: request.keys.clone(),
			};
			api::v1::light::request::Request::RemoteReadRequest(r)
		}
		Request::ReadChild { request, .. } => {
			let r = api::v1::light::RemoteReadChildRequest {
				block: request.block.encode(),
				storage_key: request.storage_key.clone(),
				child_type: request.child_type.clone(),
				child_info: request.child_info.clone(),
				keys: request.keys.clone(),
			};
			api::v1::light::request::Request::RemoteReadChildRequest(r)
		}
		Request::Call { request, .. } => {
			let r = api::v1::light::RemoteCallRequest {
				block: request.block.encode(),
				method: request.method.clone(),
				data: request.call_data.clone(),
			};
			api::v1::light::request::Request::RemoteCallRequest(r)
		}
		Request::Changes { request, .. } => {
			let r = api::v1::light::RemoteChangesRequest {
				first: request.first_block.1.encode(),
				last: request.last_block.1.encode(),
				min: request.tries_roots.1.encode(),
				max: request.max_block.1.encode(),
				storage_key: request.storage_key.clone().unwrap_or_default(),
				key: request.key.clone(),
			};
			api::v1::light::request::Request::RemoteChangesRequest(r)
		}
	};

	api::v1::light::Request { request: Some(request) }
}

fn send_reply<B: Block>(result: Result<Reply<B>, ClientError>, request: Request<B>) {
	fn send<T>(item: T, sender: oneshot::Sender<T>) {
		let _ = sender.send(item); // It is okay if the other end already hung up.
	}
	match request {
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
	Request(api::v1::light::Request, T),
	/// Incoming response from remote.
	Response(u64, api::v1::light::Response),
}

/// Substream upgrade protocol.
///
/// Reads incoming requests from remote.
#[derive(Debug, Clone)]
pub struct InboundProtocol {
	/// The max. request length in bytes.
	max_data_size: usize,
	/// The protocol to use for upgrade negotiation.
	protocol: Bytes,
}

impl UpgradeInfo for InboundProtocol {
    type Info = Bytes;
    type InfoIter = iter::Once<Self::Info>;

    fn protocol_info(&self) -> Self::InfoIter {
        iter::once(self.protocol.clone())
    }
}

impl<T> InboundUpgrade<T> for InboundProtocol
where
	T: AsyncRead + AsyncWrite + Unpin + Send + 'static
{
    type Output = Event<T>;
    type Error = ReadOneError;
    type Future = BoxFuture<'static, Result<Self::Output, Self::Error>>;

    fn upgrade_inbound(self, mut s: T, _: Self::Info) -> Self::Future {
		let future = async move {
			let vec = read_one(&mut s, self.max_data_size).await?;
			match api::v1::light::Request::decode(&vec[..]) {
				Ok(r) => Ok(Event::Request(r, s)),
				Err(e) => Err(ReadOneError::Io(io::Error::new(io::ErrorKind::Other, e)))
			}
		};
		future.boxed()
	}
}

/// Substream upgrade protocol.
///
/// Sends a request to remote and awaits the response.
#[derive(Debug, Clone)]
pub struct OutboundProtocol {
	/// The serialized protobuf request.
	request: Vec<u8>,
	/// Local identifier for the request. Used to associate it with a response.
	request_id: u64,
	/// The max. request length in bytes.
	max_data_size: usize,
	/// The protocol to use for upgrade negotiation.
	protocol: Bytes,
}

impl UpgradeInfo for OutboundProtocol {
    type Info = Bytes;
    type InfoIter = iter::Once<Self::Info>;

    fn protocol_info(&self) -> Self::InfoIter {
        iter::once(self.protocol.clone())
    }
}

impl<T> OutboundUpgrade<T> for OutboundProtocol
where
	T: AsyncRead + AsyncWrite + Unpin + Send + 'static
{
    type Output = Event<T>;
    type Error = ReadOneError;
    type Future = BoxFuture<'static, Result<Self::Output, Self::Error>>;

    fn upgrade_outbound(self, mut s: T, _: Self::Info) -> Self::Future {
		let future = async move {
			write_one(&mut s, &self.request).await?;
			let vec = read_one(&mut s, self.max_data_size).await?;
			api::v1::light::Response::decode(&vec[..])
				.map(|r| Event::Response(self.request_id, r))
				.map_err(|e| {
					ReadOneError::Io(io::Error::new(io::ErrorKind::Other, e))
				})
		};
		future.boxed()
	}
}

fn fmt_keys(first: Option<&Vec<u8>>, last: Option<&Vec<u8>>) -> String {
	if let (Some(first), Some(last)) = (first, last) {
		if first == last {
			first.to_hex::<String>()
		} else {
			format!("{}..{}", first.to_hex::<String>(), last.to_hex::<String>())
		}
	} else {
		String::from("n/a")
	}
}

#[cfg(test)]
mod tests {
	use async_std::task;
	use assert_matches::assert_matches;
	use codec::Encode;
	use crate::{
		chain::Client,
		config::ProtocolId,
		protocol::{api, light_dispatch::tests::{DummyFetchChecker, dummy_header}}
	};
	use futures::{channel::oneshot, prelude::*};
	use libp2p::{
		PeerId,
		Multiaddr,
		core::{
			ConnectedPoint,
			identity,
			muxing::{StreamMuxerBox, SubstreamRef},
			transport::{Transport, boxed::Boxed, memory::MemoryTransport},
			upgrade
		},
		noise::{self, Keypair, X25519, NoiseConfig},
		swarm::{NetworkBehaviour, NetworkBehaviourAction, PollParameters},
		yamux
	};
	use sc_client_api::StorageProof;
	use sc_client::light::fetcher;
	use sp_blockchain::{Error as ClientError};
	use sp_core::storage::ChildInfo;
	use std::{
		collections::HashSet,
		io,
		iter::{self, FromIterator},
		pin::Pin,
		sync::Arc,
		task::{Context, Poll}
	};
	use sp_runtime::{generic::Header, traits::BlakeTwo256};
	use super::{Event, LightClientHandler, Request, OutboundProtocol, PeerStatus};
	use void::Void;

	const CHILD_INFO: ChildInfo<'static> = ChildInfo::new_default(b"foobarbaz");

	type Block = sp_runtime::generic::Block<Header<u64, BlakeTwo256>, substrate_test_runtime::Extrinsic>;
	type Handler = LightClientHandler<Block>;
	type Swarm = libp2p::swarm::Swarm<Handler>;

	fn empty_proof() -> Vec<u8> {
		StorageProof::empty().encode()
	}

	fn make_swarm(ok: bool, ps: sc_peerset::PeersetHandle, cf: super::Config) -> Swarm {
		let client = Arc::new(substrate_test_runtime_client::new());
		let checker = Arc::new(DummyFetchChecker::new(ok));
		let id_key = identity::Keypair::generate_ed25519();
		let dh_key = Keypair::<X25519>::new().into_authentic(&id_key).unwrap();
		let local_peer = id_key.public().into_peer_id();
		let transport = MemoryTransport::default()
			.upgrade(upgrade::Version::V1)
			.authenticate(NoiseConfig::xx(dh_key).into_authenticated())
			.multiplex(yamux::Config::default())
			.map(|(peer, muxer), _| (peer, StreamMuxerBox::new(muxer)))
			.map_err(|e| io::Error::new(io::ErrorKind::Other, e))
			.boxed();
		Swarm::new(transport, LightClientHandler::new(cf, client, checker, ps), local_peer)
	}

	fn make_config() -> super::Config {
		super::Config::new(&ProtocolId::from(&b"foo"[..]))
	}

	struct EmptyPollParams(PeerId);

	impl PollParameters for EmptyPollParams {
		type SupportedProtocolsIter = iter::Empty<Vec<u8>>;
		type ListenedAddressesIter = iter::Empty<Multiaddr>;
		type ExternalAddressesIter = iter::Empty<Multiaddr>;

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
		let cfg = sc_peerset::PeersetConfig {
			in_peers: 128,
			out_peers: 128,
			bootnodes: Vec::new(),
			reserved_only: false,
			reserved_nodes: Vec::new(),
		};
		sc_peerset::Peerset::from_config(cfg)
	}

	fn make_behaviour
		( ok: bool
		, ps: sc_peerset::PeersetHandle
		, cf: super::Config
		) -> LightClientHandler<Block>
	{
		let client = Arc::new(substrate_test_runtime_client::new());
		let checker = Arc::new(DummyFetchChecker::new(ok));
		LightClientHandler::new(cf, client, checker, ps)
	}

	fn empty_dialer() -> ConnectedPoint {
		ConnectedPoint::Dialer { address: Multiaddr::empty() }
	}

	fn poll(mut b: &mut LightClientHandler<Block>) -> Poll<NetworkBehaviourAction<OutboundProtocol, Void>> {
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

		behaviour.inject_connected(peer.clone(), empty_dialer());
		assert_eq!(1, behaviour.peers.len());

		behaviour.inject_disconnected(&peer, empty_dialer());
		assert_eq!(0, behaviour.peers.len())
	}

	#[test]
	fn disconnects_from_peer_if_request_times_out() {
		let peer0 = PeerId::random();
		let peer1 = PeerId::random();
		let pset = peerset();
		let mut behaviour = make_behaviour(true, pset.1, make_config());

		behaviour.inject_connected(peer0.clone(), empty_dialer());
		behaviour.inject_connected(peer1.clone(), empty_dialer());

		// We now know about two peers.
		assert_eq!(HashSet::from_iter(&[peer0.clone(), peer1.clone()]), behaviour.peers.keys().collect::<HashSet<_>>());

		// No requests have been made yet.
		assert!(behaviour.pending_requests.is_empty());
		assert!(behaviour.outstanding.is_empty());

		// Issue our first request!
		let chan = oneshot::channel();
		let request = fetcher::RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: Some(1),
		};
		behaviour.request(Request::Call { request, sender: chan.0 }).unwrap();
		assert_eq!(1, behaviour.pending_requests.len());

		// The behaviour should now attempt to send the request.
		assert_matches!(poll(&mut behaviour), Poll::Ready(NetworkBehaviourAction::SendEvent { peer_id, .. }) => {
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

		behaviour.inject_connected(peer.clone(), empty_dialer());
		assert_eq!(1, behaviour.peers.len());

		let chan = oneshot::channel();
		let request = fetcher::RemoteCallRequest {
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
			let r = api::v1::light::RemoteCallResponse { proof: empty_proof() };
			api::v1::light::Response {
				response: Some(api::v1::light::response::Response::RemoteCallResponse(r)),
			}
		};

		behaviour.inject_node_event(peer.clone(), Event::Response(request_id, response));
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

		behaviour.inject_connected(peer.clone(), empty_dialer());
		assert_eq!(1, behaviour.peers.len());
		assert_eq!(0, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len());

		// Some unsolicited response
		let response = {
			let r = api::v1::light::RemoteCallResponse { proof: empty_proof() };
			api::v1::light::Response {
				response: Some(api::v1::light::response::Response::RemoteCallResponse(r)),
			}
		};

		behaviour.inject_node_event(peer.clone(), Event::Response(2347895932, response));

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

		behaviour.inject_connected(peer.clone(), empty_dialer());
		assert_eq!(1, behaviour.peers.len());

		let chan = oneshot::channel();
		let request = fetcher::RemoteCallRequest {
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
			let r = api::v1::light::RemoteReadResponse { proof: empty_proof() }; // Not a RemoteCallResponse!
			api::v1::light::Response {
				response: Some(api::v1::light::response::Response::RemoteReadResponse(r)),
			}
		};

		behaviour.inject_node_event(peer.clone(), Event::Response(request_id, response));
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

		behaviour.inject_connected(peer1.clone(), empty_dialer());
		behaviour.inject_connected(peer2.clone(), empty_dialer());
		behaviour.inject_connected(peer3.clone(), empty_dialer());
		behaviour.inject_connected(peer4.clone(), empty_dialer());
		assert_eq!(4, behaviour.peers.len());

		let mut chan = oneshot::channel();
		let request = fetcher::RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: Some(3), // Attempt up to three retries.
		};
		behaviour.request(Request::Call { request, sender: chan.0 }).unwrap();

		assert_eq!(1, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len());
		assert_matches!(poll(&mut behaviour), Poll::Ready(NetworkBehaviourAction::SendEvent { .. }));
		assert_eq!(0, behaviour.pending_requests.len());
		assert_eq!(1, behaviour.outstanding.len());

		for _ in 0 .. 3 {
			// Construct an invalid response
			let request_id = *behaviour.outstanding.keys().next().unwrap();
			let responding_peer = behaviour.outstanding.values().next().unwrap().peer.clone();
			let response = {
				let r = api::v1::light::RemoteCallResponse { proof: empty_proof() };
				api::v1::light::Response {
					response: Some(api::v1::light::response::Response::RemoteCallResponse(r))
				}
			};
			behaviour.inject_node_event(responding_peer, Event::Response(request_id, response.clone()));
			assert_matches!(poll(&mut behaviour), Poll::Ready(NetworkBehaviourAction::SendEvent { .. }));
			assert_matches!(chan.1.try_recv(), Ok(None))
		}
		// Final invalid response
		let request_id = *behaviour.outstanding.keys().next().unwrap();
		let responding_peer = behaviour.outstanding.values().next().unwrap().peer.clone();
		let response = {
			let r = api::v1::light::RemoteCallResponse { proof: empty_proof() };
			api::v1::light::Response {
				response: Some(api::v1::light::response::Response::RemoteCallResponse(r)),
			}
		};
		behaviour.inject_node_event(responding_peer, Event::Response(request_id, response));
		assert_matches!(poll(&mut behaviour), Poll::Pending);
		assert_matches!(chan.1.try_recv(), Ok(Some(Err(ClientError::RemoteFetchFailed))))
	}

	fn issue_request(request: Request<Block>) {
		let peer = PeerId::random();
		let pset = peerset();
		let mut behaviour = make_behaviour(true, pset.1, make_config());

		behaviour.inject_connected(peer.clone(), empty_dialer());
		assert_eq!(1, behaviour.peers.len());

		let response = match request {
			Request::Header{..} => {
				let r = api::v1::light::RemoteHeaderResponse {
					header: dummy_header().encode(),
					proof: empty_proof()
				};
				api::v1::light::Response {
					response: Some(api::v1::light::response::Response::RemoteHeaderResponse(r)),
				}
			}
			Request::Read{..} => {
				let r = api::v1::light::RemoteReadResponse { proof: empty_proof() };
				api::v1::light::Response {
					response: Some(api::v1::light::response::Response::RemoteReadResponse(r)),
				}
			}
			Request::ReadChild{..} => {
				let r = api::v1::light::RemoteReadResponse { proof: empty_proof() };
				api::v1::light::Response {
					response: Some(api::v1::light::response::Response::RemoteReadResponse(r)),
				}
			}
			Request::Call{..} => {
				let r = api::v1::light::RemoteCallResponse { proof: empty_proof() };
				api::v1::light::Response {
					response: Some(api::v1::light::response::Response::RemoteCallResponse(r)),
				}
			}
			Request::Changes{..} => {
				let r = api::v1::light::RemoteChangesResponse {
					max: iter::repeat(1).take(32).collect(),
					proof: Vec::new(),
					roots: Vec::new(),
					roots_proof: empty_proof()
				};
				api::v1::light::Response {
					response: Some(api::v1::light::response::Response::RemoteChangesResponse(r)),
				}
			}
		};

		behaviour.request(request).unwrap();

		assert_eq!(1, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len());
		assert_matches!(poll(&mut behaviour), Poll::Ready(NetworkBehaviourAction::SendEvent { .. }));
		assert_eq!(0, behaviour.pending_requests.len());
		assert_eq!(1, behaviour.outstanding.len());
		assert_eq!(1, *behaviour.outstanding.keys().next().unwrap());

		behaviour.inject_node_event(peer.clone(), Event::Response(1, response));

		poll(&mut behaviour);

		assert_eq!(0, behaviour.pending_requests.len());
		assert_eq!(0, behaviour.outstanding.len())
	}

	#[test]
	fn receives_remote_call_response() {
		let mut chan = oneshot::channel();
		let request = fetcher::RemoteCallRequest {
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
		let request = fetcher::RemoteReadRequest {
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
		let info = CHILD_INFO.info();
		let mut chan = oneshot::channel();
		let request = fetcher::RemoteReadChildRequest {
			header: dummy_header(),
			block: Default::default(),
			storage_key: b":child_storage:sub".to_vec(),
			keys: vec![b":key".to_vec()],
			child_info: info.0.to_vec(),
			child_type: info.1,
			retry_count: None,
		};
		issue_request(Request::ReadChild { request, sender: chan.0 });
		assert_matches!(chan.1.try_recv(), Ok(Some(Ok(_))))
	}

	#[test]
	fn receives_remote_header_response() {
		let mut chan = oneshot::channel();
		let request = fetcher::RemoteHeaderRequest {
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
		let request = fetcher::RemoteChangesRequest {
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
		let request = fetcher::RemoteCallRequest {
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
		let request = fetcher::RemoteReadRequest {
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
		let info = CHILD_INFO.info();
		let chan = oneshot::channel();
		let request = fetcher::RemoteReadChildRequest {
			header: dummy_header(),
			block: Default::default(),
			storage_key: b":child_storage:sub".to_vec(),
			keys: vec![b":key".to_vec()],
			child_info: info.0.to_vec(),
			child_type: info.1,
			retry_count: None,
		};
		send_receive(Request::ReadChild { request, sender: chan.0 });
		assert_eq!(Some(vec![42]), task::block_on(chan.1).unwrap().unwrap().remove(&b":key"[..]).unwrap());
		//                   ^--- from `DummyFetchChecker::check_read_child_proof`
	}

	#[test]
	fn send_receive_header() {
		let _ = env_logger::try_init();
		let chan = oneshot::channel();
		let request = fetcher::RemoteHeaderRequest {
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
		let request = fetcher::RemoteChangesRequest {
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
}
