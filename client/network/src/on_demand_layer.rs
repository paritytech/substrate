// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! On-demand requests service.

use crate::light_client_handler;

use futures::{channel::oneshot, prelude::*};
use parking_lot::Mutex;
use sc_client_api::{
	FetchChecker, Fetcher, AuxStore, RemoteBodyRequest, RemoteCallRequest, RemoteChangesRequest,
	RemoteHeaderRequest, RemoteReadChildRequest, RemoteReadRequest, StorageProof, ChangesProof,
};
use sp_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use sp_blockchain::{Error as ClientError, Cache, well_known_cache_keys};
use sp_runtime::{
	traits::{Block as BlockT, Header as HeaderT, NumberFor},
	generic::BlockId
};
use sp_core::storage::well_known_keys;
use sc_client_db::light::LightStorage;
use std::{collections::HashMap, pin::Pin, sync::Arc, task::Context, task::Poll};

/// Implements the `Fetcher` trait of the client. Makes it possible for the light client to perform
/// network requests for some state.
///
/// This implementation stores all the requests in a queue. The network, in parallel, is then
/// responsible for pulling elements out of that queue and fulfilling them.
pub struct OnDemand<B: BlockT> {
	/// Objects that checks whether what has been retrieved is correct.
	checker: Arc<dyn FetchChecker<B>>,

	/// Reference to backend.
	backend: Arc<LightStorage<B>>,

	/// Reference to cache.
	cache: Arc<dyn Cache<B>>,

	/// Queue of requests. Set to `Some` at initialization, then extracted by the network.
	///
	/// Note that a better alternative would be to use a MPMC queue here, and add a `poll` method
	/// from the `OnDemand`. However there exists no popular implementation of MPMC channels in
	/// asynchronous Rust at the moment
	requests_queue: Mutex<Option<TracingUnboundedReceiver<light_client_handler::Request<B>>>>,

	/// Sending side of `requests_queue`.
	requests_send: TracingUnboundedSender<light_client_handler::Request<B>>,
}

/// Dummy implementation of `FetchChecker` that always assumes that responses are bad.
///
/// Considering that it is the responsibility of the client to build the fetcher, it can use this
/// implementation if it knows that it will never perform any request.
#[derive(Default, Clone)]
pub struct AlwaysBadChecker;

impl<Block: BlockT> FetchChecker<Block> for AlwaysBadChecker {
	fn check_header_proof(
		&self,
		_request: &RemoteHeaderRequest<Block::Header>,
		_remote_header: Option<Block::Header>,
		_remote_proof: StorageProof,
	) -> Result<Block::Header, ClientError> {
		Err(ClientError::Msg("AlwaysBadChecker".into()))
	}

	fn check_read_proof(
		&self,
		_request: &RemoteReadRequest<Block::Header>,
		_remote_proof: StorageProof,
	) -> Result<HashMap<Vec<u8>,Option<Vec<u8>>>, ClientError> {
		Err(ClientError::Msg("AlwaysBadChecker".into()))
	}

	fn check_read_child_proof(
		&self,
		_request: &RemoteReadChildRequest<Block::Header>,
		_remote_proof: StorageProof,
	) -> Result<HashMap<Vec<u8>, Option<Vec<u8>>>, ClientError> {
		Err(ClientError::Msg("AlwaysBadChecker".into()))
	}

	fn check_execution_proof(
		&self,
		_request: &RemoteCallRequest<Block::Header>,
		_remote_proof: StorageProof,
	) -> Result<Vec<u8>, ClientError> {
		Err(ClientError::Msg("AlwaysBadChecker".into()))
	}

	fn check_changes_proof(
		&self,
		_request: &RemoteChangesRequest<Block::Header>,
		_remote_proof: ChangesProof<Block::Header>
	) -> Result<Vec<(NumberFor<Block>, u32)>, ClientError> {
		Err(ClientError::Msg("AlwaysBadChecker".into()))
	}

	fn check_body_proof(
		&self,
		_request: &RemoteBodyRequest<Block::Header>,
		_body: Vec<Block::Extrinsic>
	) -> Result<Vec<Block::Extrinsic>, ClientError> {
		Err(ClientError::Msg("AlwaysBadChecker".into()))
	}
}

impl<B: BlockT> OnDemand<B>
where
	B::Header: HeaderT,
{
	/// Creates new on-demand service.
	pub fn new(
		checker: Arc<dyn FetchChecker<B>>,
		cache: Arc<dyn Cache<B>>,
		backend: Arc<LightStorage<B>>,
	) -> Self {
		let (requests_send, requests_queue) = tracing_unbounded("mpsc_ondemand");
		let requests_queue = Mutex::new(Some(requests_queue));

		OnDemand {
			cache,
			backend,
			checker,
			requests_queue,
			requests_send,
		}
	}

	/// Get checker reference.
	pub fn checker(&self) -> &Arc<dyn FetchChecker<B>> {
		&self.checker
	}

	/// Extracts the queue of requests.
	///
	/// Whenever one of the methods of the `Fetcher` trait is called, an element is pushed on this
	/// channel.
	///
	/// If this function returns `None`, that means that the receiver has already been extracted in
	/// the past, and therefore that something already handles the requests.
	pub(crate) fn extract_receiver(&self)
		-> Option<TracingUnboundedReceiver<light_client_handler::Request<B>>>
	{
		self.requests_queue.lock().take()
	}
}

impl<B> Fetcher<B> for OnDemand<B>
where
	B: BlockT,
	B::Header: HeaderT,
{
	type RemoteHeaderResult = RemoteResponse<B::Header>;
	type RemoteReadResult = RemoteResponse<HashMap<Vec<u8>, Option<Vec<u8>>>>;
	type RemoteCallResult = Pin<Box<dyn Future<Output = Result<Vec<u8>, ClientError>> + Send>>;
	type RemoteChangesResult = RemoteResponse<Vec<(NumberFor<B>, u32)>>;
	type RemoteBodyResult = RemoteResponse<Vec<B::Extrinsic>>;

	fn remote_header(&self, request: RemoteHeaderRequest<B::Header>) -> Self::RemoteHeaderResult {
		let (sender, receiver) = oneshot::channel();
		let _ = self
			.requests_send
			.unbounded_send(light_client_handler::Request::Header { request, sender });
		RemoteResponse { receiver }
	}

	fn remote_read(&self, request: RemoteReadRequest<B::Header>) -> Self::RemoteReadResult {
		let (sender, receiver) = oneshot::channel();
		let _ = self
			.requests_send
			.unbounded_send(light_client_handler::Request::Read { request, sender });
		RemoteResponse { receiver }
	}

	fn remote_read_child(
		&self,
		request: RemoteReadChildRequest<B::Header>,
	) -> Self::RemoteReadResult {
		let (sender, receiver) = oneshot::channel();
		let _ = self
			.requests_send
			.unbounded_send(light_client_handler::Request::ReadChild { request, sender });
		RemoteResponse { receiver }
	}

	fn remote_call(&self, request: RemoteCallRequest<B::Header>) -> Self::RemoteCallResult {
		let (header, cache, backend, req_sender) = (
			request.header.clone(),
			self.cache.clone(),
			self.backend.clone(),
			self.requests_send.clone(),
		);


		async move {
			fetch_and_store_code(header, cache, backend, req_sender.clone()).await?;

			let (sender, receiver) = oneshot::channel();

			let _ = req_sender
				.unbounded_send(light_client_handler::Request::Call { request, sender });

			let data = receiver.await
				.map_err(|_| ClientError::RemoteFetchCancelled)??;
			Ok(data)
		}.boxed()
	}

	fn remote_changes(
		&self,
		request: RemoteChangesRequest<B::Header>,
	) -> Self::RemoteChangesResult {
		let (sender, receiver) = oneshot::channel();
		let _ = self
			.requests_send
			.unbounded_send(light_client_handler::Request::Changes { request, sender });
		RemoteResponse { receiver }
	}

	fn remote_body(&self, request: RemoteBodyRequest<B::Header>) -> Self::RemoteBodyResult {
		let (sender, receiver) = oneshot::channel();
		let _ = self
			.requests_send
			.unbounded_send(light_client_handler::Request::Body { request, sender });
		RemoteResponse { receiver }
	}
}

/// Future for an on-demand remote call response.
pub struct RemoteResponse<T> {
	receiver: oneshot::Receiver<Result<T, ClientError>>,
}

impl<T> Future for RemoteResponse<T> {
	type Output = Result<T, ClientError>;

	fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		match self.receiver.poll_unpin(cx) {
			Poll::Ready(Ok(res)) => Poll::Ready(res),
			Poll::Ready(Err(_)) => Poll::Ready(Err(ClientError::RemoteFetchCancelled)),
			Poll::Pending => Poll::Pending,
		}
	}
}

/// Called exclusively on every RemoteCallRequest, checks that we have the runtime code available
/// to verify the `RemoteCallResponse` and if not, issues a RemoteReadRequest to fetch code.
async fn fetch_and_store_code<B>(
	header: B::Header,
	cache: Arc<dyn Cache<B>>,
	backend: Arc<LightStorage<B>>,
	req_sender: TracingUnboundedSender<light_client_handler::Request<B>>,
) -> Result<(), ClientError>
	where
		B: BlockT,
{
	if let Ok(Some((_from, _to, hash))) = cache.get_at(
		&well_known_cache_keys::CODE_HASH,
		&BlockId::Hash(header.hash())
	) {
		let mut key = Vec::new();
		key.extend_from_slice(b"runtime-code");
		key.extend_from_slice(&hash);
		// alas! we don't have the runtime code locally.
		if let Ok(None) = backend.get_aux(&key) {
			let (sender, receiver) = oneshot::channel();
			// just checking we have the runtime code for this block.
			let _ = req_sender.unbounded_send(
				light_client_handler::Request::Read {
					sender,
					request: RemoteReadRequest {
						keys: vec![well_known_keys::CODE.to_vec()],
						block: header.hash(),
						header,
						// todo: shouldn't we retry?
						retry_count: None
					}
				}
			);
			let mut data = receiver.await
				.map_err(|_| ClientError::RemoteFetchCancelled)??;
			// todo: i assume it's possible that full nodes send us an empty response, how should this be handled?
			if let Some(Some(runtime_code)) = data.remove(&well_known_keys::CODE.to_vec()) {
				// i'd like to believe there's no need to hash runtime code here and compare it with hash.
				backend.insert_aux(&[(hash.as_ref(), runtime_code.as_ref())], &[])?;
			} else {
				// for lack of a better error
				return Err(ClientError::RemoteFetchFailed)
			}
		}
	};

	Ok(())
}
