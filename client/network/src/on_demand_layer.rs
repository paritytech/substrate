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
	FetchChecker, Fetcher, RemoteBodyRequest, RemoteCallRequest, RemoteChangesRequest,
	RemoteHeaderRequest, RemoteReadChildRequest, RemoteReadRequest, StorageProof, ChangesProof,
};
use sp_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use sp_blockchain::Error as ClientError;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, NumberFor};
use std::{collections::HashMap, pin::Pin, sync::Arc, task::Context, task::Poll};

/// Implements the `Fetcher` trait of the client. Makes it possible for the light client to perform
/// network requests for some state.
///
/// This implementation stores all the requests in a queue. The network, in parallel, is then
/// responsible for pulling elements out of that queue and fulfilling them.
pub struct OnDemand<B: BlockT> {
	/// Objects that checks whether what has been retrieved is correct.
	checker: Arc<dyn FetchChecker<B>>,

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
	pub fn new(checker: Arc<dyn FetchChecker<B>>) -> Self {
		let (requests_send, requests_queue) = tracing_unbounded("mpsc_ondemand");
		let requests_queue = Mutex::new(Some(requests_queue));

		OnDemand {
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
	type RemoteCallResult = RemoteResponse<Vec<u8>>;
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
		let (sender, receiver) = oneshot::channel();
		let _ = self
			.requests_send
			.unbounded_send(light_client_handler::Request::Call { request, sender });
		RemoteResponse { receiver }
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
