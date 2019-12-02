// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! On-demand requests service.

use crate::protocol::light_dispatch::RequestData;
use std::collections::HashMap;
use std::sync::Arc;
use futures::{prelude::*, sync::mpsc, sync::oneshot};
use futures03::compat::{Compat01As03, Future01CompatExt as _};
use parking_lot::Mutex;
use sp_blockchain::Error as ClientError;
use client_api::{Fetcher, FetchChecker, RemoteHeaderRequest,
	RemoteCallRequest, RemoteReadRequest, RemoteChangesRequest,
	RemoteReadChildRequest, RemoteBodyRequest};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, NumberFor};

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
	requests_queue: Mutex<Option<mpsc::UnboundedReceiver<RequestData<B>>>>,

	/// Sending side of `requests_queue`.
	requests_send: mpsc::UnboundedSender<RequestData<B>>,
}

impl<B: BlockT> OnDemand<B> where
	B::Header: HeaderT,
{
	/// Creates new on-demand service.
	pub fn new(checker: Arc<dyn FetchChecker<B>>) -> Self {
		let (requests_send, requests_queue) = mpsc::unbounded();
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
	pub(crate) fn extract_receiver(&self) -> Option<mpsc::UnboundedReceiver<RequestData<B>>> {
		self.requests_queue.lock().take()
	}
}

impl<B> Fetcher<B> for OnDemand<B> where
	B: BlockT,
	B::Header: HeaderT,
{
	type RemoteHeaderResult = Compat01As03<RemoteResponse<B::Header>>;
	type RemoteReadResult = Compat01As03<RemoteResponse<HashMap<Vec<u8>, Option<Vec<u8>>>>>;
	type RemoteCallResult = Compat01As03<RemoteResponse<Vec<u8>>>;
	type RemoteChangesResult = Compat01As03<RemoteResponse<Vec<(NumberFor<B>, u32)>>>;
	type RemoteBodyResult = Compat01As03<RemoteResponse<Vec<B::Extrinsic>>>;

	fn remote_header(&self, request: RemoteHeaderRequest<B::Header>) -> Self::RemoteHeaderResult {
		let (sender, receiver) = oneshot::channel();
		let _ = self.requests_send.unbounded_send(RequestData::RemoteHeader(request, sender));
		RemoteResponse { receiver }.compat()
	}

	fn remote_read(&self, request: RemoteReadRequest<B::Header>) -> Self::RemoteReadResult {
		let (sender, receiver) = oneshot::channel();
		let _ = self.requests_send.unbounded_send(RequestData::RemoteRead(request, sender));
		RemoteResponse { receiver }.compat()
	}

	fn remote_read_child(
		&self,
		request: RemoteReadChildRequest<B::Header>
	) -> Self::RemoteReadResult {
		let (sender, receiver) = oneshot::channel();
		let _ = self.requests_send.unbounded_send(RequestData::RemoteReadChild(request, sender));
		RemoteResponse { receiver }.compat()
	}

	fn remote_call(&self, request: RemoteCallRequest<B::Header>) -> Self::RemoteCallResult {
		let (sender, receiver) = oneshot::channel();
		let _ = self.requests_send.unbounded_send(RequestData::RemoteCall(request, sender));
		RemoteResponse { receiver }.compat()
	}

	fn remote_changes(&self, request: RemoteChangesRequest<B::Header>) -> Self::RemoteChangesResult {
		let (sender, receiver) = oneshot::channel();
		let _ = self.requests_send.unbounded_send(RequestData::RemoteChanges(request, sender));
		RemoteResponse { receiver }.compat()
	}

	fn remote_body(&self, request: RemoteBodyRequest<B::Header>) -> Self::RemoteBodyResult {
		let (sender, receiver) = oneshot::channel();
		let _ = self.requests_send.unbounded_send(RequestData::RemoteBody(request, sender));
		RemoteResponse { receiver }.compat()
	}
}

/// Future for an on-demand remote call response.
pub struct RemoteResponse<T> {
	receiver: oneshot::Receiver<Result<T, ClientError>>,
}

impl<T> Future for RemoteResponse<T> {
	type Item = T;
	type Error = ClientError;

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
		self.receiver.poll()
			.map_err(|_| ClientError::RemoteFetchCancelled.into())
			.and_then(|r| match r {
				Async::Ready(Ok(ready)) => Ok(Async::Ready(ready)),
				Async::Ready(Err(error)) => Err(error),
				Async::NotReady => Ok(Async::NotReady),
			})
	}
}
