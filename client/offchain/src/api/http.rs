// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! This module is composed of two structs: [`HttpApi`] and [`HttpWorker`]. Calling the [`http`]
//! function returns a pair of [`HttpApi`] and [`HttpWorker`] that share some state.
//!
//! The [`HttpApi`] is (indirectly) passed to the runtime when calling an offchain worker, while
//! the [`HttpWorker`] must be processed in the background. The [`HttpApi`] mimics the API of the
//! HTTP-related methods available to offchain workers.
//!
//! The reason for this design is driven by the fact that HTTP requests should continue running
//! (i.e.: the socket should continue being processed) in the background even if the runtime isn't
//! actively calling any function.

use crate::api::timestamp;
use bytes::buf::{Buf, Reader};
use fnv::FnvHashMap;
use futures::{channel::mpsc, future, prelude::*};
use hyper::{client, Body, Client as HyperClient};
use hyper_rustls::HttpsConnector;
use log::error;
use sp_core::offchain::{HttpError, HttpRequestId, HttpRequestStatus, Timestamp};
use sp_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use std::{
	convert::TryFrom,
	fmt,
	io::Read as _,
	pin::Pin,
	sync::Arc,
	task::{Context, Poll},
};

/// Wrapper struct used for keeping the hyper_rustls client running.
#[derive(Clone)]
pub struct SharedClient(Arc<HyperClient<HttpsConnector<client::HttpConnector>, Body>>);

impl SharedClient {
	pub fn new() -> Self {
		Self(Arc::new(HyperClient::builder().build(HttpsConnector::with_native_roots())))
	}
}

/// Creates a pair of [`HttpApi`] and [`HttpWorker`].
pub fn http(shared_client: SharedClient) -> (HttpApi, HttpWorker) {
	let (to_worker, from_api) = tracing_unbounded("mpsc_ocw_to_worker");
	let (to_api, from_worker) = tracing_unbounded("mpsc_ocw_to_api");

	let api = HttpApi {
		to_worker,
		from_worker: from_worker.fuse(),
		// We start with a random ID for the first HTTP request, to prevent mischievous people from
		// writing runtime code with hardcoded IDs.
		next_id: HttpRequestId(rand::random::<u16>() % 2000),
		requests: FnvHashMap::default(),
	};

	let engine =
		HttpWorker { to_api, from_api, http_client: shared_client.0, requests: Vec::new() };

	(api, engine)
}

/// Provides HTTP capabilities.
///
/// Since this struct is a helper for offchain workers, its API is mimicking the API provided
/// to offchain workers.
pub struct HttpApi {
	/// Used to sends messages to the worker.
	to_worker: TracingUnboundedSender<ApiToWorker>,
	/// Used to receive messages from the worker.
	/// We use a `Fuse` in order to have an extra protection against panicking.
	from_worker: stream::Fuse<TracingUnboundedReceiver<WorkerToApi>>,
	/// Id to assign to the next HTTP request that is started.
	next_id: HttpRequestId,
	/// List of HTTP requests in preparation or in progress.
	requests: FnvHashMap<HttpRequestId, HttpApiRequest>,
}

/// One active request within `HttpApi`.
enum HttpApiRequest {
	/// The request object is being constructed locally and not started yet.
	NotDispatched(hyper::Request<hyper::Body>, hyper::body::Sender),
	/// The request has been dispatched and we're in the process of sending out the body (if the
	/// field is `Some`) or waiting for a response (if the field is `None`).
	Dispatched(Option<hyper::body::Sender>),
	/// Received a response.
	Response(HttpApiRequestRp),
	/// A request has been dispatched but the worker notified us of an error. We report this
	/// failure to the user as an `IoError` and remove the request from the list as soon as
	/// possible.
	Fail(hyper::Error),
}

/// A request within `HttpApi` that has received a response.
struct HttpApiRequestRp {
	/// We might still be writing the request's body when the response comes.
	/// This field allows to continue writing that body.
	sending_body: Option<hyper::body::Sender>,
	/// Status code of the response.
	status_code: hyper::StatusCode,
	/// Headers of the response.
	headers: hyper::HeaderMap,
	/// Body of the response, as a channel of `Chunk` objects.
	/// While the code is designed to drop the `Receiver` once it ends, we wrap it within a
	/// `Fuse` in order to be extra precautious about panics.
	/// Elements extracted from the channel are first put into `current_read_chunk`.
	/// If the channel produces an error, then that is translated into an `IoError` and the request
	/// is removed from the list.
	body: stream::Fuse<mpsc::Receiver<Result<hyper::body::Bytes, hyper::Error>>>,
	/// Chunk that has been extracted from the channel and that is currently being read.
	/// Reading data from the response should read from this field in priority.
	current_read_chunk: Option<Reader<hyper::body::Bytes>>,
}

impl HttpApi {
	/// Mimics the corresponding method in the offchain API.
	pub fn request_start(&mut self, method: &str, uri: &str) -> Result<HttpRequestId, ()> {
		// Start by building the prototype of the request.
		// We do this first so that we don't touch anything in `self` if building the prototype
		// fails.
		let (body_sender, body) = hyper::Body::channel();
		let mut request = hyper::Request::new(body);
		*request.method_mut() = hyper::Method::from_bytes(method.as_bytes()).map_err(|_| ())?;
		*request.uri_mut() = hyper::Uri::from_maybe_shared(uri.to_owned()).map_err(|_| ())?;

		let new_id = self.next_id;
		debug_assert!(!self.requests.contains_key(&new_id));
		match self.next_id.0.checked_add(1) {
			Some(new_id) => self.next_id.0 = new_id,
			None => {
				error!("Overflow in offchain worker HTTP request ID assignment");
				return Err(())
			},
		};
		self.requests
			.insert(new_id, HttpApiRequest::NotDispatched(request, body_sender));

		Ok(new_id)
	}

	/// Mimics the corresponding method in the offchain API.
	pub fn request_add_header(
		&mut self,
		request_id: HttpRequestId,
		name: &str,
		value: &str,
	) -> Result<(), ()> {
		let request = match self.requests.get_mut(&request_id) {
			Some(&mut HttpApiRequest::NotDispatched(ref mut rq, _)) => rq,
			_ => return Err(()),
		};

		let name = hyper::header::HeaderName::try_from(name).map_err(drop)?;
		let value = hyper::header::HeaderValue::try_from(value).map_err(drop)?;
		// Note that we're always appending headers and never replacing old values.
		// We assume here that the user knows what they're doing.
		request.headers_mut().append(name, value);
		Ok(())
	}

	/// Mimics the corresponding method in the offchain API.
	pub fn request_write_body(
		&mut self,
		request_id: HttpRequestId,
		chunk: &[u8],
		deadline: Option<Timestamp>,
	) -> Result<(), HttpError> {
		// Extract the request from the list.
		// Don't forget to add it back if necessary when returning.
		let mut request = self.requests.remove(&request_id).ok_or_else(|| HttpError::Invalid)?;

		let mut deadline = timestamp::deadline_to_future(deadline);
		// Closure that writes data to a sender, taking the deadline into account. Can return `Ok`
		// (if the body has been written), or `DeadlineReached`, or `IoError`.
		// If `IoError` is returned, don't forget to remove the request from the list.
		let mut poll_sender = move |sender: &mut hyper::body::Sender| -> Result<(), HttpError> {
			let mut when_ready = future::maybe_done(future::poll_fn(|cx| sender.poll_ready(cx)));
			futures::executor::block_on(future::select(&mut when_ready, &mut deadline));
			match when_ready {
				future::MaybeDone::Done(Ok(())) => {},
				future::MaybeDone::Done(Err(_)) => return Err(HttpError::IoError),
				future::MaybeDone::Future(_) | future::MaybeDone::Gone => {
					debug_assert!(matches!(deadline, future::MaybeDone::Done(..)));
					return Err(HttpError::DeadlineReached)
				},
			};

			futures::executor::block_on(
				sender.send_data(hyper::body::Bytes::from(chunk.to_owned())),
			)
			.map_err(|_| {
				error!("HTTP sender refused data despite being ready");
				HttpError::IoError
			})
		};

		loop {
			request = match request {
				HttpApiRequest::NotDispatched(request, sender) => {
					// If the request is not dispatched yet, dispatch it and loop again.
					let _ = self
						.to_worker
						.unbounded_send(ApiToWorker::Dispatch { id: request_id, request });
					HttpApiRequest::Dispatched(Some(sender))
				},

				HttpApiRequest::Dispatched(Some(mut sender)) => {
					if !chunk.is_empty() {
						match poll_sender(&mut sender) {
							Err(HttpError::IoError) => return Err(HttpError::IoError),
							other => {
								self.requests
									.insert(request_id, HttpApiRequest::Dispatched(Some(sender)));
								return other
							},
						}
					} else {
						// Writing an empty body is a hint that we should stop writing. Dropping
						// the sender.
						self.requests.insert(request_id, HttpApiRequest::Dispatched(None));
						return Ok(())
					}
				},

				HttpApiRequest::Response(
					mut response @ HttpApiRequestRp { sending_body: Some(_), .. },
				) => {
					if !chunk.is_empty() {
						match poll_sender(
							response
								.sending_body
								.as_mut()
								.expect("Can only enter this match branch if Some; qed"),
						) {
							Err(HttpError::IoError) => return Err(HttpError::IoError),
							other => {
								self.requests
									.insert(request_id, HttpApiRequest::Response(response));
								return other
							},
						}
					} else {
						// Writing an empty body is a hint that we should stop writing. Dropping
						// the sender.
						self.requests.insert(
							request_id,
							HttpApiRequest::Response(HttpApiRequestRp {
								sending_body: None,
								..response
							}),
						);
						return Ok(())
					}
				},

				HttpApiRequest::Fail(_) =>
				// If the request has already failed, return without putting back the request
				// in the list.
					return Err(HttpError::IoError),

				v @ HttpApiRequest::Dispatched(None) |
				v @ HttpApiRequest::Response(HttpApiRequestRp { sending_body: None, .. }) => {
					// We have already finished sending this body.
					self.requests.insert(request_id, v);
					return Err(HttpError::Invalid)
				},
			}
		}
	}

	/// Mimics the corresponding method in the offchain API.
	pub fn response_wait(
		&mut self,
		ids: &[HttpRequestId],
		deadline: Option<Timestamp>,
	) -> Vec<HttpRequestStatus> {
		// First of all, dispatch all the non-dispatched requests and drop all senders so that the
		// user can't write anymore data.
		for id in ids {
			match self.requests.get_mut(id) {
				Some(HttpApiRequest::NotDispatched(_, _)) => {},
				Some(HttpApiRequest::Dispatched(sending_body)) |
				Some(HttpApiRequest::Response(HttpApiRequestRp { sending_body, .. })) => {
					let _ = sending_body.take();
					continue
				},
				_ => continue,
			};

			let (request, _sender) = match self.requests.remove(id) {
				Some(HttpApiRequest::NotDispatched(rq, s)) => (rq, s),
				_ => unreachable!("we checked for NotDispatched above; qed"),
			};

			let _ = self.to_worker.unbounded_send(ApiToWorker::Dispatch { id: *id, request });

			// We also destroy the sender in order to forbid writing more data.
			self.requests.insert(*id, HttpApiRequest::Dispatched(None));
		}

		let mut deadline = timestamp::deadline_to_future(deadline);

		loop {
			// Within that loop, first try to see if we have all the elements for a response.
			// This includes the situation where the deadline is reached.
			{
				let mut output = Vec::with_capacity(ids.len());
				let mut must_wait_more = false;
				for id in ids {
					output.push(match self.requests.get(id) {
						None => HttpRequestStatus::Invalid,
						Some(HttpApiRequest::NotDispatched(_, _)) => unreachable!(
							"we replaced all the NotDispatched with Dispatched earlier; qed"
						),
						Some(HttpApiRequest::Dispatched(_)) => {
							must_wait_more = true;
							HttpRequestStatus::DeadlineReached
						},
						Some(HttpApiRequest::Fail(_)) => HttpRequestStatus::IoError,
						Some(HttpApiRequest::Response(HttpApiRequestRp {
							status_code, ..
						})) => HttpRequestStatus::Finished(status_code.as_u16()),
					});
				}
				debug_assert_eq!(output.len(), ids.len());

				// Are we ready to call `return`?
				let is_done =
					if let future::MaybeDone::Done(_) = deadline { true } else { !must_wait_more };

				if is_done {
					// Requests in "fail" mode are purged before returning.
					debug_assert_eq!(output.len(), ids.len());
					for n in (0..ids.len()).rev() {
						if let HttpRequestStatus::IoError = output[n] {
							self.requests.remove(&ids[n]);
						}
					}
					return output
				}
			}

			// Grab next message from the worker. We call `continue` if deadline is reached so that
			// we loop back and `return`.
			let next_message = {
				let mut next_msg = future::maybe_done(self.from_worker.next());
				futures::executor::block_on(future::select(&mut next_msg, &mut deadline));
				if let future::MaybeDone::Done(msg) = next_msg {
					msg
				} else {
					debug_assert!(matches!(deadline, future::MaybeDone::Done(..)));
					continue
				}
			};

			// Update internal state based on received message.
			match next_message {
				Some(WorkerToApi::Response { id, status_code, headers, body }) => {
					match self.requests.remove(&id) {
						Some(HttpApiRequest::Dispatched(sending_body)) => {
							self.requests.insert(
								id,
								HttpApiRequest::Response(HttpApiRequestRp {
									sending_body,
									status_code,
									headers,
									body: body.fuse(),
									current_read_chunk: None,
								}),
							);
						},
						None => {}, // can happen if we detected an IO error when sending the body
						_ => error!("State mismatch between the API and worker"),
					}
				},

				Some(WorkerToApi::Fail { id, error }) => match self.requests.remove(&id) {
					Some(HttpApiRequest::Dispatched(_)) => {
						self.requests.insert(id, HttpApiRequest::Fail(error));
					},
					None => {}, // can happen if we detected an IO error when sending the body
					_ => error!("State mismatch between the API and worker"),
				},

				None => {
					error!("Worker has crashed");
					return ids.iter().map(|_| HttpRequestStatus::IoError).collect()
				},
			}
		}
	}

	/// Mimics the corresponding method in the offchain API.
	pub fn response_headers(&mut self, request_id: HttpRequestId) -> Vec<(Vec<u8>, Vec<u8>)> {
		// Do an implicit non-blocking wait on the request.
		let _ = self.response_wait(&[request_id], Some(timestamp::now()));

		let headers = match self.requests.get(&request_id) {
			Some(HttpApiRequest::Response(HttpApiRequestRp { headers, .. })) => headers,
			_ => return Vec::new(),
		};

		headers
			.iter()
			.map(|(name, value)| (name.as_str().as_bytes().to_owned(), value.as_bytes().to_owned()))
			.collect()
	}

	/// Mimics the corresponding method in the offchain API.
	pub fn response_read_body(
		&mut self,
		request_id: HttpRequestId,
		buffer: &mut [u8],
		deadline: Option<Timestamp>,
	) -> Result<usize, HttpError> {
		// Do an implicit wait on the request.
		let _ = self.response_wait(&[request_id], deadline);

		// Remove the request from the list and handle situations where the request is invalid or
		// in the wrong state.
		let mut response = match self.requests.remove(&request_id) {
			Some(HttpApiRequest::Response(r)) => r,
			// Because we called `response_wait` above, we know that the deadline has been reached
			// and we still haven't received a response.
			Some(rq @ HttpApiRequest::Dispatched(_)) => {
				self.requests.insert(request_id, rq);
				return Err(HttpError::DeadlineReached)
			},
			// The request has failed.
			Some(HttpApiRequest::Fail { .. }) => return Err(HttpError::IoError),
			// Request hasn't been dispatched yet; reading the body is invalid.
			Some(rq @ HttpApiRequest::NotDispatched(_, _)) => {
				self.requests.insert(request_id, rq);
				return Err(HttpError::Invalid)
			},
			None => return Err(HttpError::Invalid),
		};

		// Convert the deadline into a `Future` that resolves when the deadline is reached.
		let mut deadline = timestamp::deadline_to_future(deadline);

		loop {
			// First read from `current_read_chunk`.
			if let Some(mut current_read_chunk) = response.current_read_chunk.take() {
				match current_read_chunk.read(buffer) {
					Ok(0) => {},
					Ok(n) => {
						self.requests.insert(
							request_id,
							HttpApiRequest::Response(HttpApiRequestRp {
								current_read_chunk: Some(current_read_chunk),
								..response
							}),
						);
						return Ok(n)
					},
					Err(err) => {
						// This code should never be reached unless there's a logic error somewhere.
						error!("Failed to read from current read chunk: {:?}", err);
						return Err(HttpError::IoError)
					},
				}
			}

			// If we reach here, that means the `current_read_chunk` is empty and needs to be
			// filled with a new chunk from `body`. We block on either the next body or the
			// deadline.
			let mut next_body = future::maybe_done(response.body.next());
			futures::executor::block_on(future::select(&mut next_body, &mut deadline));

			if let future::MaybeDone::Done(next_body) = next_body {
				match next_body {
					Some(Ok(chunk)) => response.current_read_chunk = Some(chunk.reader()),
					Some(Err(_)) => return Err(HttpError::IoError),
					None => return Ok(0), // eof
				}
			}

			if let future::MaybeDone::Done(_) = deadline {
				self.requests.insert(request_id, HttpApiRequest::Response(response));
				return Err(HttpError::DeadlineReached)
			}
		}
	}
}

impl fmt::Debug for HttpApi {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.debug_list().entries(self.requests.iter()).finish()
	}
}

impl fmt::Debug for HttpApiRequest {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			HttpApiRequest::NotDispatched(_, _) =>
				f.debug_tuple("HttpApiRequest::NotDispatched").finish(),
			HttpApiRequest::Dispatched(_) => f.debug_tuple("HttpApiRequest::Dispatched").finish(),
			HttpApiRequest::Response(HttpApiRequestRp { status_code, headers, .. }) => f
				.debug_tuple("HttpApiRequest::Response")
				.field(status_code)
				.field(headers)
				.finish(),
			HttpApiRequest::Fail(err) => f.debug_tuple("HttpApiRequest::Fail").field(err).finish(),
		}
	}
}

/// Message send from the API to the worker.
enum ApiToWorker {
	/// Dispatches a new HTTP request.
	Dispatch {
		/// ID to send back when the response comes back.
		id: HttpRequestId,
		/// Request to start executing.
		request: hyper::Request<hyper::Body>,
	},
}

/// Message send from the API to the worker.
enum WorkerToApi {
	/// A request has succeeded.
	Response {
		/// The ID that was passed to the worker.
		id: HttpRequestId,
		/// Status code of the response.
		status_code: hyper::StatusCode,
		/// Headers of the response.
		headers: hyper::HeaderMap,
		/// Body of the response, as a channel of `Chunk` objects.
		/// We send the body back through a channel instead of returning the hyper `Body` object
		/// because we don't want the `HttpApi` to have to drive the reading.
		/// Instead, reading an item from the channel will notify the worker task, which will push
		/// the next item.
		/// Can also be used to send an error, in case an error happend on the HTTP socket. After
		/// an error is sent, the channel will close.
		body: mpsc::Receiver<Result<hyper::body::Bytes, hyper::Error>>,
	},
	/// A request has failed because of an error. The request is then no longer valid.
	Fail {
		/// The ID that was passed to the worker.
		id: HttpRequestId,
		/// Error that happened.
		error: hyper::Error,
	},
}

/// Must be continuously polled for the [`HttpApi`] to properly work.
pub struct HttpWorker {
	/// Used to sends messages to the `HttpApi`.
	to_api: TracingUnboundedSender<WorkerToApi>,
	/// Used to receive messages from the `HttpApi`.
	from_api: TracingUnboundedReceiver<ApiToWorker>,
	/// The engine that runs HTTP requests.
	http_client: Arc<HyperClient<HttpsConnector<client::HttpConnector>, Body>>,
	/// HTTP requests that are being worked on by the engine.
	requests: Vec<(HttpRequestId, HttpWorkerRequest)>,
}

/// HTTP request being processed by the worker.
enum HttpWorkerRequest {
	/// Request has been dispatched and is waiting for a response from the Internet.
	Dispatched(hyper::client::ResponseFuture),
	/// Progressively reading the body of the response and sending it to the channel.
	ReadBody {
		/// Body to read `Chunk`s from. Only used if the channel is ready to accept data.
		body: hyper::Body,
		/// Channel to the [`HttpApi`] where we send the chunks to.
		tx: mpsc::Sender<Result<hyper::body::Bytes, hyper::Error>>,
	},
}

impl Future for HttpWorker {
	type Output = ();

	fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		// Reminder: this is continuously run in the background.

		// We use a `me` variable because the compiler isn't smart enough to allow borrowing
		// multiple fields at once through a `Deref`.
		let me = &mut *self;

		// We remove each element from `requests` one by one and add them back only if necessary.
		for n in (0..me.requests.len()).rev() {
			let (id, request) = me.requests.swap_remove(n);
			match request {
				HttpWorkerRequest::Dispatched(mut future) => {
					// Check for an HTTP response from the Internet.
					let response = match Future::poll(Pin::new(&mut future), cx) {
						Poll::Pending => {
							me.requests.push((id, HttpWorkerRequest::Dispatched(future)));
							continue
						},
						Poll::Ready(Ok(response)) => response,
						Poll::Ready(Err(error)) => {
							let _ = me.to_api.unbounded_send(WorkerToApi::Fail { id, error });
							continue // don't insert the request back
						},
					};

					// We received a response! Decompose it into its parts.
					let (head, body) = response.into_parts();
					let (status_code, headers) = (head.status, head.headers);

					let (body_tx, body_rx) = mpsc::channel(3);
					let _ = me.to_api.unbounded_send(WorkerToApi::Response {
						id,
						status_code,
						headers,
						body: body_rx,
					});

					me.requests.push((id, HttpWorkerRequest::ReadBody { body, tx: body_tx }));
					cx.waker().wake_by_ref(); // reschedule in order to poll the new future
					continue
				},

				HttpWorkerRequest::ReadBody { mut body, mut tx } => {
					// Before reading from the HTTP response, check that `tx` is ready to accept
					// a new chunk.
					match tx.poll_ready(cx) {
						Poll::Ready(Ok(())) => {},
						Poll::Ready(Err(_)) => continue, // don't insert the request back
						Poll::Pending => {
							me.requests.push((id, HttpWorkerRequest::ReadBody { body, tx }));
							continue
						},
					}

					// `tx` is ready. Read a chunk from the socket and send it to the channel.
					match Stream::poll_next(Pin::new(&mut body), cx) {
						Poll::Ready(Some(Ok(chunk))) => {
							let _ = tx.start_send(Ok(chunk));
							me.requests.push((id, HttpWorkerRequest::ReadBody { body, tx }));
							cx.waker().wake_by_ref(); // reschedule in order to continue reading
						},
						Poll::Ready(Some(Err(err))) => {
							let _ = tx.start_send(Err(err));
							// don't insert the request back
						},
						Poll::Ready(None) => {}, // EOF; don't insert the request back
						Poll::Pending => {
							me.requests.push((id, HttpWorkerRequest::ReadBody { body, tx }));
						},
					}
				},
			}
		}

		// Check for messages coming from the [`HttpApi`].
		match Stream::poll_next(Pin::new(&mut me.from_api), cx) {
			Poll::Pending => {},
			Poll::Ready(None) => return Poll::Ready(()), // stops the worker
			Poll::Ready(Some(ApiToWorker::Dispatch { id, request })) => {
				let future = me.http_client.request(request);
				debug_assert!(me.requests.iter().all(|(i, _)| *i != id));
				me.requests.push((id, HttpWorkerRequest::Dispatched(future)));
				cx.waker().wake_by_ref(); // reschedule the task to poll the request
			},
		}

		Poll::Pending
	}
}

impl fmt::Debug for HttpWorker {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.debug_list().entries(self.requests.iter()).finish()
	}
}

impl fmt::Debug for HttpWorkerRequest {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			HttpWorkerRequest::Dispatched(_) =>
				f.debug_tuple("HttpWorkerRequest::Dispatched").finish(),
			HttpWorkerRequest::ReadBody { .. } =>
				f.debug_tuple("HttpWorkerRequest::Response").finish(),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::{http, SharedClient};
	use crate::api::timestamp;
	use core::convert::Infallible;
	use futures::future;
	use lazy_static::lazy_static;
	use sp_core::offchain::{Duration, HttpError, HttpRequestId, HttpRequestStatus};

	// Using lazy_static to avoid spawning lots of different SharedClients,
	// as spawning a SharedClient is CPU-intensive and opens lots of fds.
	lazy_static! {
		static ref SHARED_CLIENT: SharedClient = SharedClient::new();
	}

	// Returns an `HttpApi` whose worker is ran in the background, and a `SocketAddr` to an HTTP
	// server that runs in the background as well.
	macro_rules! build_api_server {
		() => {{
			let hyper_client = SHARED_CLIENT.clone();
			let (api, worker) = http(hyper_client.clone());

			let (addr_tx, addr_rx) = std::sync::mpsc::channel();
			std::thread::spawn(move || {
				let rt = tokio::runtime::Runtime::new().unwrap();
				let worker = rt.spawn(worker);
				let server = rt.spawn(async move {
					let server = hyper::Server::bind(&"127.0.0.1:0".parse().unwrap()).serve(
						hyper::service::make_service_fn(|_| async move {
							Ok::<_, Infallible>(hyper::service::service_fn(
								move |_req| async move {
									Ok::<_, Infallible>(hyper::Response::new(hyper::Body::from(
										"Hello World!",
									)))
								},
							))
						}),
					);
					let _ = addr_tx.send(server.local_addr());
					server.await.map_err(drop)
				});
				let _ = rt.block_on(future::join(worker, server));
			});
			(api, addr_rx.recv().unwrap())
		}};
	}

	#[test]
	fn basic_localhost() {
		let deadline = timestamp::now().add(Duration::from_millis(10_000));

		// Performs an HTTP query to a background HTTP server.

		let (mut api, addr) = build_api_server!();

		let id = api.request_start("POST", &format!("http://{}", addr)).unwrap();
		api.request_write_body(id, &[], Some(deadline)).unwrap();

		match api.response_wait(&[id], Some(deadline))[0] {
			HttpRequestStatus::Finished(200) => {},
			v => panic!("Connecting to localhost failed: {:?}", v),
		}

		let headers = api.response_headers(id);
		assert!(headers.iter().any(|(h, _)| h.eq_ignore_ascii_case(b"Date")));

		let mut buf = vec![0; 2048];
		let n = api.response_read_body(id, &mut buf, Some(deadline)).unwrap();
		assert_eq!(&buf[..n], b"Hello World!");
	}

	#[test]
	fn request_start_invalid_call() {
		let (mut api, addr) = build_api_server!();

		match api.request_start("\0", &format!("http://{}", addr)) {
			Err(()) => {},
			Ok(_) => panic!(),
		};

		match api.request_start("GET", "http://\0localhost") {
			Err(()) => {},
			Ok(_) => panic!(),
		};
	}

	#[test]
	fn request_add_header_invalid_call() {
		let (mut api, addr) = build_api_server!();

		match api.request_add_header(HttpRequestId(0xdead), "Foo", "bar") {
			Err(()) => {},
			Ok(_) => panic!(),
		};

		let id = api.request_start("GET", &format!("http://{}", addr)).unwrap();
		match api.request_add_header(id, "\0", "bar") {
			Err(()) => {},
			Ok(_) => panic!(),
		};

		let id = api.request_start("POST", &format!("http://{}", addr)).unwrap();
		match api.request_add_header(id, "Foo", "\0") {
			Err(()) => {},
			Ok(_) => panic!(),
		};

		let id = api.request_start("POST", &format!("http://{}", addr)).unwrap();
		api.request_add_header(id, "Foo", "Bar").unwrap();
		api.request_write_body(id, &[1, 2, 3, 4], None).unwrap();
		match api.request_add_header(id, "Foo2", "Bar") {
			Err(()) => {},
			Ok(_) => panic!(),
		};

		let id = api.request_start("GET", &format!("http://{}", addr)).unwrap();
		api.response_headers(id);
		match api.request_add_header(id, "Foo2", "Bar") {
			Err(()) => {},
			Ok(_) => panic!(),
		};

		let id = api.request_start("GET", &format!("http://{}", addr)).unwrap();
		api.response_read_body(id, &mut [], None).unwrap();
		match api.request_add_header(id, "Foo2", "Bar") {
			Err(()) => {},
			Ok(_) => panic!(),
		};
	}

	#[test]
	fn request_write_body_invalid_call() {
		let (mut api, addr) = build_api_server!();

		match api.request_write_body(HttpRequestId(0xdead), &[1, 2, 3], None) {
			Err(HttpError::Invalid) => {},
			_ => panic!(),
		};

		match api.request_write_body(HttpRequestId(0xdead), &[], None) {
			Err(HttpError::Invalid) => {},
			_ => panic!(),
		};

		let id = api.request_start("POST", &format!("http://{}", addr)).unwrap();
		api.request_write_body(id, &[1, 2, 3, 4], None).unwrap();
		api.request_write_body(id, &[1, 2, 3, 4], None).unwrap();
		api.request_write_body(id, &[], None).unwrap();
		match api.request_write_body(id, &[], None) {
			Err(HttpError::Invalid) => {},
			_ => panic!(),
		};

		let id = api.request_start("POST", &format!("http://{}", addr)).unwrap();
		api.request_write_body(id, &[1, 2, 3, 4], None).unwrap();
		api.request_write_body(id, &[1, 2, 3, 4], None).unwrap();
		api.request_write_body(id, &[], None).unwrap();
		match api.request_write_body(id, &[1, 2, 3, 4], None) {
			Err(HttpError::Invalid) => {},
			_ => panic!(),
		};

		let id = api.request_start("POST", &format!("http://{}", addr)).unwrap();
		api.request_write_body(id, &[1, 2, 3, 4], None).unwrap();
		api.response_wait(&[id], None);
		match api.request_write_body(id, &[], None) {
			Err(HttpError::Invalid) => {},
			_ => panic!(),
		};

		let id = api.request_start("POST", &format!("http://{}", addr)).unwrap();
		api.request_write_body(id, &[1, 2, 3, 4], None).unwrap();
		api.response_wait(&[id], None);
		match api.request_write_body(id, &[1, 2, 3, 4], None) {
			Err(HttpError::Invalid) => {},
			_ => panic!(),
		};

		let id = api.request_start("POST", &format!("http://{}", addr)).unwrap();
		api.response_headers(id);
		match api.request_write_body(id, &[1, 2, 3, 4], None) {
			Err(HttpError::Invalid) => {},
			_ => panic!(),
		};

		let id = api.request_start("GET", &format!("http://{}", addr)).unwrap();
		api.response_headers(id);
		match api.request_write_body(id, &[], None) {
			Err(HttpError::Invalid) => {},
			_ => panic!(),
		};

		let id = api.request_start("POST", &format!("http://{}", addr)).unwrap();
		api.response_read_body(id, &mut [], None).unwrap();
		match api.request_write_body(id, &[1, 2, 3, 4], None) {
			Err(HttpError::Invalid) => {},
			_ => panic!(),
		};

		let id = api.request_start("POST", &format!("http://{}", addr)).unwrap();
		api.response_read_body(id, &mut [], None).unwrap();
		match api.request_write_body(id, &[], None) {
			Err(HttpError::Invalid) => {},
			_ => panic!(),
		};
	}

	#[test]
	fn response_headers_invalid_call() {
		let (mut api, addr) = build_api_server!();
		assert_eq!(api.response_headers(HttpRequestId(0xdead)), &[]);

		let id = api.request_start("POST", &format!("http://{}", addr)).unwrap();
		assert_eq!(api.response_headers(id), &[]);

		let id = api.request_start("POST", &format!("http://{}", addr)).unwrap();
		api.request_write_body(id, &[], None).unwrap();
		while api.response_headers(id).is_empty() {
			std::thread::sleep(std::time::Duration::from_millis(100));
		}

		let id = api.request_start("GET", &format!("http://{}", addr)).unwrap();
		api.response_wait(&[id], None);
		assert_ne!(api.response_headers(id), &[]);

		let id = api.request_start("GET", &format!("http://{}", addr)).unwrap();
		let mut buf = [0; 128];
		while api.response_read_body(id, &mut buf, None).unwrap() != 0 {}
		assert_eq!(api.response_headers(id), &[]);
	}

	#[test]
	fn response_header_invalid_call() {
		let (mut api, addr) = build_api_server!();

		let id = api.request_start("POST", &format!("http://{}", addr)).unwrap();
		assert_eq!(api.response_headers(id), &[]);

		let id = api.request_start("POST", &format!("http://{}", addr)).unwrap();
		api.request_add_header(id, "Foo", "Bar").unwrap();
		assert_eq!(api.response_headers(id), &[]);

		let id = api.request_start("GET", &format!("http://{}", addr)).unwrap();
		api.request_add_header(id, "Foo", "Bar").unwrap();
		api.request_write_body(id, &[], None).unwrap();
		// Note: this test actually sends out the request, and is supposed to test a situation
		// where we haven't received any response yet. This test can theoretically fail if the
		// HTTP response comes back faster than the kernel schedules our thread, but that is highly
		// unlikely.
		assert_eq!(api.response_headers(id), &[]);
	}

	#[test]
	fn response_read_body_invalid_call() {
		let (mut api, addr) = build_api_server!();
		let mut buf = [0; 512];

		match api.response_read_body(HttpRequestId(0xdead), &mut buf, None) {
			Err(HttpError::Invalid) => {},
			_ => panic!(),
		}

		let id = api.request_start("GET", &format!("http://{}", addr)).unwrap();
		while api.response_read_body(id, &mut buf, None).unwrap() != 0 {}
		match api.response_read_body(id, &mut buf, None) {
			Err(HttpError::Invalid) => {},
			_ => panic!(),
		}
	}

	#[test]
	fn fuzzing() {
		// Uses the API in random ways to try to trigger panics.
		// Doesn't test some paths, such as waiting for multiple requests. Also doesn't test what
		// happens if the server force-closes our socket.

		let (mut api, addr) = build_api_server!();

		for _ in 0..50 {
			let id = api.request_start("POST", &format!("http://{}", addr)).unwrap();

			for _ in 0..250 {
				match rand::random::<u8>() % 6 {
					0 => {
						let _ = api.request_add_header(id, "Foo", "Bar");
					},
					1 => {
						let _ = api.request_write_body(id, &[1, 2, 3, 4], None);
					},
					2 => {
						let _ = api.request_write_body(id, &[], None);
					},
					3 => {
						let _ = api.response_wait(&[id], None);
					},
					4 => {
						let _ = api.response_headers(id);
					},
					5 => {
						let mut buf = [0; 512];
						let _ = api.response_read_body(id, &mut buf, None);
					},
					6..=255 => unreachable!(),
				}
			}
		}
	}
}
