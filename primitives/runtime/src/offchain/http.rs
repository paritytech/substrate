// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! A high-level helpers for making HTTP requests from Offchain Workers.
//!
//! `sp-io` crate exposes a low level methods to make and control HTTP requests
//! available only for Offchain Workers. Those might be hard to use
//! and usually that level of control is not really necessary.
//! This module aims to provide high-level wrappers for those APIs
//! to simplify making HTTP requests.
//!
//!
//! Example:
//! ```rust,no_run
//! use sp_runtime::offchain::http::Request;
//!
//! // initiate a GET request to localhost:1234
//! let request: Request = Request::get("http://localhost:1234");
//! let pending = request
//! 	.add_header("X-Auth", "hunter2")
//! 	.send()
//! 	.unwrap();
//!
//! // wait for the response indefinitely
//! let mut response = pending.wait().unwrap();
//!
//! // then check the headers
//! let mut headers = response.headers().into_iter();
//! assert_eq!(headers.current(), None);
//!
//! // and collect the body
//! let body = response.body();
//! assert_eq!(body.clone().collect::<Vec<_>>(), b"1234".to_vec());
//! assert_eq!(body.error(), &None);
//! ```

use sp_core::{
	offchain::{
		HttpError, HttpRequestId as RequestId, HttpRequestStatus as RequestStatus, Timestamp,
	},
	RuntimeDebug,
};
#[cfg(not(feature = "std"))]
use sp_std::prelude::vec;
use sp_std::{prelude::Vec, str};

/// Request method (HTTP verb)
#[derive(Clone, PartialEq, Eq, RuntimeDebug)]
pub enum Method {
	/// GET request
	Get,
	/// POST request
	Post,
	/// PUT request
	Put,
	/// PATCH request
	Patch,
	/// DELETE request
	Delete,
	/// Custom verb
	Other(&'static str),
}

impl AsRef<str> for Method {
	fn as_ref(&self) -> &str {
		match *self {
			Method::Get => "GET",
			Method::Post => "POST",
			Method::Put => "PUT",
			Method::Patch => "PATCH",
			Method::Delete => "DELETE",
			Method::Other(m) => m,
		}
	}
}

mod header {
	use super::*;

	/// A header type.
	#[derive(Clone, PartialEq, Eq, RuntimeDebug)]
	pub struct Header {
		name: Vec<u8>,
		value: Vec<u8>,
	}

	impl Header {
		/// Creates new header given it's name and value.
		pub fn new(name: &str, value: &str) -> Self {
			Header { name: name.as_bytes().to_vec(), value: value.as_bytes().to_vec() }
		}

		/// Returns the name of this header.
		pub fn name(&self) -> &str {
			// Header keys are always produced from `&str` so this is safe.
			// we don't store them as `Strings` to avoid bringing `alloc::String` to sp-std
			// or here.
			unsafe { str::from_utf8_unchecked(&self.name) }
		}

		/// Returns the value of this header.
		pub fn value(&self) -> &str {
			// Header values are always produced from `&str` so this is safe.
			// we don't store them as `Strings` to avoid bringing `alloc::String` to sp-std
			// or here.
			unsafe { str::from_utf8_unchecked(&self.value) }
		}
	}
}

/// An HTTP request builder.
#[derive(Clone, PartialEq, Eq, RuntimeDebug)]
pub struct Request<'a, T = Vec<&'static [u8]>> {
	/// Request method
	pub method: Method,
	/// Request URL
	pub url: &'a str,
	/// Body of the request
	pub body: T,
	/// Deadline to finish sending the request
	pub deadline: Option<Timestamp>,
	/// Request list of headers.
	headers: Vec<header::Header>,
}

impl<T: Default> Default for Request<'static, T> {
	fn default() -> Self {
		Request {
			method: Method::Get,
			url: "http://localhost",
			headers: Vec::new(),
			body: Default::default(),
			deadline: None,
		}
	}
}

impl<'a> Request<'a> {
	/// Start a simple GET request
	pub fn get(url: &'a str) -> Self {
		Self::new(url)
	}
}

impl<'a, T> Request<'a, T> {
	/// Create new POST request with given body.
	pub fn post(url: &'a str, body: T) -> Self {
		let req: Request = Request::default();

		Request { url, body, method: Method::Post, headers: req.headers, deadline: req.deadline }
	}
}

impl<'a, T: Default> Request<'a, T> {
	/// Create a new Request builder with the given URL.
	pub fn new(url: &'a str) -> Self {
		Request::default().url(url)
	}

	/// Change the method of the request
	pub fn method(mut self, method: Method) -> Self {
		self.method = method;
		self
	}

	/// Change the URL of the request.
	pub fn url(mut self, url: &'a str) -> Self {
		self.url = url;
		self
	}

	/// Set the body of the request.
	pub fn body(mut self, body: T) -> Self {
		self.body = body;
		self
	}

	/// Add a header.
	pub fn add_header(mut self, name: &str, value: &str) -> Self {
		self.headers.push(header::Header::new(name, value));
		self
	}

	/// Set the deadline of the request.
	pub fn deadline(mut self, deadline: Timestamp) -> Self {
		self.deadline = Some(deadline);
		self
	}
}

impl<'a, I: AsRef<[u8]>, T: IntoIterator<Item = I>> Request<'a, T> {
	/// Send the request and return a handle.
	///
	/// Err is returned in case the deadline is reached
	/// or the request timeouts.
	pub fn send(self) -> Result<PendingRequest, HttpError> {
		let meta = &[];

		// start an http request.
		let id = sp_io::offchain::http_request_start(self.method.as_ref(), self.url, meta)
			.map_err(|_| HttpError::IoError)?;

		// add custom headers
		for header in &self.headers {
			sp_io::offchain::http_request_add_header(id, header.name(), header.value())
				.map_err(|_| HttpError::IoError)?
		}

		// write body
		for chunk in self.body {
			sp_io::offchain::http_request_write_body(id, chunk.as_ref(), self.deadline)?;
		}

		// finalize the request
		sp_io::offchain::http_request_write_body(id, &[], self.deadline)?;

		Ok(PendingRequest { id })
	}
}

/// A request error
#[derive(Clone, PartialEq, Eq, RuntimeDebug)]
pub enum Error {
	/// Deadline has been reached.
	DeadlineReached,
	/// Request had timed out.
	IoError,
	/// Unknown error has been encountered.
	Unknown,
}

/// A struct representing an uncompleted http request.
#[derive(PartialEq, Eq, RuntimeDebug)]
pub struct PendingRequest {
	/// Request ID
	pub id: RequestId,
}

/// A result of waiting for a pending request.
pub type HttpResult = Result<Response, Error>;

impl PendingRequest {
	/// Wait for the request to complete.
	///
	/// NOTE this waits for the request indefinitely.
	pub fn wait(self) -> HttpResult {
		match self.try_wait(None) {
			Ok(res) => res,
			Err(_) => panic!("Since `None` is passed we will never get a deadline error; qed"),
		}
	}

	/// Attempts to wait for the request to finish,
	/// but will return `Err` in case the deadline is reached.
	pub fn try_wait(
		self,
		deadline: impl Into<Option<Timestamp>>,
	) -> Result<HttpResult, PendingRequest> {
		Self::try_wait_all(vec![self], deadline)
			.pop()
			.expect("One request passed, one status received; qed")
	}

	/// Wait for all provided requests.
	pub fn wait_all(requests: Vec<PendingRequest>) -> Vec<HttpResult> {
		Self::try_wait_all(requests, None)
			.into_iter()
			.map(|r| match r {
				Ok(r) => r,
				Err(_) => panic!("Since `None` is passed we will never get a deadline error; qed"),
			})
			.collect()
	}

	/// Attempt to wait for all provided requests, but up to given deadline.
	///
	/// Requests that are complete will resolve to an `Ok` others will return a `DeadlineReached`
	/// error.
	pub fn try_wait_all(
		requests: Vec<PendingRequest>,
		deadline: impl Into<Option<Timestamp>>,
	) -> Vec<Result<HttpResult, PendingRequest>> {
		let ids = requests.iter().map(|r| r.id).collect::<Vec<_>>();
		let statuses = sp_io::offchain::http_response_wait(&ids, deadline.into());

		statuses
			.into_iter()
			.zip(requests.into_iter())
			.map(|(status, req)| match status {
				RequestStatus::DeadlineReached => Err(req),
				RequestStatus::IoError => Ok(Err(Error::IoError)),
				RequestStatus::Invalid => Ok(Err(Error::Unknown)),
				RequestStatus::Finished(code) => Ok(Ok(Response::new(req.id, code))),
			})
			.collect()
	}
}

/// A HTTP response.
#[derive(RuntimeDebug)]
pub struct Response {
	/// Request id
	pub id: RequestId,
	/// Response status code
	pub code: u16,
	/// A collection of headers.
	headers: Option<Headers>,
}

impl Response {
	fn new(id: RequestId, code: u16) -> Self {
		Self { id, code, headers: None }
	}

	/// Retrieve the headers for this response.
	pub fn headers(&mut self) -> &Headers {
		if self.headers.is_none() {
			self.headers = Some(Headers { raw: sp_io::offchain::http_response_headers(self.id) });
		}
		self.headers.as_ref().expect("Headers were just set; qed")
	}

	/// Retrieve the body of this response.
	pub fn body(&self) -> ResponseBody {
		ResponseBody::new(self.id)
	}
}

/// A buffered byte iterator over response body.
///
/// Note that reading the body may return `None` in following cases:
/// 1. Either the deadline you've set is reached (check via `#error`;
/// 	   In such case you can resume the reader by setting a new deadline)
/// 2. Or because of IOError. In such case the reader is not resumable and will keep
///    returning `None`.
/// 3. The body has been returned. The reader will keep returning `None`.
#[derive(Clone)]
pub struct ResponseBody {
	id: RequestId,
	error: Option<HttpError>,
	buffer: [u8; 4096],
	filled_up_to: Option<usize>,
	position: usize,
	deadline: Option<Timestamp>,
}

#[cfg(feature = "std")]
impl std::fmt::Debug for ResponseBody {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		fmt.debug_struct("ResponseBody")
			.field("id", &self.id)
			.field("error", &self.error)
			.field("buffer", &self.buffer.len())
			.field("filled_up_to", &self.filled_up_to)
			.field("position", &self.position)
			.field("deadline", &self.deadline)
			.finish()
	}
}

impl ResponseBody {
	fn new(id: RequestId) -> Self {
		ResponseBody {
			id,
			error: None,
			buffer: [0_u8; 4096],
			filled_up_to: None,
			position: 0,
			deadline: None,
		}
	}

	/// Set the deadline for reading the body.
	pub fn deadline(&mut self, deadline: impl Into<Option<Timestamp>>) {
		self.deadline = deadline.into();
		self.error = None;
	}

	/// Return an error that caused the iterator to return `None`.
	///
	/// If the error is `DeadlineReached` you can resume the iterator by setting
	/// a new deadline.
	pub fn error(&self) -> &Option<HttpError> {
		&self.error
	}
}

impl Iterator for ResponseBody {
	type Item = u8;

	fn next(&mut self) -> Option<Self::Item> {
		if self.error.is_some() {
			return None
		}

		if self.filled_up_to.is_none() {
			let result =
				sp_io::offchain::http_response_read_body(self.id, &mut self.buffer, self.deadline);
			match result {
				Err(e) => {
					self.error = Some(e);
					return None
				},
				Ok(0) => return None,
				Ok(size) => {
					self.position = 0;
					self.filled_up_to = Some(size as usize);
				},
			}
		}

		if Some(self.position) == self.filled_up_to {
			self.filled_up_to = None;
			return self.next()
		}

		let result = self.buffer[self.position];
		self.position += 1;
		Some(result)
	}
}

/// A collection of Headers in the response.
#[derive(Clone, PartialEq, Eq, RuntimeDebug)]
pub struct Headers {
	/// Raw headers
	pub raw: Vec<(Vec<u8>, Vec<u8>)>,
}

impl Headers {
	/// Retrieve a single header from the list of headers.
	///
	/// Note this method is linearly looking from all the headers
	/// comparing them with the needle byte-by-byte.
	/// If you want to consume multiple headers it's better to iterate
	/// and collect them on your own.
	pub fn find(&self, name: &str) -> Option<&str> {
		let raw = name.as_bytes();
		for &(ref key, ref val) in &self.raw {
			if &**key == raw {
				return str::from_utf8(&val).ok()
			}
		}
		None
	}

	/// Convert this headers into an iterator.
	pub fn into_iter(&self) -> HeadersIterator {
		HeadersIterator { collection: &self.raw, index: None }
	}
}

/// A custom iterator traversing all the headers.
#[derive(Clone, RuntimeDebug)]
pub struct HeadersIterator<'a> {
	collection: &'a [(Vec<u8>, Vec<u8>)],
	index: Option<usize>,
}

impl<'a> HeadersIterator<'a> {
	/// Move the iterator to the next position.
	///
	/// Returns `true` is `current` has been set by this call.
	pub fn next(&mut self) -> bool {
		let index = self.index.map(|x| x + 1).unwrap_or(0);
		self.index = Some(index);
		index < self.collection.len()
	}

	/// Returns current element (if any).
	///
	/// Note that you have to call `next` prior to calling this
	pub fn current(&self) -> Option<(&str, &str)> {
		self.collection
			.get(self.index?)
			.map(|val| (str::from_utf8(&val.0).unwrap_or(""), str::from_utf8(&val.1).unwrap_or("")))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_core::offchain::{testing, OffchainWorkerExt};
	use sp_io::TestExternalities;

	#[test]
	fn should_send_a_basic_request_and_get_response() {
		let (offchain, state) = testing::TestOffchainExt::new();
		let mut t = TestExternalities::default();
		t.register_extension(OffchainWorkerExt::new(offchain));

		t.execute_with(|| {
			let request: Request = Request::get("http://localhost:1234");
			let pending = request.add_header("X-Auth", "hunter2").send().unwrap();
			// make sure it's sent correctly
			state.write().fulfill_pending_request(
				0,
				testing::PendingRequest {
					method: "GET".into(),
					uri: "http://localhost:1234".into(),
					headers: vec![("X-Auth".into(), "hunter2".into())],
					sent: true,
					..Default::default()
				},
				b"1234".to_vec(),
				None,
			);

			// wait
			let mut response = pending.wait().unwrap();

			// then check the response
			let mut headers = response.headers().into_iter();
			assert_eq!(headers.current(), None);
			assert_eq!(headers.next(), false);
			assert_eq!(headers.current(), None);

			let body = response.body();
			assert_eq!(body.clone().collect::<Vec<_>>(), b"1234".to_vec());
			assert_eq!(body.error(), &None);
		})
	}

	#[test]
	fn should_send_huge_response() {
		let (offchain, state) = testing::TestOffchainExt::new();
		let mut t = TestExternalities::default();
		t.register_extension(OffchainWorkerExt::new(offchain));

		t.execute_with(|| {
			let request: Request = Request::get("http://localhost:1234");
			let pending = request.add_header("X-Auth", "hunter2").send().unwrap();
			// make sure it's sent correctly
			state.write().fulfill_pending_request(
				0,
				testing::PendingRequest {
					method: "GET".into(),
					uri: "http://localhost:1234".into(),
					headers: vec![("X-Auth".into(), "hunter2".into())],
					sent: true,
					..Default::default()
				},
				vec![0; 5923],
				None,
			);

			// wait
			let response = pending.wait().unwrap();

			let body = response.body();
			assert_eq!(body.clone().collect::<Vec<_>>(), vec![0; 5923]);
			assert_eq!(body.error(), &None);
		})
	}

	#[test]
	fn should_send_a_post_request() {
		let (offchain, state) = testing::TestOffchainExt::new();
		let mut t = TestExternalities::default();
		t.register_extension(OffchainWorkerExt::new(offchain));

		t.execute_with(|| {
			let pending = Request::default()
				.method(Method::Post)
				.url("http://localhost:1234")
				.body(vec![b"1234"])
				.send()
				.unwrap();
			// make sure it's sent correctly
			state.write().fulfill_pending_request(
				0,
				testing::PendingRequest {
					method: "POST".into(),
					uri: "http://localhost:1234".into(),
					body: b"1234".to_vec(),
					sent: true,
					..Default::default()
				},
				b"1234".to_vec(),
				Some(("Test".to_owned(), "Header".to_owned())),
			);

			// wait
			let mut response = pending.wait().unwrap();

			// then check the response
			let mut headers = response.headers().into_iter();
			assert_eq!(headers.current(), None);
			assert_eq!(headers.next(), true);
			assert_eq!(headers.current(), Some(("Test", "Header")));

			let body = response.body();
			assert_eq!(body.clone().collect::<Vec<_>>(), b"1234".to_vec());
			assert_eq!(body.error(), &None);
		})
	}
}
