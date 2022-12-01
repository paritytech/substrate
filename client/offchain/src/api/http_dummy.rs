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

//! Contains the same API as the `http` module, except that everything returns an error.

use sp_core::offchain::{HttpError, HttpRequestId, HttpRequestStatus, Timestamp};
use std::{
	future::Future,
	pin::Pin,
	task::{Context, Poll},
};

/// Wrapper struct (wrapping nothing in case of http_dummy) used for keeping the hyper_rustls client running.
#[derive(Clone)]
pub struct SharedClient;

impl SharedClient {
	pub fn new() -> Self {
		Self
	}
}

/// Creates a pair of [`HttpApi`] and [`HttpWorker`].
pub fn http(_: SharedClient) -> (HttpApi, HttpWorker) {
	(HttpApi, HttpWorker)
}

/// Dummy implementation of HTTP capabilities.
#[derive(Debug)]
pub struct HttpApi;

/// Dummy implementation of HTTP capabilities.
#[derive(Debug)]
pub struct HttpWorker;

impl HttpApi {
	/// Mimics the corresponding method in the offchain API.
	pub fn request_start(&mut self, _: &str, _: &str) -> Result<HttpRequestId, ()> {
		/// Because this always returns an error, none of the other methods should ever be called.
		Err(())
	}

	/// Mimics the corresponding method in the offchain API.
	pub fn request_add_header(&mut self, _: HttpRequestId, _: &str, _: &str) -> Result<(), ()> {
		unreachable!(
			"Creating a request always fails, thus this function will \
			never be called; qed"
		)
	}

	/// Mimics the corresponding method in the offchain API.
	pub fn request_write_body(
		&mut self,
		_: HttpRequestId,
		_: &[u8],
		_: Option<Timestamp>,
	) -> Result<(), HttpError> {
		unreachable!(
			"Creating a request always fails, thus this function will \
			never be called; qed"
		)
	}

	/// Mimics the corresponding method in the offchain API.
	pub fn response_wait(
		&mut self,
		requests: &[HttpRequestId],
		_: Option<Timestamp>,
	) -> Vec<HttpRequestStatus> {
		if requests.is_empty() {
			Vec::new()
		} else {
			unreachable!(
				"Creating a request always fails, thus the list of requests should \
				always be empty; qed"
			)
		}
	}

	/// Mimics the corresponding method in the offchain API.
	pub fn response_headers(&mut self, _: HttpRequestId) -> Vec<(Vec<u8>, Vec<u8>)> {
		unreachable!(
			"Creating a request always fails, thus this function will \
			never be called; qed"
		)
	}

	/// Mimics the corresponding method in the offchain API.
	pub fn response_read_body(
		&mut self,
		_: HttpRequestId,
		_: &mut [u8],
		_: Option<Timestamp>,
	) -> Result<usize, HttpError> {
		unreachable!(
			"Creating a request always fails, thus this function will \
			never be called; qed"
		)
	}
}

impl Future for HttpWorker {
	type Output = ();

	fn poll(self: Pin<&mut Self>, _: &mut Context) -> Poll<Self::Output> {
		Poll::Ready(())
	}
}
