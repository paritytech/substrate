// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Utilities for offchain calls testing.
//!
//! Namely all ExecutionExtensions that allow mocking
//! the extra APIs.

use std::{
	collections::BTreeMap,
	sync::Arc,
};
use crate::offchain::{
	self,
	storage::InMemOffchainStorage,
	HttpError,
	HttpRequestId as RequestId,
	HttpRequestStatus as RequestStatus,
	Timestamp,
	StorageKind,
	OpaqueNetworkState,
	TransactionPool,
	OffchainStorage,
};
use parking_lot::RwLock;

/// Pending request.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct PendingRequest {
	/// HTTP method
	pub method: String,
	/// URI
	pub uri: String,
	/// Encoded Metadata
	pub meta: Vec<u8>,
	/// Request headers
	pub headers: Vec<(String, String)>,
	/// Request body
	pub body: Vec<u8>,
	/// Has the request been sent already.
	pub sent: bool,
	/// Response body
	pub response: Option<Vec<u8>>,
	/// Number of bytes already read from the response body.
	pub read: usize,
	/// Response headers
	pub response_headers: Vec<(String, String)>,
}

/// Internal state of the externalities.
///
/// This can be used in tests to respond or assert stuff about interactions.
#[derive(Debug, Default)]
pub struct OffchainState {
	/// A list of pending requests.
	pub requests: BTreeMap<RequestId, PendingRequest>,
	expected_requests: BTreeMap<RequestId, PendingRequest>,
	/// Persistent local storage
	pub persistent_storage: InMemOffchainStorage,
	/// Local storage
	pub local_storage: InMemOffchainStorage,
	/// Current timestamp (unix millis)
	pub timestamp: u64,
	/// A supposedly random seed.
	pub seed: [u8; 32],
}

impl OffchainState {
	/// Asserts that pending request has been submitted and fills it's response.
	pub fn fulfill_pending_request(
		&mut self,
		id: u16,
		expected: PendingRequest,
		response: impl Into<Vec<u8>>,
		response_headers: impl IntoIterator<Item=(String, String)>,
	) {
		match self.requests.get_mut(&RequestId(id)) {
			None => {
				panic!("Missing pending request: {:?}.\n\nAll: {:?}", id, self.requests);
			}
			Some(req) => {
				assert_eq!(
					*req,
					expected,
				);
				req.response = Some(response.into());
				req.response_headers = response_headers.into_iter().collect();
			}
		}
	}

	fn fulfill_expected(&mut self, id: u16) {
		if let Some(mut req) = self.expected_requests.remove(&RequestId(id)) {
			let response = req.response.take().expect("Response checked while added.");
			let headers = std::mem::take(&mut req.response_headers);
			self.fulfill_pending_request(id, req, response, headers);
		}
	}

	/// Add expected HTTP request.
	///
	/// This method can be used to initialize expected HTTP requests and their responses
	/// before running the actual code that utilizes them (for instance before calling into runtime).
	/// Expected request has to be fulfilled before this struct is dropped,
	/// the `response` and `response_headers` fields will be used to return results to the callers.
	pub fn expect_request(&mut self, id: u16, expected: PendingRequest) {
		if expected.response.is_none() {
			panic!("Expected request needs to have a response.");
		}
		self.expected_requests.insert(RequestId(id), expected);
	}
}

impl Drop for OffchainState {
	fn drop(&mut self) {
		// If we panic! while we are already in a panic, the test dies with an illegal instruction.
		if !self.expected_requests.is_empty() && !std::thread::panicking() {
			panic!("Unfulfilled expected requests: {:?}", self.expected_requests);
		}
	}
}

/// Implementation of offchain externalities used for tests.
#[derive(Clone, Default, Debug)]
pub struct TestOffchainExt(pub Arc<RwLock<OffchainState>>);

impl TestOffchainExt {
	/// Create new `TestOffchainExt` and a reference to the internal state.
	pub fn new() -> (Self, Arc<RwLock<OffchainState>>) {
		let ext = Self::default();
		let state = ext.0.clone();
		(ext, state)
	}
}

impl offchain::Externalities for TestOffchainExt {
	fn is_validator(&self) -> bool {
		true
	}

	fn network_state(&self) -> Result<OpaqueNetworkState, ()> {
		Ok(OpaqueNetworkState {
			peer_id: Default::default(),
			external_addresses: vec![],
		})
	}

	fn timestamp(&mut self) -> Timestamp {
		Timestamp::from_unix_millis(self.0.read().timestamp)
	}

	fn sleep_until(&mut self, _deadline: Timestamp) {
		unimplemented!("not needed in tests so far")
	}

	fn random_seed(&mut self) -> [u8; 32] {
		self.0.read().seed
	}

	fn local_storage_set(&mut self, kind: StorageKind, key: &[u8], value: &[u8]) {
		let mut state = self.0.write();
		match kind {
			StorageKind::LOCAL => &mut state.local_storage,
			StorageKind::PERSISTENT => &mut state.persistent_storage,
		}.set(b"", key, value);
	}

	fn local_storage_compare_and_set(
		&mut self,
		kind: StorageKind,
		key: &[u8],
		old_value: Option<&[u8]>,
		new_value: &[u8]
	) -> bool {
		let mut state = self.0.write();
		match kind {
			StorageKind::LOCAL => &mut state.local_storage,
			StorageKind::PERSISTENT => &mut state.persistent_storage,
		}.compare_and_set(b"", key, old_value, new_value)
	}

	fn local_storage_get(&mut self, kind: StorageKind, key: &[u8]) -> Option<Vec<u8>> {
		let state = self.0.read();
		match kind {
			StorageKind::LOCAL => &state.local_storage,
			StorageKind::PERSISTENT => &state.persistent_storage,
		}.get(b"", key)
	}

	fn http_request_start(&mut self, method: &str, uri: &str, meta: &[u8]) -> Result<RequestId, ()> {
		let mut state = self.0.write();
		let id = RequestId(state.requests.len() as u16);
		state.requests.insert(id.clone(), PendingRequest {
			method: method.into(),
			uri: uri.into(),
			meta: meta.into(),
			..Default::default()
		});
		Ok(id)
	}

	fn http_request_add_header(
		&mut self,
		request_id: RequestId,
		name: &str,
		value: &str,
	) -> Result<(), ()> {
		let mut state = self.0.write();
		if let Some(req) = state.requests.get_mut(&request_id) {
			req.headers.push((name.into(), value.into()));
			Ok(())
		} else {
			Err(())
		}
	}

	fn http_request_write_body(
		&mut self,
		request_id: RequestId,
		chunk: &[u8],
		_deadline: Option<Timestamp>
	) -> Result<(), HttpError> {
		let mut state = self.0.write();

		let sent = {
			let req = state.requests.get_mut(&request_id).ok_or(HttpError::IoError)?;
			req.body.extend(chunk);
			if chunk.is_empty() {
				req.sent = true;
			}
			req.sent
		};

		if sent {
			state.fulfill_expected(request_id.0);
		}

		Ok(())
	}

	fn http_response_wait(
		&mut self,
		ids: &[RequestId],
		_deadline: Option<Timestamp>,
	) -> Vec<RequestStatus> {
		let state = self.0.read();

		ids.iter().map(|id| match state.requests.get(id) {
			Some(req) if req.response.is_none() =>
				panic!("No `response` provided for request with id: {:?}", id),
			None => RequestStatus::Invalid,
			_ => RequestStatus::Finished(200),
		}).collect()
	}

	fn http_response_headers(&mut self, request_id: RequestId) -> Vec<(Vec<u8>, Vec<u8>)> {
		let state = self.0.read();
		if let Some(req) = state.requests.get(&request_id) {
			req.response_headers
				.clone()
				.into_iter()
				.map(|(k, v)| (k.into_bytes(), v.into_bytes()))
				.collect()
		} else {
			Default::default()
		}
	}

	fn http_response_read_body(
		&mut self,
		request_id: RequestId,
		buffer: &mut [u8],
		_deadline: Option<Timestamp>
	) -> Result<usize, HttpError> {
		let mut state = self.0.write();
		if let Some(req) = state.requests.get_mut(&request_id) {
			let response = req.response
				.as_mut()
				.expect(&format!("No response provided for request: {:?}", request_id));

			if req.read >= response.len() {
				// Remove the pending request as per spec.
				state.requests.remove(&request_id);
				Ok(0)
			} else {
				let read = std::cmp::min(buffer.len(), response[req.read..].len());
				buffer[0..read].copy_from_slice(&response[req.read..read]);
				req.read += read;
				Ok(read)
			}
		} else {
			Err(HttpError::IoError)
		}
	}
}

/// The internal state of the fake transaction pool.
#[derive(Default)]
pub struct PoolState {
	/// A vector of transactions submitted from the runtime.
	pub transactions: Vec<Vec<u8>>,
}

/// Implementation of transaction pool used for test.
///
/// Note that this implementation does not verify correctness
/// of sent extrinsics. It's meant to be used in contexts
/// where an actual runtime is not known.
///
/// It's advised to write integration tests that include the
/// actual transaction pool to make sure the produced
/// transactions are valid.
#[derive(Default)]
pub struct TestTransactionPoolExt(Arc<RwLock<PoolState>>);

impl TestTransactionPoolExt {
	/// Create new `TestTransactionPoolExt` and a reference to the internal state.
	pub fn new() -> (Self, Arc<RwLock<PoolState>>) {
		let ext = Self::default();
		let state = ext.0.clone();
		(ext, state)
	}
}

impl TransactionPool for TestTransactionPoolExt {
	fn submit_transaction(&mut self, extrinsic: Vec<u8>) -> Result<(), ()> {
		self.0.write().transactions.push(extrinsic);
		Ok(())
	}
}
