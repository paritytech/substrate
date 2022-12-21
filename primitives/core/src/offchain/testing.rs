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

//! Utilities for offchain calls testing.
//!
//! Namely all ExecutionExtensions that allow mocking
//! the extra APIs.

use crate::{
	offchain::{
		self, storage::InMemOffchainStorage, HttpError, HttpRequestId as RequestId,
		HttpRequestStatus as RequestStatus, OffchainOverlayedChange, OffchainStorage,
		OpaqueNetworkState, StorageKind, Timestamp, TransactionPool,
	},
	OpaquePeerId,
};
use std::{
	collections::{BTreeMap, VecDeque},
	sync::Arc,
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

/// Sharable "persistent" offchain storage for test.
#[derive(Debug, Clone, Default)]
pub struct TestPersistentOffchainDB {
	persistent: Arc<RwLock<InMemOffchainStorage>>,
}

impl TestPersistentOffchainDB {
	const PREFIX: &'static [u8] = b"";

	/// Create a new and empty offchain storage db for persistent items
	pub fn new() -> Self {
		Self { persistent: Arc::new(RwLock::new(InMemOffchainStorage::default())) }
	}

	/// Apply a set of off-chain changes directly to the test backend
	pub fn apply_offchain_changes(
		&mut self,
		changes: impl Iterator<Item = ((Vec<u8>, Vec<u8>), OffchainOverlayedChange)>,
	) {
		let mut me = self.persistent.write();
		for ((_prefix, key), value_operation) in changes {
			match value_operation {
				OffchainOverlayedChange::SetValue(val) =>
					me.set(Self::PREFIX, key.as_slice(), val.as_slice()),
				OffchainOverlayedChange::Remove => me.remove(Self::PREFIX, key.as_slice()),
			}
		}
	}

	/// Retrieve a key from the test backend.
	pub fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
		OffchainStorage::get(self, Self::PREFIX, key)
	}
}

impl OffchainStorage for TestPersistentOffchainDB {
	fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		self.persistent.write().set(prefix, key, value);
	}

	fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		self.persistent.write().remove(prefix, key);
	}

	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		self.persistent.read().get(prefix, key)
	}

	fn compare_and_set(
		&mut self,
		prefix: &[u8],
		key: &[u8],
		old_value: Option<&[u8]>,
		new_value: &[u8],
	) -> bool {
		self.persistent.write().compare_and_set(prefix, key, old_value, new_value)
	}
}

/// Internal state of the externalities.
///
/// This can be used in tests to respond or assert stuff about interactions.
#[derive(Debug, Default)]
pub struct OffchainState {
	/// A list of pending requests.
	pub requests: BTreeMap<RequestId, PendingRequest>,
	// Queue of requests that the test is expected to perform (in order).
	expected_requests: VecDeque<PendingRequest>,
	/// Persistent local storage
	pub persistent_storage: TestPersistentOffchainDB,
	/// Local storage
	pub local_storage: InMemOffchainStorage,
	/// A supposedly random seed.
	pub seed: [u8; 32],
	/// A timestamp simulating the current time.
	pub timestamp: Timestamp,
}

impl OffchainState {
	/// Asserts that pending request has been submitted and fills it's response.
	pub fn fulfill_pending_request(
		&mut self,
		id: u16,
		expected: PendingRequest,
		response: impl Into<Vec<u8>>,
		response_headers: impl IntoIterator<Item = (String, String)>,
	) {
		match self.requests.get_mut(&RequestId(id)) {
			None => {
				panic!("Missing pending request: {:?}.\n\nAll: {:?}", id, self.requests);
			},
			Some(req) => {
				assert_eq!(*req, expected);
				req.response = Some(response.into());
				req.response_headers = response_headers.into_iter().collect();
			},
		}
	}

	fn fulfill_expected(&mut self, id: u16) {
		if let Some(mut req) = self.expected_requests.pop_back() {
			let response = req.response.take().expect("Response checked when added.");
			let headers = std::mem::take(&mut req.response_headers);
			self.fulfill_pending_request(id, req, response, headers);
		}
	}

	/// Add expected HTTP request.
	///
	/// This method can be used to initialize expected HTTP requests and their responses
	/// before running the actual code that utilizes them (for instance before calling into
	/// runtime). Expected request has to be fulfilled before this struct is dropped,
	/// the `response` and `response_headers` fields will be used to return results to the callers.
	/// Requests are expected to be performed in the insertion order.
	pub fn expect_request(&mut self, expected: PendingRequest) {
		if expected.response.is_none() {
			panic!("Expected request needs to have a response.");
		}
		self.expected_requests.push_front(expected);
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

	/// Create new `TestOffchainExt` and a reference to the internal state.
	pub fn with_offchain_db(
		offchain_db: TestPersistentOffchainDB,
	) -> (Self, Arc<RwLock<OffchainState>>) {
		let (ext, state) = Self::new();
		ext.0.write().persistent_storage = offchain_db;
		(ext, state)
	}
}

impl offchain::Externalities for TestOffchainExt {
	fn is_validator(&self) -> bool {
		true
	}

	fn network_state(&self) -> Result<OpaqueNetworkState, ()> {
		Ok(OpaqueNetworkState { peer_id: Default::default(), external_addresses: vec![] })
	}

	fn timestamp(&mut self) -> Timestamp {
		self.0.read().timestamp
	}

	fn sleep_until(&mut self, deadline: Timestamp) {
		self.0.write().timestamp = deadline;
	}

	fn random_seed(&mut self) -> [u8; 32] {
		self.0.read().seed
	}

	fn http_request_start(
		&mut self,
		method: &str,
		uri: &str,
		meta: &[u8],
	) -> Result<RequestId, ()> {
		let mut state = self.0.write();
		let id = RequestId(state.requests.len() as u16);
		state.requests.insert(
			id,
			PendingRequest {
				method: method.into(),
				uri: uri.into(),
				meta: meta.into(),
				..Default::default()
			},
		);
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
		_deadline: Option<Timestamp>,
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

		ids.iter()
			.map(|id| match state.requests.get(id) {
				Some(req) if req.response.is_none() => {
					panic!("No `response` provided for request with id: {:?}", id)
				},
				None => RequestStatus::Invalid,
				_ => RequestStatus::Finished(200),
			})
			.collect()
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
		_deadline: Option<Timestamp>,
	) -> Result<usize, HttpError> {
		let mut state = self.0.write();
		if let Some(req) = state.requests.get_mut(&request_id) {
			let response = req
				.response
				.as_mut()
				.unwrap_or_else(|| panic!("No response provided for request: {:?}", request_id));

			if req.read >= response.len() {
				// Remove the pending request as per spec.
				state.requests.remove(&request_id);
				Ok(0)
			} else {
				let read = std::cmp::min(buffer.len(), response[req.read..].len());
				buffer[0..read].copy_from_slice(&response[req.read..req.read + read]);
				req.read += read;
				Ok(read)
			}
		} else {
			Err(HttpError::IoError)
		}
	}

	fn set_authorized_nodes(&mut self, _nodes: Vec<OpaquePeerId>, _authorized_only: bool) {
		unimplemented!()
	}
}

impl offchain::DbExternalities for TestOffchainExt {
	fn local_storage_set(&mut self, kind: StorageKind, key: &[u8], value: &[u8]) {
		let mut state = self.0.write();
		match kind {
			StorageKind::LOCAL => state.local_storage.set(b"", key, value),
			StorageKind::PERSISTENT => state.persistent_storage.set(b"", key, value),
		};
	}

	fn local_storage_clear(&mut self, kind: StorageKind, key: &[u8]) {
		let mut state = self.0.write();
		match kind {
			StorageKind::LOCAL => state.local_storage.remove(b"", key),
			StorageKind::PERSISTENT => state.persistent_storage.remove(b"", key),
		};
	}

	fn local_storage_compare_and_set(
		&mut self,
		kind: StorageKind,
		key: &[u8],
		old_value: Option<&[u8]>,
		new_value: &[u8],
	) -> bool {
		let mut state = self.0.write();
		match kind {
			StorageKind::LOCAL =>
				state.local_storage.compare_and_set(b"", key, old_value, new_value),
			StorageKind::PERSISTENT =>
				state.persistent_storage.compare_and_set(b"", key, old_value, new_value),
		}
	}

	fn local_storage_get(&mut self, kind: StorageKind, key: &[u8]) -> Option<Vec<u8>> {
		let state = self.0.read();
		match kind {
			StorageKind::LOCAL => state.local_storage.get(TestPersistentOffchainDB::PREFIX, key),
			StorageKind::PERSISTENT => state.persistent_storage.get(key),
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
