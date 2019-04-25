// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! RPC Metadata
use std::sync::Arc;

use jsonrpc_pubsub::{Session, PubSubMetadata};
use crate::rpc::futures::sync::mpsc;

/// RPC Metadata.
///
/// Manages persistent session for transports that support it
/// and may contain some additional info extracted from specific transports
/// (like remote client IP address, request headers, etc)
#[derive(Default, Clone)]
pub struct Metadata {
	session: Option<Arc<Session>>,
}

impl crate::rpc::Metadata for Metadata {}
impl PubSubMetadata for Metadata {
	fn session(&self) -> Option<Arc<Session>> {
		self.session.clone()
	}
}

impl Metadata {
	/// Create new `Metadata` with session (Pub/Sub) support.
	pub fn new(transport: mpsc::Sender<String>) -> Self {
		Metadata {
			session: Some(Arc::new(Session::new(transport))),
		}
	}

	/// Create new `Metadata` for tests.
	#[cfg(test)]
	pub fn new_test() -> (mpsc::Receiver<String>, Self) {
		let (tx, rx) = mpsc::channel(1);
		(rx, Self::new(tx))
	}
}
