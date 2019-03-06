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
