// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! RPC Metadata
use std::sync::Arc;

use jsonrpc_core::futures::sync::mpsc;
use jsonrpc_pubsub::{PubSubMetadata, Session};

/// RPC Metadata.
///
/// Manages persistent session for transports that support it
/// and may contain some additional info extracted from specific transports
/// (like remote client IP address, request headers, etc)
#[derive(Default, Clone)]
pub struct Metadata {
	session: Option<Arc<Session>>,
}

impl jsonrpc_core::Metadata for Metadata {}
impl PubSubMetadata for Metadata {
	fn session(&self) -> Option<Arc<Session>> {
		self.session.clone()
	}
}

impl Metadata {
	/// Create new `Metadata` with session (Pub/Sub) support.
	pub fn new(transport: mpsc::Sender<String>) -> Self {
		Metadata { session: Some(Arc::new(Session::new(transport))) }
	}

	/// Create new `Metadata` for tests.
	#[cfg(test)]
	pub fn new_test() -> (mpsc::Receiver<String>, Self) {
		let (tx, rx) = mpsc::channel(1);
		(rx, Self::new(tx))
	}
}

impl From<mpsc::Sender<String>> for Metadata {
	fn from(sender: mpsc::Sender<String>) -> Self {
		Self::new(sender)
	}
}
