// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

use std::sync::Arc;

use jsonrpc_pubsub::{Session, PubSubMetadata};

#[derive(Default, Clone)]
pub struct Metadata {
	session: Option<Arc<Session>>,
}

impl ::rpc::Metadata for Metadata {}
impl PubSubMetadata for Metadata {
	fn session(&self) -> Option<Arc<Session>> {
		self.session.clone()
	}
}

impl Metadata {
	pub fn new(transport: ::rpc::futures::sync::mpsc::Sender<String>) -> Self {
		Metadata {
			session: Some(Arc::new(Session::new(transport))),
		}
	}
}
