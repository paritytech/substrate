// Copyright 2020 Parity Technologies (UK) Ltd.
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

use crate::ServicetoWorkerMsg;

use futures::channel::{mpsc, oneshot};
use futures::SinkExt;

use sc_network::Multiaddr;
use sp_authority_discovery::AuthorityId;

/// Service to interact with the [`Worker`].
#[derive(Clone)]
pub struct Service {
	to_worker: mpsc::Sender<ServicetoWorkerMsg>,
}

/// A [`Service`] allows to interact with a [`Worker`], e.g. by querying the
/// [`Worker`]'s local address cache for a given [`AuthorityId`].
impl Service {
	pub(crate) fn new(to_worker: mpsc::Sender<ServicetoWorkerMsg>) -> Self {
		Self {
			to_worker,
		}
	}

	/// Get the addresses for the given [`AuthorityId`] from the local address cache.
	//
	// TODO: Should this function be able to error?
	pub async fn get_addresses(&mut self, authority: AuthorityId) -> Option<Vec<Multiaddr>> {
		let (tx, rx) = oneshot::channel();

		if let Err(_) = self.to_worker.send(ServicetoWorkerMsg::GetAddresses(authority, tx)).await {
			return None;
		}

		rx.await.ok().flatten()
	}
}
