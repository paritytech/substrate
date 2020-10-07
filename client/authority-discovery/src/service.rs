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

use sc_network::{Multiaddr, PeerId};
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

	/// Get the addresses for the given [`AuthorityId`] from the local address
	/// cache.
	///
	/// Returns `None` if no entry was present or connection to the
	/// [`crate::Worker`] failed.
	///
	/// [`Multiaddr`]s returned always include a [`PeerId`] via a
	/// [`libp2p::core::multiaddr:Protocol::P2p`] component. [`Multiaddr`]s
	/// might differ in their [`PeerId`], e.g. when each [`Multiaddr`]
	/// represents a different sentry node. This might change once support for
	/// sentry nodes is removed (see
	/// https://github.com/paritytech/substrate/issues/6845).
	pub async fn get_addresses_by_authority_id(&mut self, authority: AuthorityId) -> Option<Vec<Multiaddr>> {
		let (tx, rx) = oneshot::channel();

		self.to_worker
			.send(ServicetoWorkerMsg::GetAddressesByAuthorityId(authority, tx))
			.await
			.ok()?;

		rx.await.ok().flatten()
	}

	/// Get the [`AuthorityId`] for the given [`PeerId`] from the local address
	/// cache.
	///
	/// Returns `None` if no entry was present or connection to the
	/// [`crate::Worker`] failed.
	pub async fn get_authority_id_by_peer_id(&mut self, peer_id: PeerId) -> Option<AuthorityId> {
		let (tx, rx) = oneshot::channel();

		self.to_worker
			.send(ServicetoWorkerMsg::GetAuthorityIdByPeerId(peer_id, tx))
			.await
			.ok()?;

		rx.await.ok().flatten()
	}
}
