// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use std::{collections::HashSet, fmt::Debug};

use crate::ServicetoWorkerMsg;

use futures::{
	channel::{mpsc, oneshot},
	SinkExt,
};

use sc_network::{Multiaddr, PeerId};
use sp_authority_discovery::AuthorityId;

/// Service to interact with the [`crate::Worker`].
#[derive(Clone)]
pub struct Service {
	to_worker: mpsc::Sender<ServicetoWorkerMsg>,
}

impl Debug for Service {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		f.debug_tuple("AuthorityDiscoveryService").finish()
	}
}

/// A [`Service`] allows to interact with a [`crate::Worker`], e.g. by querying the
/// [`crate::Worker`]'s local address cache for a given [`AuthorityId`].
impl Service {
	pub(crate) fn new(to_worker: mpsc::Sender<ServicetoWorkerMsg>) -> Self {
		Self { to_worker }
	}

	/// Get the addresses for the given [`AuthorityId`] from the local address
	/// cache.
	///
	/// Returns `None` if no entry was present or connection to the
	/// [`crate::Worker`] failed.
	///
	/// Note: [`Multiaddr`]s returned always include a [`PeerId`] via a
	/// [`libp2p::core::multiaddr::Protocol::P2p`] component. Equality of
	/// [`PeerId`]s across [`Multiaddr`]s returned by a single call is not
	/// enforced today, given that there are still authorities out there
	/// publishing the addresses of their sentry nodes on the DHT. In the future
	/// this guarantee can be provided.
	pub async fn get_addresses_by_authority_id(
		&mut self,
		authority: AuthorityId,
	) -> Option<HashSet<Multiaddr>> {
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
	pub async fn get_authority_ids_by_peer_id(
		&mut self,
		peer_id: PeerId,
	) -> Option<HashSet<AuthorityId>> {
		let (tx, rx) = oneshot::channel();

		self.to_worker
			.send(ServicetoWorkerMsg::GetAuthorityIdsByPeerId(peer_id, tx))
			.await
			.ok()?;

		rx.await.ok().flatten()
	}
}
