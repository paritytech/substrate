// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use sc_network_common::service::{NetworkPeers, NetworkSyncForkRequest};
use sp_runtime::traits::{Block as BlockT, NumberFor};

pub use libp2p::{identity::error::SigningError, kad::record::Key as KademliaKey};
use libp2p::{Multiaddr, PeerId};
use sc_network_common::{config::MultiaddrWithPeerId, protocol::ProtocolName};
use sc_peerset::ReputationChange;
use std::collections::HashSet;

mockall::mock! {
	pub ChainSyncInterface<B: BlockT> {}

	impl<B: BlockT + 'static> NetworkSyncForkRequest<B::Hash, NumberFor<B>>
		for ChainSyncInterface<B>
	{
		fn set_sync_fork_request(&self, peers: Vec<PeerId>, hash: B::Hash, number: NumberFor<B>);
	}
}

mockall::mock! {
	pub NetworkServiceHandle {}
}

// Mocked `Network` for `ChainSync`-related tests
mockall::mock! {
	pub Network {}

	impl NetworkPeers for Network {
		fn set_authorized_peers(&self, peers: HashSet<PeerId>);
		fn set_authorized_only(&self, reserved_only: bool);
		fn add_known_address(&self, peer_id: PeerId, addr: Multiaddr);
		fn report_peer(&self, who: PeerId, cost_benefit: ReputationChange);
		fn disconnect_peer(&self, who: PeerId, protocol: ProtocolName);
		fn accept_unreserved_peers(&self);
		fn deny_unreserved_peers(&self);
		fn add_reserved_peer(&self, peer: MultiaddrWithPeerId) -> Result<(), String>;
		fn remove_reserved_peer(&self, peer_id: PeerId);
		fn set_reserved_peers(
			&self,
			protocol: ProtocolName,
			peers: HashSet<Multiaddr>,
		) -> Result<(), String>;
		fn add_peers_to_reserved_set(
			&self,
			protocol: ProtocolName,
			peers: HashSet<Multiaddr>,
		) -> Result<(), String>;
		fn remove_peers_from_reserved_set(&self, protocol: ProtocolName, peers: Vec<PeerId>);
		fn add_to_peers_set(
			&self,
			protocol: ProtocolName,
			peers: HashSet<Multiaddr>,
		) -> Result<(), String>;
		fn remove_from_peers_set(&self, protocol: ProtocolName, peers: Vec<PeerId>);
		fn sync_num_connected(&self) -> usize;
	}
}
