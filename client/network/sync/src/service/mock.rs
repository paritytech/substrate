// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use futures::channel::oneshot;
use libp2p::{Multiaddr, PeerId};

use sc_consensus::{BlockImportError, BlockImportStatus};
use sc_network::{
	config::MultiaddrWithPeerId,
	request_responses::{IfDisconnected, RequestFailure},
	types::ProtocolName,
	NetworkNotification, NetworkPeers, NetworkRequest, NetworkSyncForkRequest,
	NotificationSenderError, NotificationSenderT, ReputationChange,
};
use sc_network_common::role::ObservedRole;
use sp_runtime::traits::{Block as BlockT, NumberFor};

use std::collections::HashSet;

mockall::mock! {
	pub ChainSyncInterface<B: BlockT> {
		pub fn justification_sync_link_request_justification(&self, hash: &B::Hash, number: NumberFor<B>);
		pub fn justification_sync_link_clear_justification_requests(&self);
	}

	impl<B: BlockT + 'static> NetworkSyncForkRequest<B::Hash, NumberFor<B>>
		for ChainSyncInterface<B>
	{
		fn set_sync_fork_request(&self, peers: Vec<PeerId>, hash: B::Hash, number: NumberFor<B>);
	}

	impl<B: BlockT> sc_consensus::Link<B> for ChainSyncInterface<B> {
		fn blocks_processed(
			&mut self,
			imported: usize,
			count: usize,
			results: Vec<(Result<BlockImportStatus<NumberFor<B>>, BlockImportError>, B::Hash)>,
		);
		fn justification_imported(
			&mut self,
			who: PeerId,
			hash: &B::Hash,
			number: NumberFor<B>,
			success: bool,
		);
		fn request_justification(&mut self, hash: &B::Hash, number: NumberFor<B>);
	}
}

impl<B: BlockT> sc_consensus::JustificationSyncLink<B> for MockChainSyncInterface<B> {
	fn request_justification(&self, hash: &B::Hash, number: NumberFor<B>) {
		self.justification_sync_link_request_justification(hash, number);
	}

	fn clear_justification_requests(&self) {
		self.justification_sync_link_clear_justification_requests();
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
		fn remove_peers_from_reserved_set(
			&self,
			protocol: ProtocolName,
			peers: Vec<PeerId>
		) -> Result<(), String>;
		fn sync_num_connected(&self) -> usize;
		fn peer_role(&self, peer_id: PeerId, handshake: Vec<u8>) -> Option<ObservedRole>;
	}

	#[async_trait::async_trait]
	impl NetworkRequest for Network {
		async fn request(
			&self,
			target: PeerId,
			protocol: ProtocolName,
			request: Vec<u8>,
			connect: IfDisconnected,
		) -> Result<Vec<u8>, RequestFailure>;
		fn start_request(
			&self,
			target: PeerId,
			protocol: ProtocolName,
			request: Vec<u8>,
			tx: oneshot::Sender<Result<Vec<u8>, RequestFailure>>,
			connect: IfDisconnected,
		);
	}

	impl NetworkNotification for Network {
		fn write_notification(&self, target: PeerId, protocol: ProtocolName, message: Vec<u8>);
		fn notification_sender(
			&self,
			target: PeerId,
			protocol: ProtocolName,
		) -> Result<Box<dyn NotificationSenderT>, NotificationSenderError>;
		fn set_notification_handshake(&self, protocol: ProtocolName, handshake: Vec<u8>);
	}
}
