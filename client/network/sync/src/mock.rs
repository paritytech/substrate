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

//! Contains a mock implementation of `ChainSync` that can be used
//! for testing calls made to `ChainSync`.

use futures::task::Poll;
use libp2p::PeerId;
use sc_network_common::sync::{
	message::{BlockAnnounce, BlockData, BlockRequest, BlockResponse},
	BadPeer, ChainSync as ChainSyncT, Metrics, OnBlockData, OnBlockJustification,
	OpaqueBlockResponse, PeerInfo, SyncStatus,
};
use sp_runtime::traits::{Block as BlockT, NumberFor};

mockall::mock! {
	pub ChainSync<Block: BlockT> {}

	impl<Block: BlockT> ChainSyncT<Block> for ChainSync<Block> {
		fn peer_info(&self, who: &PeerId) -> Option<PeerInfo<Block>>;
		fn status(&self) -> SyncStatus<Block>;
		fn num_sync_requests(&self) -> usize;
		fn num_downloaded_blocks(&self) -> usize;
		fn num_peers(&self) -> usize;
		fn num_active_peers(&self) -> usize;
		fn new_peer(
			&mut self,
			who: PeerId,
			best_hash: Block::Hash,
			best_number: NumberFor<Block>,
		) -> Result<Option<BlockRequest<Block>>, BadPeer>;
		fn update_chain_info(&mut self, best_hash: &Block::Hash, best_number: NumberFor<Block>);
		fn request_justification(&mut self, hash: &Block::Hash, number: NumberFor<Block>);
		fn clear_justification_requests(&mut self);
		fn set_sync_fork_request(
			&mut self,
			peers: Vec<PeerId>,
			hash: &Block::Hash,
			number: NumberFor<Block>,
		);
		fn on_block_data(
			&mut self,
			who: &PeerId,
			request: Option<BlockRequest<Block>>,
			response: BlockResponse<Block>,
		) -> Result<OnBlockData<Block>, BadPeer>;
		fn on_block_justification(
			&mut self,
			who: PeerId,
			response: BlockResponse<Block>,
		) -> Result<OnBlockJustification<Block>, BadPeer>;
		fn on_justification_import(
			&mut self,
			hash: Block::Hash,
			number: NumberFor<Block>,
			success: bool,
		);
		fn on_block_finalized(&mut self, hash: &Block::Hash, number: NumberFor<Block>);
		fn on_validated_block_announce(
			&mut self,
			is_best: bool,
			who: PeerId,
			announce: &BlockAnnounce<Block::Header>,
		);
		fn peer_disconnected(&mut self, who: &PeerId);
		fn metrics(&self) -> Metrics;
		fn block_response_into_blocks(
			&self,
			request: &BlockRequest<Block>,
			response: OpaqueBlockResponse,
		) -> Result<Vec<BlockData<Block>>, String>;
		fn poll<'a>(
			&mut self,
			cx: &mut std::task::Context<'a>,
		) -> Poll<()>;
		fn send_block_request(
			&mut self,
			who: PeerId,
			request: BlockRequest<Block>,
		);
	}
}
