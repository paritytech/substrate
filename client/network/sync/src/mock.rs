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

//! Contains a mock implementation of `ChainSync` that can be used
//! for testing calls made to `ChainSync`.

use futures::task::Poll;
use libp2p::PeerId;
use sc_consensus::{BlockImportError, BlockImportStatus};
use sc_network_common::sync::{
	message::{BlockAnnounce, BlockData, BlockRequest, BlockResponse},
	warp::{EncodedProof, WarpProofRequest},
	BadPeer, ChainSync as ChainSyncT, Metrics, OnBlockData, OnBlockJustification, OnStateData,
	OpaqueBlockRequest, OpaqueBlockResponse, OpaqueStateRequest, OpaqueStateResponse, PeerInfo,
	PollBlockAnnounceValidation, SyncStatus,
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
		fn justification_requests<'a>(
			&'a mut self,
		) -> Box<dyn Iterator<Item = (PeerId, BlockRequest<Block>)> + 'a>;
		fn block_requests<'a>(&'a mut self) -> Box<dyn Iterator<Item = (PeerId, BlockRequest<Block>)> + 'a>;
		fn state_request(&mut self) -> Option<(PeerId, OpaqueStateRequest)>;
		fn warp_sync_request(&mut self) -> Option<(PeerId, WarpProofRequest<Block>)>;
		fn on_block_data(
			&mut self,
			who: &PeerId,
			request: Option<BlockRequest<Block>>,
			response: BlockResponse<Block>,
		) -> Result<OnBlockData<Block>, BadPeer>;
		fn on_state_data(
			&mut self,
			who: &PeerId,
			response: OpaqueStateResponse,
		) -> Result<OnStateData<Block>, BadPeer>;
		fn on_warp_sync_data(&mut self, who: &PeerId, response: EncodedProof) -> Result<(), BadPeer>;
		fn on_block_justification(
			&mut self,
			who: PeerId,
			response: BlockResponse<Block>,
		) -> Result<OnBlockJustification<Block>, BadPeer>;
		fn on_blocks_processed(
			&mut self,
			imported: usize,
			count: usize,
			results: Vec<(Result<BlockImportStatus<NumberFor<Block>>, BlockImportError>, Block::Hash)>,
		) -> Box<dyn Iterator<Item = Result<(PeerId, BlockRequest<Block>), BadPeer>>>;
		fn on_justification_import(
			&mut self,
			hash: Block::Hash,
			number: NumberFor<Block>,
			success: bool,
		);
		fn on_block_finalized(&mut self, hash: &Block::Hash, number: NumberFor<Block>);
		fn push_block_announce_validation(
			&mut self,
			who: PeerId,
			hash: Block::Hash,
			announce: BlockAnnounce<Block::Header>,
			is_best: bool,
		);
		fn poll_block_announce_validation<'a>(
			&mut self,
			cx: &mut std::task::Context<'a>,
		) -> Poll<PollBlockAnnounceValidation<Block::Header>>;
		fn peer_disconnected(&mut self, who: &PeerId) -> Option<OnBlockData<Block>>;
		fn metrics(&self) -> Metrics;
		fn create_opaque_block_request(&self, request: &BlockRequest<Block>) -> OpaqueBlockRequest;
		fn encode_block_request(&self, request: &OpaqueBlockRequest) -> Result<Vec<u8>, String>;
		fn decode_block_response(&self, response: &[u8]) -> Result<OpaqueBlockResponse, String>;
		fn block_response_into_blocks(
			&self,
			request: &BlockRequest<Block>,
			response: OpaqueBlockResponse,
		) -> Result<Vec<BlockData<Block>>, String>;
		fn encode_state_request(&self, request: &OpaqueStateRequest) -> Result<Vec<u8>, String>;
		fn decode_state_response(&self, response: &[u8]) -> Result<OpaqueStateResponse, String>;
		fn poll<'a>(
			&mut self,
			cx: &mut std::task::Context<'a>,
		) -> Poll<PollBlockAnnounceValidation<Block::Header>>;
	}
}
