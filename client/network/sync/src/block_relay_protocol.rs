// Copyright Parity Technologies (UK) Ltd.
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

//! Block relay protocol related definitions.

use futures::channel::oneshot;
use libp2p::PeerId;
use sc_network::request_responses::{ProtocolConfig, RequestFailure};
use sc_network_common::sync::message::{BlockData, BlockRequest};
use sp_runtime::traits::Block as BlockT;
use std::sync::Arc;

/// The serving side of the block relay protocol. It runs a single instance
/// of the server task that processes the incoming protocol messages.
#[async_trait::async_trait]
pub trait BlockServer<Block: BlockT>: Send {
	/// Starts the protocol processing.
	async fn run(&mut self);
}

/// The client side stub to download blocks from peers. This is a handle
/// that can be used to initiate concurrent downloads.
#[async_trait::async_trait]
pub trait BlockDownloader<Block: BlockT>: Send + Sync {
	/// Performs the protocol specific sequence to fetch the block from the peer.
	/// Output: if the download succeeds, the response is a `Vec<u8>` which is
	/// in a format specific to the protocol implementation. The block data
	/// can be extracted from this response using [`BlockDownloader::block_response_into_blocks`].
	async fn download_block(
		&self,
		who: PeerId,
		request: BlockRequest<Block>,
	) -> Result<Result<Vec<u8>, RequestFailure>, oneshot::Canceled>;

	/// Parses the protocol specific response to retrieve the block data.
	fn block_response_into_blocks(
		&self,
		request: &BlockRequest<Block>,
		response: Vec<u8>,
	) -> Result<Vec<BlockData<Block>>, BlockResponseError>;
}

/// Errors returned by [`BlockDownloader::block_response_into_blocks`].
#[derive(Debug)]
pub enum BlockResponseError {
	/// Failed to decode the response bytes.
	DecodeFailed(String),

	/// Failed to extract the blocks from the decoded bytes.
	ExtractionFailed(String),
}

/// Block relay specific params for network creation, specified in
/// ['sc_service::BuildNetworkParams'].
pub struct BlockRelayParams<Block: BlockT> {
	pub server: Box<dyn BlockServer<Block>>,
	pub downloader: Arc<dyn BlockDownloader<Block>>,
	pub request_response_config: ProtocolConfig,
}
