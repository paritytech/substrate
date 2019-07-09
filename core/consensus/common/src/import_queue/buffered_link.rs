// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Provides the `buffered_link` utility.
//!
//! The buffered link is a channel that allows buffering the method calls on `Link`.
//!
//! # Example
//!
//! ```no_run
//! use substrate_consensus_common::import_queue::Link;
//! # use substrate_consensus_common::import_queue::buffered_link::buffered_link;
//! # use test_client::runtime::Block;
//! # struct DummyLink; impl Link<Block> for DummyLink {}
//! # let mut my_link = DummyLink;
//! let (mut tx, mut rx) = buffered_link::<Block>();
//! tx.blocks_processed(vec![], false);
//! rx.poll_actions(&mut my_link);	// Calls `my_link.blocks_processed(vec![], false)`
//! ```
//!

use futures::{prelude::*, sync::mpsc};
use runtime_primitives::traits::{Block as BlockT, NumberFor};
use crate::import_queue::{Origin, Link, SharedFinalityProofRequestBuilder};

/// Wraps around an unbounded channel from the `futures` crate. The sender implements `Link` and
/// can be used to buffer commands, and the receiver can be used to poll said commands and transfer
/// them to another link.
pub fn buffered_link<B: BlockT>() -> (BufferedLinkSender<B>, BufferedLinkReceiver<B>) {
	let (tx, rx) = mpsc::unbounded();
	let tx = BufferedLinkSender { tx };
	let rx = BufferedLinkReceiver { rx };
	(tx, rx)
}

/// See [`buffered_link`].
pub struct BufferedLinkSender<B: BlockT> {
	tx: mpsc::UnboundedSender<BlockImportWorkerMsg<B>>,
}

/// Internal buffered message.
enum BlockImportWorkerMsg<B: BlockT> {
	BlockImported(B::Hash, NumberFor<B>),
	BlocksProcessed(Vec<B::Hash>, bool),
	JustificationImported(Origin, B::Hash, NumberFor<B>, bool),
	ClearJustificationRequests,
	RequestJustification(B::Hash, NumberFor<B>),
	FinalityProofImported(Origin, (B::Hash, NumberFor<B>), Result<(B::Hash, NumberFor<B>), ()>),
	RequestFinalityProof(B::Hash, NumberFor<B>),
	SetFinalityProofRequestBuilder(SharedFinalityProofRequestBuilder<B>),
	ReportPeer(Origin, i32),
	Restart,
}

impl<B: BlockT> Link<B> for BufferedLinkSender<B> {
	fn block_imported(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self.tx.unbounded_send(BlockImportWorkerMsg::BlockImported(hash.clone(), number));
	}

	fn blocks_processed(&mut self, processed_blocks: Vec<B::Hash>, has_error: bool) {
		let _ = self.tx.unbounded_send(BlockImportWorkerMsg::BlocksProcessed(processed_blocks, has_error));
	}

	fn justification_imported(
		&mut self,
		who: Origin,
		hash: &B::Hash,
		number: NumberFor<B>,
		success: bool
	) {
		let msg = BlockImportWorkerMsg::JustificationImported(who, hash.clone(), number, success);
		let _ = self.tx.unbounded_send(msg);
	}

	fn clear_justification_requests(&mut self) {
		let _ = self.tx.unbounded_send(BlockImportWorkerMsg::ClearJustificationRequests);
	}

	fn request_justification(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self.tx.unbounded_send(BlockImportWorkerMsg::RequestJustification(hash.clone(), number));
	}

	fn finality_proof_imported(
		&mut self,
		who: Origin,
		request_block: (B::Hash, NumberFor<B>),
		finalization_result: Result<(B::Hash, NumberFor<B>), ()>,
	) {
		let msg = BlockImportWorkerMsg::FinalityProofImported(who, request_block, finalization_result);
		let _ = self.tx.unbounded_send(msg);
	}

	fn request_finality_proof(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self.tx.unbounded_send(BlockImportWorkerMsg::RequestFinalityProof(hash.clone(), number));
	}

	fn set_finality_proof_request_builder(&mut self, request_builder: SharedFinalityProofRequestBuilder<B>) {
		let _ = self.tx.unbounded_send(BlockImportWorkerMsg::SetFinalityProofRequestBuilder(request_builder));
	}

	fn report_peer(&mut self, who: Origin, reputation_change: i32) {
		let _ = self.tx.unbounded_send(BlockImportWorkerMsg::ReportPeer(who, reputation_change));
	}

	fn restart(&mut self) {
		let _ = self.tx.unbounded_send(BlockImportWorkerMsg::Restart);
	}
}

/// See [`buffered_link`].
pub struct BufferedLinkReceiver<B: BlockT> {
	rx: mpsc::UnboundedReceiver<BlockImportWorkerMsg<B>>,
}

impl<B: BlockT> BufferedLinkReceiver<B> {
	/// Polls for the buffered link actions. Any enqueued action will be propagated to the link
	/// passed as parameter.
	///
	/// This method should behave in a way similar to `Future::poll`. It can register the current
	/// task and notify later when more actions are ready to be polled. To continue the comparison,
	/// it is as if this method always returned `Ok(Async::NotReady)`.
	pub fn poll_actions(&mut self, link: &mut dyn Link<B>) {
		loop {
			let msg = if let Ok(Async::Ready(Some(msg))) = self.rx.poll() {
				msg
			} else {
				break
			};

			match msg {
				BlockImportWorkerMsg::BlockImported(hash, number) =>
					link.block_imported(&hash, number),
				BlockImportWorkerMsg::BlocksProcessed(blocks, has_error) =>
					link.blocks_processed(blocks, has_error),
				BlockImportWorkerMsg::JustificationImported(who, hash, number, success) =>
					link.justification_imported(who, &hash, number, success),
				BlockImportWorkerMsg::ClearJustificationRequests =>
					link.clear_justification_requests(),
				BlockImportWorkerMsg::RequestJustification(hash, number) =>
					link.request_justification(&hash, number),
				BlockImportWorkerMsg::FinalityProofImported(who, block, result) =>
					link.finality_proof_imported(who, block, result),
				BlockImportWorkerMsg::RequestFinalityProof(hash, number) =>
					link.request_finality_proof(&hash, number),
				BlockImportWorkerMsg::SetFinalityProofRequestBuilder(builder) =>
					link.set_finality_proof_request_builder(builder),
				BlockImportWorkerMsg::ReportPeer(who, reput) =>
					link.report_peer(who, reput),
				BlockImportWorkerMsg::Restart =>
					link.restart(),
			}
		}
	}
}
