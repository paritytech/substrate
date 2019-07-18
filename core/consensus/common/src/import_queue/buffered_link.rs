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
//! tx.blocks_processed(0, 0, vec![]);
//! rx.poll_actions(&mut my_link);	// Calls `my_link.blocks_processed(0, 0, vec![])`
//! ```
//!

use futures::{prelude::*, sync::mpsc};
use runtime_primitives::traits::{Block as BlockT, NumberFor};
use crate::import_queue::{Origin, Link, BlockImportResult, BlockImportError};

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

impl<B: BlockT> BufferedLinkSender<B> {
	/// Returns true if the sender points to nowhere.
	///
	/// Once `true` is returned, it is pointless to use the sender anymore.
	pub fn is_closed(&self) -> bool {
		self.tx.is_closed()
	}
}

/// Internal buffered message.
enum BlockImportWorkerMsg<B: BlockT> {
	BlocksProcessed(usize, usize, Vec<(Result<BlockImportResult<NumberFor<B>>, BlockImportError>, B::Hash)>),
	JustificationImported(Origin, B::Hash, NumberFor<B>, bool),
	RequestJustification(B::Hash, NumberFor<B>),
	FinalityProofImported(Origin, (B::Hash, NumberFor<B>), Result<(B::Hash, NumberFor<B>), ()>),
	RequestFinalityProof(B::Hash, NumberFor<B>),
}

impl<B: BlockT> Link<B> for BufferedLinkSender<B> {
	fn blocks_processed(
		&mut self,
		imported: usize,
		count: usize,
		results: Vec<(Result<BlockImportResult<NumberFor<B>>, BlockImportError>, B::Hash)>
	) {
		let _ = self.tx.unbounded_send(BlockImportWorkerMsg::BlocksProcessed(imported, count, results));
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
				BlockImportWorkerMsg::BlocksProcessed(imported, count, results) =>
					link.blocks_processed(imported, count, results),
				BlockImportWorkerMsg::JustificationImported(who, hash, number, success) =>
					link.justification_imported(who, &hash, number, success),
				BlockImportWorkerMsg::RequestJustification(hash, number) =>
					link.request_justification(&hash, number),
				BlockImportWorkerMsg::FinalityProofImported(who, block, result) =>
					link.finality_proof_imported(who, block, result),
				BlockImportWorkerMsg::RequestFinalityProof(hash, number) =>
					link.request_finality_proof(&hash, number),
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use test_client::runtime::Block;

	#[test]
	fn is_closed() {
		let (tx, rx) = super::buffered_link::<Block>();
		assert!(!tx.is_closed());
		drop(rx);
		assert!(tx.is_closed());
	}
}
