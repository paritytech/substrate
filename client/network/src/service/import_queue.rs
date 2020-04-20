// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Wraps around a `Box<dyn ImportQueue<_>>` and gives it a better future-oriented API.

use crate::PeerId;

use futures::prelude::*;
use sp_consensus::BlockOrigin;
use sp_consensus::import_queue::{BlockImportError, BlockImportResult, ImportQueue, Link, Origin, IncomingBlock};
use sp_runtime::{Justification, traits::{Block as BlockT, NumberFor}};
use sp_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use std::task::Poll;

/// Wraps around a `Box<dyn ImportQueue<B>>`.
pub struct SmartImportQueue<B: BlockT> {
	queue: Box<dyn ImportQueue<B>>,
	pending_actions_tx: TracingUnboundedSender<ImportQueueAction<B>>,
	pending_actions_rx: TracingUnboundedReceiver<ImportQueueAction<B>>,
}

impl<B: BlockT> SmartImportQueue<B> {
	/// Import bunch of blocks.
	pub fn import_blocks(&mut self, origin: BlockOrigin, blocks: Vec<IncomingBlock<B>>) {
		self.queue.import_blocks(origin, blocks);
	}

	/// Import a block justification.
	pub fn import_justification(
		&mut self,
		who: Origin,
		hash: B::Hash,
		number: NumberFor<B>,
		justification: Justification
	) {
		self.queue.import_justification(who, hash, number, justification);
	}

	/// Import block finality proof.
	pub fn import_finality_proof(
		&mut self,
		who: Origin,
		hash: B::Hash,
		number: NumberFor<B>,
		finality_proof: Vec<u8>
	) {
		self.queue.import_finality_proof(who, hash, number, finality_proof);
	}

	/// Returns the next action reported by the import queue.
	pub fn next_action<'a>(&'a mut self) -> impl Future<Output = ImportQueueAction<B>> + 'a {
		future::poll_fn(move |cx| {
			// Try to empty the receiver first, so that the unbounded queue doesn't get filled up
			// if `next_action` isn't called quickly enough.
			if let Poll::Ready(Some(action)) = self.pending_actions_rx.poll_next_unpin(cx) {
				return Poll::Ready(action)
			}

			// If the receiver is empty, ask the import queue to push things on it.
			self.queue.poll_actions(cx, &mut NetworkLink {
				out: &mut self.pending_actions_tx,
			});

			if let Poll::Ready(Some(action)) = self.pending_actions_rx.poll_next_unpin(cx) {
				Poll::Ready(action)
			} else {
				Poll::Pending
			}
		})
	}
}

impl<B: BlockT> From<Box<dyn ImportQueue<B>>> for SmartImportQueue<B> {
	fn from(queue: Box<dyn ImportQueue<B>>) -> Self {
		let (pending_actions_tx, pending_actions_rx) = tracing_unbounded("smart-import-queue");
		SmartImportQueue {
			queue,
			pending_actions_tx,
			pending_actions_rx,
		}
	}
}

/// Action that the import queue has performed.
///
/// This enum mimics the functions of the `Link` trait.
pub enum ImportQueueAction<B: BlockT> {
	BlocksProcessed {
		imported: usize,
		count: usize,
		results: Vec<(Result<BlockImportResult<NumberFor<B>>, BlockImportError>, B::Hash)>,
	},
	JustificationImported {
		who: PeerId,
		hash: B::Hash,
		number: NumberFor<B>,
		success: bool,
	},
	RequestJustification {
		hash: B::Hash,
		number: NumberFor<B>,
	},
	RequestFinalityProof {
		hash: B::Hash,
		number: NumberFor<B>,
	},
	FinalityProofImported {
		who: PeerId,
		request_block: (B::Hash, NumberFor<B>),
		finalization_result: Result<(B::Hash, NumberFor<B>), ()>,
	},
}

// Implementation of `import_queue::Link` trait that sends actions on the sender inside of it.
struct NetworkLink<'a, B: BlockT> {
	out: &'a mut TracingUnboundedSender<ImportQueueAction<B>>,
}

impl<'a, B: BlockT> Link<B> for NetworkLink<'a, B> {
	fn blocks_processed(
		&mut self,
		imported: usize,
		count: usize,
		results: Vec<(Result<BlockImportResult<NumberFor<B>>, BlockImportError>, B::Hash)>
	) {
		let _ = self.out.unbounded_send(ImportQueueAction::BlocksProcessed {
			imported,
			count,
			results,
		});
	}

	fn justification_imported(&mut self, who: PeerId, hash: &B::Hash, number: NumberFor<B>, success: bool) {
		let _ = self.out.unbounded_send(ImportQueueAction::JustificationImported {
			who,
			hash: hash.clone(),
			number,
			success,
		});
	}

	fn request_justification(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self.out.unbounded_send(ImportQueueAction::RequestJustification {
			hash: hash.clone(),
			number,
		});
	}

	fn request_finality_proof(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self.out.unbounded_send(ImportQueueAction::RequestFinalityProof {
			hash: hash.clone(),
			number,
		});
	}

	fn finality_proof_imported(
		&mut self,
		who: PeerId,
		request_block: (B::Hash, NumberFor<B>),
		finalization_result: Result<(B::Hash, NumberFor<B>), ()>,
	) {
		let _ = self.out.unbounded_send(ImportQueueAction::FinalityProofImported {
			who,
			request_block,
			finalization_result,
		});
	}
}
