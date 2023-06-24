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

//! Provides the `buffered_link` utility.
//!
//! The buffered link is a channel that allows buffering the method calls on `Link`.
//!
//! # Example
//!
//! ```
//! use sc_consensus::import_queue::Link;
//! # use sc_consensus::import_queue::buffered_link::buffered_link;
//! # use sp_test_primitives::Block;
//! # struct DummyLink; impl Link<Block> for DummyLink {}
//! # let mut my_link = DummyLink;
//! let (mut tx, mut rx) = buffered_link::<Block>(100_000);
//! tx.blocks_processed(0, 0, vec![]);
//!
//! // Calls `my_link.blocks_processed(0, 0, vec![])` when polled.
//! let _fut = futures::future::poll_fn(move |cx| {
//! 	rx.poll_actions(cx, &mut my_link);
//! 	std::task::Poll::Pending::<()>
//! });
//! ```

use crate::import_queue::{Link, RuntimeOrigin};
use futures::prelude::*;
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use sp_runtime::traits::{Block as BlockT, NumberFor};
use std::{
	pin::Pin,
	task::{Context, Poll},
};

use super::BlockImportResult;

/// Wraps around an unbounded channel from the `futures` crate. The sender implements `Link` and
/// can be used to buffer commands, and the receiver can be used to poll said commands and transfer
/// them to another link. `queue_size_warning` sets the warning threshold of the channel queue size.
pub fn buffered_link<B: BlockT>(
	queue_size_warning: usize,
) -> (BufferedLinkSender<B>, BufferedLinkReceiver<B>) {
	let (tx, rx) = tracing_unbounded("mpsc_buffered_link", queue_size_warning);
	let tx = BufferedLinkSender { tx };
	let rx = BufferedLinkReceiver { rx: rx.fuse() };
	(tx, rx)
}

/// See [`buffered_link`].
pub struct BufferedLinkSender<B: BlockT> {
	tx: TracingUnboundedSender<BlockImportWorkerMsg<B>>,
}

impl<B: BlockT> BufferedLinkSender<B> {
	/// Returns true if the sender points to nowhere.
	///
	/// Once `true` is returned, it is pointless to use the sender anymore.
	pub fn is_closed(&self) -> bool {
		self.tx.is_closed()
	}
}

impl<B: BlockT> Clone for BufferedLinkSender<B> {
	fn clone(&self) -> Self {
		BufferedLinkSender { tx: self.tx.clone() }
	}
}

/// Internal buffered message.
pub enum BlockImportWorkerMsg<B: BlockT> {
	BlocksProcessed(usize, usize, Vec<(BlockImportResult<B>, B::Hash)>),
	JustificationImported(RuntimeOrigin, B::Hash, NumberFor<B>, bool),
	RequestJustification(B::Hash, NumberFor<B>),
}

impl<B: BlockT> Link<B> for BufferedLinkSender<B> {
	fn blocks_processed(
		&mut self,
		imported: usize,
		count: usize,
		results: Vec<(BlockImportResult<B>, B::Hash)>,
	) {
		let _ = self
			.tx
			.unbounded_send(BlockImportWorkerMsg::BlocksProcessed(imported, count, results));
	}

	fn justification_imported(
		&mut self,
		who: RuntimeOrigin,
		hash: &B::Hash,
		number: NumberFor<B>,
		success: bool,
	) {
		let msg = BlockImportWorkerMsg::JustificationImported(who, *hash, number, success);
		let _ = self.tx.unbounded_send(msg);
	}

	fn request_justification(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self
			.tx
			.unbounded_send(BlockImportWorkerMsg::RequestJustification(*hash, number));
	}
}

/// See [`buffered_link`].
pub struct BufferedLinkReceiver<B: BlockT> {
	rx: stream::Fuse<TracingUnboundedReceiver<BlockImportWorkerMsg<B>>>,
}

impl<B: BlockT> BufferedLinkReceiver<B> {
	/// Send action for the synchronization to perform.
	pub fn send_actions(&mut self, msg: BlockImportWorkerMsg<B>, link: &mut dyn Link<B>) {
		match msg {
			BlockImportWorkerMsg::BlocksProcessed(imported, count, results) =>
				link.blocks_processed(imported, count, results),
			BlockImportWorkerMsg::JustificationImported(who, hash, number, success) =>
				link.justification_imported(who, &hash, number, success),
			BlockImportWorkerMsg::RequestJustification(hash, number) =>
				link.request_justification(&hash, number),
		}
	}

	/// Polls for the buffered link actions. Any enqueued action will be propagated to the link
	/// passed as parameter.
	///
	/// This method should behave in a way similar to `Future::poll`. It can register the current
	/// task and notify later when more actions are ready to be polled. To continue the comparison,
	/// it is as if this method always returned `Poll::Pending`.
	///
	/// Returns an error if the corresponding [`BufferedLinkSender`] has been closed.
	pub fn poll_actions(&mut self, cx: &mut Context, link: &mut dyn Link<B>) -> Result<(), ()> {
		loop {
			let msg = match Stream::poll_next(Pin::new(&mut self.rx), cx) {
				Poll::Ready(Some(msg)) => msg,
				Poll::Ready(None) => break Err(()),
				Poll::Pending => break Ok(()),
			};

			self.send_actions(msg, &mut *link);
		}
	}

	/// Poll next element from import queue and send the corresponding action command over the link.
	pub async fn next_action(&mut self, link: &mut dyn Link<B>) -> Result<(), ()> {
		if let Some(msg) = self.rx.next().await {
			self.send_actions(msg, link);
			return Ok(())
		}
		Err(())
	}

	/// Close the channel.
	pub fn close(&mut self) -> bool {
		self.rx.get_mut().close()
	}
}

#[cfg(test)]
mod tests {
	use sp_test_primitives::Block;

	#[test]
	fn is_closed() {
		let (tx, rx) = super::buffered_link::<Block>(1);
		assert!(!tx.is_closed());
		drop(rx);
		assert!(tx.is_closed());
	}
}
