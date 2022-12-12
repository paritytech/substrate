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

use libp2p::PeerId;
use sc_consensus::{BlockImportError, BlockImportStatus, JustificationSyncLink, Link};
use sc_network_common::service::NetworkSyncForkRequest;
use sc_utils::mpsc::TracingUnboundedSender;
use sp_runtime::traits::{Block as BlockT, NumberFor};

/// Commands send to `ChainSync`
#[derive(Debug)]
pub enum ToServiceCommand<B: BlockT> {
	SetSyncForkRequest(Vec<PeerId>, B::Hash, NumberFor<B>),
	RequestJustification(B::Hash, NumberFor<B>),
	ClearJustificationRequests,
	BlocksProcessed(
		usize,
		usize,
		Vec<(Result<BlockImportStatus<NumberFor<B>>, BlockImportError>, B::Hash)>,
	),
	JustificationImported(PeerId, B::Hash, NumberFor<B>, bool),
}

/// Handle for communicating with `ChainSync` asynchronously
#[derive(Clone)]
pub struct ChainSyncInterfaceHandle<B: BlockT> {
	tx: TracingUnboundedSender<ToServiceCommand<B>>,
}

impl<B: BlockT> ChainSyncInterfaceHandle<B> {
	/// Create new handle
	pub fn new(tx: TracingUnboundedSender<ToServiceCommand<B>>) -> Self {
		Self { tx }
	}
}

impl<B: BlockT + 'static> NetworkSyncForkRequest<B::Hash, NumberFor<B>>
	for ChainSyncInterfaceHandle<B>
{
	/// Configure an explicit fork sync request.
	///
	/// Note that this function should not be used for recent blocks.
	/// Sync should be able to download all the recent forks normally.
	/// `set_sync_fork_request` should only be used if external code detects that there's
	/// a stale fork missing.
	///
	/// Passing empty `peers` set effectively removes the sync request.
	fn set_sync_fork_request(&self, peers: Vec<PeerId>, hash: B::Hash, number: NumberFor<B>) {
		let _ = self
			.tx
			.unbounded_send(ToServiceCommand::SetSyncForkRequest(peers, hash, number));
	}
}

impl<B: BlockT> JustificationSyncLink<B> for ChainSyncInterfaceHandle<B> {
	/// Request a justification for the given block from the network.
	///
	/// On success, the justification will be passed to the import queue that was part at
	/// initialization as part of the configuration.
	fn request_justification(&self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self.tx.unbounded_send(ToServiceCommand::RequestJustification(*hash, number));
	}

	fn clear_justification_requests(&self) {
		let _ = self.tx.unbounded_send(ToServiceCommand::ClearJustificationRequests);
	}
}

impl<B: BlockT> Link<B> for ChainSyncInterfaceHandle<B> {
	fn blocks_processed(
		&mut self,
		imported: usize,
		count: usize,
		results: Vec<(Result<BlockImportStatus<NumberFor<B>>, BlockImportError>, B::Hash)>,
	) {
		let _ = self
			.tx
			.unbounded_send(ToServiceCommand::BlocksProcessed(imported, count, results));
	}

	fn justification_imported(
		&mut self,
		who: PeerId,
		hash: &B::Hash,
		number: NumberFor<B>,
		success: bool,
	) {
		let _ = self
			.tx
			.unbounded_send(ToServiceCommand::JustificationImported(who, *hash, number, success));
	}

	fn request_justification(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		let _ = self.tx.unbounded_send(ToServiceCommand::RequestJustification(*hash, number));
	}
}
