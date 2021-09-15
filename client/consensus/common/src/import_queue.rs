// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Import Queue primitive: something which can verify and import blocks.
//!
//! This serves as an intermediate and abstracted step between synchronization
//! and import. Each mode of consensus will have its own requirements for block
//! verification. Some algorithms can verify in parallel, while others only
//! sequentially.
//!
//! The `ImportQueue` trait allows such verification strategies to be
//! instantiated. The `BasicQueue` and `BasicVerifier` traits allow serial
//! queues to be instantiated simply.

use std::{collections::HashMap, iter::FromIterator};

use log::{debug, trace};
use sp_runtime::{
	traits::{Block as BlockT, Header as _, NumberFor},
	Justifications,
};

use crate::{
	block_import::{
		BlockCheckParams, BlockImport, BlockImportParams, ImportResult, ImportedAux, ImportedState,
		JustificationImport, StateAction,
	},
	metrics::Metrics,
};
pub use basic_queue::BasicQueue;
use sp_consensus::{error::Error as ConsensusError, BlockOrigin, CacheKeyId};

/// A commonly-used Import Queue type.
///
/// This defines the transaction type of the `BasicQueue` to be the transaction type for a client.
pub type DefaultImportQueue<Block, Client> =
	BasicQueue<Block, sp_api::TransactionFor<Client, Block>>;

mod basic_queue;
pub mod buffered_link;

/// Shared block import struct used by the queue.
pub type BoxBlockImport<B, Transaction> =
	Box<dyn BlockImport<B, Error = ConsensusError, Transaction = Transaction> + Send + Sync>;

/// Shared justification import struct used by the queue.
pub type BoxJustificationImport<B> =
	Box<dyn JustificationImport<B, Error = ConsensusError> + Send + Sync>;

/// Maps to the Origin used by the network.
pub type Origin = libp2p::PeerId;

/// Block data used by the queue.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IncomingBlock<B: BlockT> {
	/// Block header hash.
	pub hash: <B as BlockT>::Hash,
	/// Block header if requested.
	pub header: Option<<B as BlockT>::Header>,
	/// Block body if requested.
	pub body: Option<Vec<<B as BlockT>::Extrinsic>>,
	/// Indexed block body if requested.
	pub indexed_body: Option<Vec<Vec<u8>>>,
	/// Justification(s) if requested.
	pub justifications: Option<Justifications>,
	/// The peer, we received this from
	pub origin: Option<Origin>,
	/// Allow importing the block skipping state verification if parent state is missing.
	pub allow_missing_state: bool,
	/// Skip block execution and state verification.
	pub skip_execution: bool,
	/// Re-validate existing block.
	pub import_existing: bool,
	/// Do not compute new state, but rather set it to the given set.
	pub state: Option<ImportedState<B>>,
}

/// Verify a justification of a block
#[async_trait::async_trait]
pub trait Verifier<B: BlockT>: Send + Sync {
	/// Verify the given data and return the BlockImportParams and an optional
	/// new set of validators to import. If not, err with an Error-Message
	/// presented to the User in the logs.
	async fn verify(
		&mut self,
		block: BlockImportParams<B, ()>,
	) -> Result<(BlockImportParams<B, ()>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String>;
}

/// Blocks import queue API.
///
/// The `import_*` methods can be called in order to send elements for the import queue to verify.
/// Afterwards, call `poll_actions` to determine how to respond to these elements.
pub trait ImportQueue<B: BlockT>: Send {
	/// Import bunch of blocks.
	fn import_blocks(&mut self, origin: BlockOrigin, blocks: Vec<IncomingBlock<B>>);
	/// Import block justifications.
	fn import_justifications(
		&mut self,
		who: Origin,
		hash: B::Hash,
		number: NumberFor<B>,
		justifications: Justifications,
	);
	/// Polls for actions to perform on the network.
	///
	/// This method should behave in a way similar to `Future::poll`. It can register the current
	/// task and notify later when more actions are ready to be polled. To continue the comparison,
	/// it is as if this method always returned `Poll::Pending`.
	fn poll_actions(&mut self, cx: &mut futures::task::Context, link: &mut dyn Link<B>);
}

/// Hooks that the verification queue can use to influence the synchronization
/// algorithm.
pub trait Link<B: BlockT>: Send {
	/// Batch of blocks imported, with or without error.
	fn blocks_processed(
		&mut self,
		_imported: usize,
		_count: usize,
		_results: Vec<(BlockImportResult<B>, B::Hash)>,
	) {
	}

	/// Justification import result.
	fn justification_imported(
		&mut self,
		_who: Origin,
		_hash: &B::Hash,
		_number: NumberFor<B>,
		_success: bool,
	) {
	}

	/// Request a justification for the given block.
	fn request_justification(&mut self, _hash: &B::Hash, _number: NumberFor<B>) {}
}

/// Block import successful result.
#[derive(Debug, PartialEq)]
pub enum BlockImportStatus<N: std::fmt::Debug + PartialEq> {
	/// Imported known block.
	ImportedKnown(N, Option<Origin>),
	/// Imported unknown block.
	ImportedUnknown(N, ImportedAux, Option<Origin>),
}

/// Block import error.
#[derive(Debug)]
pub enum BlockImportError {
	/// Block missed header, can't be imported
	IncompleteHeader(Option<Origin>),
	/// Block verification failed, can't be imported
	VerificationFailed(Option<Origin>, String),
	/// Block is known to be Bad
	BadBlock(Option<Origin>),
	/// Parent state is missing.
	MissingState,
	/// Block has an unknown parent
	UnknownParent,
	/// Block import has been cancelled. This can happen if the parent block fails to be imported.
	Cancelled,
	/// Other error.
	Other(ConsensusError),
}

type BlockImportResult<B> = Result<BlockImportStatus<NumberFor<B>>, BlockImportError>;

/// Single block import function.
pub async fn import_single_block<B: BlockT, V: Verifier<B>, Transaction: Send + 'static>(
	import_handle: &mut impl BlockImport<B, Transaction = Transaction, Error = ConsensusError>,
	block_origin: BlockOrigin,
	block: IncomingBlock<B>,
	verifier: &mut V,
) -> BlockImportResult<B> {
	import_single_block_metered(import_handle, block_origin, block, verifier, None).await
}

/// Single block import function with metering.
pub(crate) async fn import_single_block_metered<
	B: BlockT,
	V: Verifier<B>,
	Transaction: Send + 'static,
>(
	import_handle: &mut impl BlockImport<B, Transaction = Transaction, Error = ConsensusError>,
	block_origin: BlockOrigin,
	block: IncomingBlock<B>,
	verifier: &mut V,
	metrics: Option<Metrics>,
) -> BlockImportResult<B> {
	let peer = block.origin;

	let (header, justifications) = match (block.header, block.justifications) {
		(Some(header), justifications) => (header, justifications),
		(None, _) => {
			if let Some(ref peer) = peer {
				debug!(target: "sync", "Header {} was not provided by {} ", block.hash, peer);
			} else {
				debug!(target: "sync", "Header {} was not provided ", block.hash);
			}
			return Err(BlockImportError::IncompleteHeader(peer))
		},
	};

	trace!(target: "sync", "Header {} has {:?} logs", block.hash, header.digest().logs().len());

	let number = header.number().clone();
	let hash = block.hash;
	let parent_hash = header.parent_hash().clone();

	let import_handler = |import| match import {
		Ok(ImportResult::AlreadyInChain) => {
			trace!(target: "sync", "Block already in chain {}: {:?}", number, hash);
			Ok(BlockImportStatus::ImportedKnown(number, peer.clone()))
		},
		Ok(ImportResult::Imported(aux)) =>
			Ok(BlockImportStatus::ImportedUnknown(number, aux, peer.clone())),
		Ok(ImportResult::MissingState) => {
			debug!(target: "sync", "Parent state is missing for {}: {:?}, parent: {:?}",
					number, hash, parent_hash);
			Err(BlockImportError::MissingState)
		},
		Ok(ImportResult::UnknownParent) => {
			debug!(target: "sync", "Block with unknown parent {}: {:?}, parent: {:?}",
					number, hash, parent_hash);
			Err(BlockImportError::UnknownParent)
		},
		Ok(ImportResult::KnownBad) => {
			debug!(target: "sync", "Peer gave us a bad block {}: {:?}", number, hash);
			Err(BlockImportError::BadBlock(peer.clone()))
		},
		Err(e) => {
			debug!(target: "sync", "Error importing block {}: {:?}: {:?}", number, hash, e);
			Err(BlockImportError::Other(e))
		},
	};

	match import_handler(
		import_handle
			.check_block(BlockCheckParams {
				hash,
				number,
				parent_hash,
				allow_missing_state: block.allow_missing_state,
				import_existing: block.import_existing,
				allow_missing_parent: block.state.is_some(),
			})
			.await,
	)? {
		BlockImportStatus::ImportedUnknown { .. } => (),
		r => return Ok(r), // Any other successful result means that the block is already imported.
	}

	let started = std::time::Instant::now();

	let mut import_block = BlockImportParams::new(block_origin, header);
	import_block.body = block.body;
	import_block.justifications = justifications;
	import_block.post_hash = Some(hash);
	import_block.import_existing = block.import_existing;
	import_block.indexed_body = block.indexed_body;

	if let Some(state) = block.state {
		let changes = crate::block_import::StorageChanges::Import(state);
		import_block.state_action = StateAction::ApplyChanges(changes);
	} else if block.skip_execution {
		import_block.state_action = StateAction::Skip;
	} else if block.allow_missing_state {
		import_block.state_action = StateAction::ExecuteIfPossible;
	}

	let (import_block, maybe_keys) = verifier.verify(import_block).await.map_err(|msg| {
		if let Some(ref peer) = peer {
			trace!(target: "sync", "Verifying {}({}) from {} failed: {}", number, hash, peer, msg);
		} else {
			trace!(target: "sync", "Verifying {}({}) failed: {}", number, hash, msg);
		}
		if let Some(metrics) = metrics.as_ref() {
			metrics.report_verification(false, started.elapsed());
		}
		BlockImportError::VerificationFailed(peer.clone(), msg)
	})?;

	if let Some(metrics) = metrics.as_ref() {
		metrics.report_verification(true, started.elapsed());
	}

	let cache = HashMap::from_iter(maybe_keys.unwrap_or_default());
	let import_block = import_block.clear_storage_changes_and_mutate();
	let imported = import_handle.import_block(import_block, cache).await;
	if let Some(metrics) = metrics.as_ref() {
		metrics.report_verification_and_import(started.elapsed());
	}
	import_handler(imported)
}
