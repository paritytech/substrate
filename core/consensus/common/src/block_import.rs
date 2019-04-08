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

//! Block import helpers.

use runtime_primitives::traits::{Block as BlockT, DigestItemFor, Header as HeaderT, NumberFor};
use runtime_primitives::Justification;
use std::borrow::Cow;
use std::collections::HashMap;
use crate::well_known_cache_keys;

/// Block import result.
#[derive(Debug, PartialEq, Eq)]
pub enum ImportResult {
	/// Block imported.
	Imported(ImportedAux),
	/// Already in the blockchain.
	AlreadyInChain,
	/// Block or parent is known to be bad.
	KnownBad,
	/// Block parent is not in the chain.
	UnknownParent,
}

/// Auxiliary data associated with an imported block result.
#[derive(Debug, PartialEq, Eq)]
pub struct ImportedAux {
	/// Clear all pending justification requests.
	pub clear_justification_requests: bool,
	/// Request a justification for the given block.
	pub needs_justification: bool,
	/// Received a bad justification.
	pub bad_justification: bool,
}

impl Default for ImportedAux {
	fn default() -> ImportedAux {
		ImportedAux {
			clear_justification_requests: false,
			needs_justification: false,
			bad_justification: false,
		}
	}
}

impl ImportResult {
	/// Returns default value for `ImportResult::Imported` with both
	/// `clear_justification_requests` and `needs_justification` set to false.
	pub fn imported() -> ImportResult {
		ImportResult::Imported(ImportedAux::default())
	}
}

/// Block data origin.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BlockOrigin {
	/// Genesis block built into the client.
	Genesis,
	/// Block is part of the initial sync with the network.
	NetworkInitialSync,
	/// Block was broadcasted on the network.
	NetworkBroadcast,
	/// Block that was received from the network and validated in the consensus process.
	ConsensusBroadcast,
	/// Block that was collated by this node.
	Own,
	/// Block was imported from a file.
	File,
}

/// Fork choice strategy.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ForkChoiceStrategy {
	/// Longest chain fork choice.
	LongestChain,
	/// Custom fork choice rule, where true indicates the new block should be the best block.
	Custom(bool),
}

/// Data required to import a Block
pub struct ImportBlock<Block: BlockT> {
	/// Origin of the Block
	pub origin: BlockOrigin,
	/// The header, without consensus post-digests applied. This should be in the same
	/// state as it comes out of the runtime.
	///
	/// Consensus engines which alter the header (by adding post-runtime digests)
	/// should strip those off in the initial verification process and pass them
	/// via the `post_digests` field. During block authorship, they should
	/// not be pushed to the header directly.
	///
	/// The reason for this distinction is so the header can be directly
	/// re-executed in a runtime that checks digest equivalence -- the
	/// post-runtime digests are pushed back on after.
	pub header: Block::Header,
	/// Justification provided for this block from the outside.
	pub justification: Option<Justification>,
	/// Digest items that have been added after the runtime for external
	/// work, like a consensus signature.
	pub post_digests: Vec<DigestItemFor<Block>>,
	/// Block's body
	pub body: Option<Vec<Block::Extrinsic>>,
	/// Is this block finalized already?
	/// `true` implies instant finality.
	pub finalized: bool,
	/// Auxiliary consensus data produced by the block.
	/// Contains a list of key-value pairs. If values are `None`, the keys
	/// will be deleted.
	pub auxiliary: Vec<(Vec<u8>, Option<Vec<u8>>)>,
	/// Fork choice strategy of this import.
	pub fork_choice: ForkChoiceStrategy,
}

impl<Block: BlockT> ImportBlock<Block> {
	/// Deconstruct the justified header into parts.
	pub fn into_inner(self)
		-> (
			BlockOrigin,
			<Block as BlockT>::Header,
			Option<Justification>,
			Vec<DigestItemFor<Block>>,
			Option<Vec<<Block as BlockT>::Extrinsic>>,
			bool,
			Vec<(Vec<u8>, Option<Vec<u8>>)>,
		) {
		(
			self.origin,
			self.header,
			self.justification,
			self.post_digests,
			self.body,
			self.finalized,
			self.auxiliary,
		)
	}

	/// Get a handle to full header (with post-digests applied).
	pub fn post_header(&self) -> Cow<Block::Header> {
		use runtime_primitives::traits::Digest;

		if self.post_digests.is_empty() {
			Cow::Borrowed(&self.header)
		} else {
			Cow::Owned({
				let mut hdr = self.header.clone();
				for digest_item in &self.post_digests {
					hdr.digest_mut().push(digest_item.clone());
				}

				hdr
			})
		}
	}
}

/// Block import trait.
pub trait BlockImport<B: BlockT> {
	type Error: ::std::error::Error + Send + 'static;

	/// Check block preconditions.
	fn check_block(
		&self,
		hash: B::Hash,
		parent_hash: B::Hash,
	) -> Result<ImportResult, Self::Error>;

	/// Import a block.
	///
	/// Cached data can be accessed through the blockchain cache.
	fn import_block(
		&self,
		block: ImportBlock<B>,
		cache: HashMap<well_known_cache_keys::Id, Vec<u8>>,
	) -> Result<ImportResult, Self::Error>;
}

/// Justification import trait
pub trait JustificationImport<B: BlockT> {
	type Error: ::std::error::Error + Send + 'static;

	/// Called by the import queue when it is started.
	fn on_start(&self, _link: &crate::import_queue::Link<B>) { }

	/// Import a Block justification and finalize the given block.
	fn import_justification(
		&self,
		hash: B::Hash,
		number: NumberFor<B>,
		justification: Justification,
	) -> Result<(), Self::Error>;
}
