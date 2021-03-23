// This file is part of Substrate.

// Copyright (C) 2021-2021 Parity Technologies (UK) Ltd.
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

//! Api related to snapshot export and import.

use sp_runtime::traits::{NumberFor, Block as BlockT};
use crate::DatabaseError;
use codec::{Encode, Decode};


#[derive(Clone, Debug, Encode, Decode)]
/// Different storage mode.
pub enum SnapshotDBMode {
	/// Do not apply binary diff between consecutive values.
	NoDiff,
	/// Use xdelta3 VcDiff.
	Xdelta3Diff,
}

impl Default for SnapshotDBMode {
	fn default() -> Self {
		SnapshotDBMode::NoDiff
	}
}

/// Snapshot configuration.
#[derive(Clone, Debug)]
pub struct SnapshotConfig<B: BlockT> {
	/// Number to start from.
	pub from: NumberFor<B>,

	/// Hash to start from.
	pub from_hash: B::Hash,

	/// Number of max block.
	pub to: NumberFor<B>,

	/// Hash of block to snapshot.
	pub to_hash: B::Hash,
}

/// A state visitor implementation for a given backend at a given block.
pub struct StateVisitor<'a, B: BlockT, BA>(pub &'a BA, pub &'a B::Hash);

impl<'a, B, BA> StateVisitor<'a, B, BA>
	where
		B: BlockT,
		BA: crate::backend::Backend<B>,
{
	/// Visit with call back taking the child trie root path and related key values for arguments.
	///
	/// The ordered is required to be top trie then child trie by prefixed storage key order, with
	/// every trie key values consecutively ordered.
	pub fn state_visit(
		&self,
		mut visitor: impl FnMut(Option<&[u8]>, Vec<u8>, Vec<u8>) -> std::result::Result<(), DatabaseError>,
	) -> std::result::Result<(), DatabaseError> {
		let mut state = self.0.state_at(sp_runtime::generic::BlockId::Hash(self.1.clone()))
			.map_err(|e| DatabaseError(Box::new(e)))?;
		use sp_state_machine::Backend;
		let trie_state = state.as_trie_backend().expect("Snapshot runing on a trie backend.");

		let mut prev_child = None;
		let prev_child = &mut prev_child;
		let mut prefixed_storage_key = None;
		let prefixed_storage_key = &mut prefixed_storage_key;
		trie_state.for_key_values(|child, key, value| {
			if child != prev_child.as_ref() {
				*prefixed_storage_key = child.map(|ci| ci.prefixed_storage_key().into_inner());
				*prev_child = child.cloned();
			}
			visitor(
				prefixed_storage_key.as_ref().map(Vec::as_slice),
				key,
				value,
			).expect("Failure adding value to snapshot db.");
		}).map_err(|e| {
			let error: String = e.into();
			DatabaseError(Box::new(sp_blockchain::Error::Backend(error)))
		})?;
		Ok(())
	}
}
