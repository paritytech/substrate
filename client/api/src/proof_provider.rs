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

//! Proof utilities
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT},
};
use crate::{StorageProof, ChangesProof};
use sp_storage::{ChildInfo, StorageKey, PrefixedStorageKey};

/// Interface for providing block proving utilities.
pub trait ProofProvider<Block: BlockT> {
	/// Reads storage value at a given block + key, returning read proof.
	fn read_proof(
		&self,
		id: &BlockId<Block>,
		keys: &mut dyn Iterator<Item=&[u8]>,
	) -> sp_blockchain::Result<StorageProof>;

	/// Reads child storage value at a given block + storage_key + key, returning
	/// read proof.
	fn read_child_proof(
		&self,
		id: &BlockId<Block>,
		child_info: &ChildInfo,
		keys: &mut dyn Iterator<Item=&[u8]>,
	) -> sp_blockchain::Result<StorageProof>;

	/// Execute a call to a contract on top of state in a block of given hash
	/// AND returning execution proof.
	///
	/// No changes are made.
	fn execution_proof(
		&self,
		id: &BlockId<Block>,
		method: &str,
		call_data: &[u8],
	) -> sp_blockchain::Result<(Vec<u8>, StorageProof)>;
	/// Reads given header and generates CHT-based header proof.
	fn header_proof(&self, id: &BlockId<Block>) -> sp_blockchain::Result<(Block::Header, StorageProof)>;

	/// Get proof for computation of (block, extrinsic) pairs where key has been changed at given blocks range.
	/// `min` is the hash of the first block, which changes trie root is known to the requester - when we're using
	/// changes tries from ascendants of this block, we should provide proofs for changes tries roots
	/// `max` is the hash of the last block known to the requester - we can't use changes tries from descendants
	/// of this block.
	/// Works only for runtimes that are supporting changes tries.
	fn key_changes_proof(
		&self,
		first: Block::Hash,
		last: Block::Hash,
		min: Block::Hash,
		max: Block::Hash,
		storage_key: Option<&PrefixedStorageKey>,
		key: &StorageKey,
	) -> sp_blockchain::Result<ChangesProof<Block::Header>>;

	/// Given a `BlockId` iterate over all storage values starting at `start_key` exclusively,
	/// building proofs until size limit is reached. Returns combined proof and the number of collected keys.
	fn read_proof_collection(
		&self,
		id: &BlockId<Block>,
		start_key: &[u8],
		size_limit: usize,
	) -> sp_blockchain::Result<(StorageProof, u32)>;

	/// Given a `BlockId` iterate over all storage values starting at `start_key`.
	/// Returns collected keys and values.
	fn storage_collection(
		&self,
		id: &BlockId<Block>,
		start_key: &[u8],
		size_limit: usize,
	) -> sp_blockchain::Result<Vec<(Vec<u8>, Vec<u8>)>>;

	/// Verify read storage proof for a set of keys.
	/// Returns collected key-value pairs and a flag indicating if iteration is complete.
	fn verify_range_proof(
		&self,
		root: Block::Hash,
		proof: StorageProof,
		start_key: &[u8],
	) -> sp_blockchain::Result<(Vec<(Vec<u8>, Vec<u8>)>, bool)>;
}
