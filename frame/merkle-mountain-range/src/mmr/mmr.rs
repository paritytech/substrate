// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{
	Trait, HashingOf,
	mmr::{
		Node, NodeOf, Hasher,
		storage::{Storage, OffchainStorage, RuntimeStorage},
		utils::NodesUtils,
	},
	primitives,
};
use frame_support::{debug, RuntimeDebug};
use sp_std::fmt;

/// A wrapper around a MMR library to expose limited functionality.
///
/// Available functions depend on the storage kind ([Runtime](crate::mmr::storage::RuntimeStorage)
/// vs [Off-chain](crate::mmr::storage::OffchainStorage)).
pub struct MMR<StorageType, T, L> where
	T: Trait,
	L: primitives::LeafData<HashingOf<T>>,
	Storage<StorageType, T, L>: mmr_lib::MMRStore<NodeOf<T, L>>,
{
	mmr: mmr_lib::MMR<
		NodeOf<T, L>,
		Hasher<<T as Trait>::Hashing, L>,
		Storage<StorageType, T, L>
	>,
	leaves: u64,
}

impl<StorageType, T, L> MMR<StorageType, T, L> where
	T: Trait,
	L: primitives::LeafData<HashingOf<T>>,
	Storage<StorageType, T, L>: mmr_lib::MMRStore<NodeOf<T, L>>,
{
	/// Create a pointer to an existing MMR with given number of leaves.
	pub fn new(leaves: u64) -> Self {
		let size = NodesUtils::new(leaves).size();
		Self {
			mmr: mmr_lib::MMR::new(size, Default::default()),
			leaves,
		}
	}

	/// Verify proof of a single leaf.
	pub fn verify_leaf_proof(
		&self,
		leaf: L,
		proof: primitives::Proof<<T as Trait>::Hash>,
	) -> Result<bool, Error> {
		let p = mmr_lib::MerkleProof::<
			NodeOf<T, L>,
			Hasher<<T as Trait>::Hashing, L>,
		>::new(
			self.mmr.mmr_size(),
			proof.items.into_iter().map(Node::Inner).collect(),
		);
		let position = mmr_lib::leaf_index_to_pos(proof.leaf_index);
		let root = self.mmr.get_root().map_err(|e| Error::GetRoot.debug(e))?;
		p.verify(
			root,
			vec![(position, Node::Leaf(leaf))],
		).map_err(|e| Error::Verify.debug(e))
	}

	/// Return the internal size of the MMR (number of nodes).
	#[cfg(test)]
	pub fn size(&self) -> u64 {
		self.mmr.mmr_size()
	}
}

/// Runtime specific MMR functions.
impl<T, L> MMR<RuntimeStorage, T, L> where
	T: Trait,
	L: primitives::LeafData<HashingOf<T>>,
{
	/// Push another item to the MMR.
	///
	/// Returns element position (index) in the MMR.
	pub fn push(&mut self, leaf: L) -> Option<u64> {
		let res = self.mmr.push(Node::Leaf(leaf)).map_err(|e| {
			debug::native::error!("Error while pushing MMR node: {:?}", e);
			()
		}).map_err(|e| Error::Push.debug(e)).ok();

		if res.is_some() {
			self.leaves += 1;
		}

		res
	}

	/// Commit the changes to underlying storage, return current number of leaves and
	/// calculate the new MMR's root hash.
	pub fn finalize(self) -> Result<(u64, <T as Trait>::Hash), Error> {
		let root = self.mmr.get_root().map_err(|e| Error::GetRoot.debug(e))?;
		self.mmr.commit().map_err(|e| Error::Commit.debug(e))?;
		Ok((self.leaves, root.hash()))
	}
}

/// Off-chain specific MMR functions.
impl<T, L> MMR<OffchainStorage, T, L> where
	T: Trait,
	L: primitives::LeafData<HashingOf<T>>,
{
	/// Generate a proof for given leaf index.
	///
	/// Proof generation requires all the nodes (or their hashes) to be available in the storage.
	/// (i.e. you can't run the function in the pruned storage).
	pub fn generate_proof(&self, leaf_index: u64) -> Result<
		(L, primitives::Proof<<T as Trait>::Hash>),
		Error
	> {
		let position = mmr_lib::leaf_index_to_pos(leaf_index);
		let store = <Storage<OffchainStorage, T, L>>::default();
		let leaf = match mmr_lib::MMRStore::get_elem(&store, position) {
			Ok(Some(Node::Leaf(leaf))) => leaf,
			e => return Err(Error::LeafNotFound.debug(e)),
		};
		let leaf_count = self.leaves;
		self.mmr.gen_proof(vec![position])
			.map_err(|e| Error::GenerateProof.debug(e))
			.map(|p| primitives::Proof {
				leaf_index,
				leaf_count,
				items: p.proof_items().iter().map(|x| x.hash()).collect(),
			})
			.map(|p| (leaf, p))
	}
}

/// Merkle Mountain Range operation error.
#[derive(RuntimeDebug)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub enum Error {
	/// Error while pushing new node.
	Push,
	/// Error getting the new root.
	GetRoot,
	/// Error commiting changes.
	Commit,
	/// Error during proof generation.
	GenerateProof,
	/// Proof verification error.
	Verify,
	/// Leaf not found in the storage.
	LeafNotFound,
}

impl Error {
	/// Replace given error `e` with `self` and generate a log entry with error details.
	pub(crate) fn debug(self, e: impl fmt::Debug) -> Self {
		debug::native::error!("[{:?}] MMR error: {:?}", self, e);
		self
	}
}

