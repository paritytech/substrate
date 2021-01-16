// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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
	Config, HashingOf, Instance,
	mmr::{
		Node, NodeOf, Hasher,
		storage::{Storage, OffchainStorage, RuntimeStorage},
		utils::NodesUtils,
	},
	primitives,
};
use frame_support::{debug, RuntimeDebug};
use sp_std::fmt;
#[cfg(not(feature = "std"))]
use sp_std::{vec, prelude::Vec};

/// A wrapper around a MMR library to expose limited functionality.
///
/// Available functions depend on the storage kind ([Runtime](crate::mmr::storage::RuntimeStorage)
/// vs [Off-chain](crate::mmr::storage::OffchainStorage)).
pub struct Mmr<StorageType, T, I, L> where
	T: Config<I>,
	I: Instance,
	L: primitives::FullLeaf,
	Storage<StorageType, T, I, L>: mmr_lib::MMRStore<NodeOf<T, I, L>>,
{
	mmr: mmr_lib::MMR<
		NodeOf<T, I, L>,
		Hasher<HashingOf<T, I>, L>,
		Storage<StorageType, T, I, L>
	>,
	leaves: u64,
}

impl<StorageType, T, I, L> Mmr<StorageType, T, I, L> where
	T: Config<I>,
	I: Instance,
	L: primitives::FullLeaf,
	Storage<StorageType, T, I, L>: mmr_lib::MMRStore<NodeOf<T, I, L>>,
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
		proof: primitives::Proof<<T as Config<I>>::Hash>,
	) -> Result<bool, Error> {
		let p = mmr_lib::MerkleProof::<
			NodeOf<T, I, L>,
			Hasher<HashingOf<T, I>, L>,
		>::new(
			self.mmr.mmr_size(),
			proof.items.into_iter().map(Node::Hash).collect(),
		);
		let position = mmr_lib::leaf_index_to_pos(proof.leaf_index);
		let root = self.mmr.get_root().map_err(|e| Error::GetRoot.log_error(e))?;
		p.verify(
			root,
			vec![(position, Node::Data(leaf))],
		).map_err(|e| Error::Verify.log_debug(e))
	}

	/// Return the internal size of the MMR (number of nodes).
	#[cfg(test)]
	pub fn size(&self) -> u64 {
		self.mmr.mmr_size()
	}
}

/// Runtime specific MMR functions.
impl<T, I, L> Mmr<RuntimeStorage, T, I, L> where
	T: Config<I>,
	I: Instance,
	L: primitives::FullLeaf,
{

	/// Push another item to the MMR.
	///
	/// Returns element position (index) in the MMR.
	pub fn push(&mut self, leaf: L) -> Option<u64> {
		let position = self.mmr.push(Node::Data(leaf))
			.map_err(|e| Error::Push.log_error(e))
			.ok()?;

		self.leaves += 1;

		Some(position)
	}

	/// Commit the changes to underlying storage, return current number of leaves and
	/// calculate the new MMR's root hash.
	pub fn finalize(self) -> Result<(u64, <T as Config<I>>::Hash), Error> {
		let root = self.mmr.get_root().map_err(|e| Error::GetRoot.log_error(e))?;
		self.mmr.commit().map_err(|e| Error::Commit.log_error(e))?;
		Ok((self.leaves, root.hash()))
	}
}

/// Off-chain specific MMR functions.
impl<T, I, L> Mmr<OffchainStorage, T, I, L> where
	T: Config<I>,
	I: Instance,
	L: primitives::FullLeaf,
{
	/// Generate a proof for given leaf index.
	///
	/// Proof generation requires all the nodes (or their hashes) to be available in the storage.
	/// (i.e. you can't run the function in the pruned storage).
	pub fn generate_proof(&self, leaf_index: u64) -> Result<
		(L, primitives::Proof<<T as Config<I>>::Hash>),
		Error
	> {
		let position = mmr_lib::leaf_index_to_pos(leaf_index);
		let store = <Storage<OffchainStorage, T, I, L>>::default();
		let leaf = match mmr_lib::MMRStore::get_elem(&store, position) {
			Ok(Some(Node::Data(leaf))) => leaf,
			e => return Err(Error::LeafNotFound.log_debug(e)),
		};
		let leaf_count = self.leaves;
		self.mmr.gen_proof(vec![position])
			.map_err(|e| Error::GenerateProof.log_error(e))
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
	/// Consume given error `e` with `self` and generate a native log entry with error details.
	pub(crate) fn log_error(self, e: impl fmt::Debug) -> Self {
		debug::native::error!("[{:?}] MMR error: {:?}", self, e);
		self
	}

	/// Consume given error `e` with `self` and generate a native log entry with error details.
	pub(crate) fn log_debug(self, e: impl fmt::Debug) -> Self {
		debug::native::debug!("[{:?}] MMR error: {:?}", self, e);
		self
	}

}

