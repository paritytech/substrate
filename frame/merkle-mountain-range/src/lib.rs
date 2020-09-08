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

//! # Merkle Mountain Range
//!
//! ## Overview
//!
//! NOTE This pallet is experimental and not proven to work in production.
//!
#![cfg_attr(not(feature = "std"), no_std)]

use codec::Encode;
use frame_support::{
	debug, decl_module, decl_storage, RuntimeDebug,
	dispatch::Parameter,
	weights::Weight,
	traits::Get,
};
use sp_runtime::traits;
use sp_std::{fmt, marker::PhantomData};

mod mmr;
mod primitives;
#[cfg(test)]
mod tests;

/// A provider of the MMR's leaf data.
pub trait LeafDataProvider {
	/// A type that should end up in the leaf of MMR.
	type LeafData: Parameter;

	/// The method to return leaf data that should be placed
	/// in the leaf node appended MMR at this block.
	///
	/// This is being called by the `on_initialize` method of
	/// this pallet at the very beginning of each block.
	/// The second argument should indicate how much `Weight`
	/// was required to retrieve the data.
	fn leaf_data() -> (Self::LeafData, Weight);
}

/// This pallet's configuration trait
pub trait Trait: frame_system::Trait {
	/// A hasher type for MMR.
	///
	/// To construct trie nodes that result in merging (bagging) two peaks, depending on the node
	/// kind we take either:
	/// - The node (hash) itself if it's an inner node.
	/// - The hash of SCALE-encoding of the leaf data if it's a leaf node.
	///
	/// Then we create a tuple of these two hashes, SCALE-encode it (concatenate) and
	/// hash, to obtain a new MMR inner node - the new peak.
	type Hashing: traits::Hash<Output = <Self as Trait>::Hash>;

	/// The hashing output type.
	///
	/// This type is actually going to be stored in the MMR.
	/// Required to be provided again, to satisfy trait bounds for storage items.
	type Hash: traits::Member + traits::MaybeSerializeDeserialize + sp_std::fmt::Debug
		+ sp_std::hash::Hash + AsRef<[u8]> + AsMut<[u8]> + Copy + Default + codec::Codec
		+ codec::EncodeLike;

	/// Data stored in the leaf nodes.
	///
	/// By default every leaf node will always include a (parent) block hash and
	/// any additional `LeafData` defined by this type.
	type LeafData: LeafDataProvider;
}

decl_storage! {
	trait Store for Module<T: Trait> as MerkleMountainRange {
		/// Latest MMR Root hash.
		pub RootHash get(fn mmr_root_hash): <T as Trait>::Hash;

		/// Current size of the MMR (number of leaves).
		pub NumberOfLeaves get(fn mmr_leaves): u64;

		/// Hashes of the nodes in the MMR.
		///
		/// Note this collection only contains MMR peaks, the inner nodes (and leaves)
		/// are pruned and only stored in the Offchain DB.
		pub Nodes get(fn mmr_peak): map hasher(identity) u64 => Option<<T as Trait>::Hash>;

		// TODO [ToDr] Populate initial MMR?
	}
}

decl_module! {
	/// A public part of the pallet.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn on_initialize(n: T::BlockNumber) -> Weight {
			debug::native::info!("Hello World from MMR");

			let hash = <frame_system::Module<T>>::parent_hash();
			let (data, leaf_weight) = T::LeafData::leaf_data();
			let mut mmr = MMR::<T, _>::new(Self::mmr_leaves());
			mmr.push(primitives::Leaf { hash, data })
				.expect("MMR push never fails.");

			// update the size
			let (leaves, root) = mmr.finalize().expect("MMR finalize never fails.");
			<NumberOfLeaves>::put(leaves);
			<RootHash<T>>::put(root);

			let pruned = Self::prune_non_peaks();
			let peaks = mmr::NodesUtils::new(leaves).number_of_peaks();

			leaf_weight + <T as frame_system::Trait>::DbWeight::get().reads_writes(
				2 + peaks,
				2 + peaks + pruned
			)
		}
	}
}

impl<T: Trait> Module<T> {
	/// Returns the number of nodes pruned.
	fn prune_non_peaks() -> u64 {
		debug::native::info!("Pruning MMR of size: {:?}", Self::mmr_leaves());
		// TODO [ToDr] Implement me
		0
	}

	fn offchain_key(pos: u64) -> Vec<u8> {
		// TODO [ToDr] Configurable?
		(b"mmr-", pos).encode()
	}
}

/// A node stored in the MMR.
#[derive(RuntimeDebug, Clone, PartialEq, codec::Encode, codec::Decode)]
pub enum MMRNode<H: traits::Hash, L> {
	Leaf(L),
	Inner(H::Output),
}

/// MMRNode type for runtime `T`.
pub type MMRNodeOf<T, L> = MMRNode<<T as Trait>::Hashing, L>;

/// A wrapper around a MMR library to expose limited functionality that works
/// with non-peak nodes pruned.
pub struct MMR<T: Trait, L: codec::Codec + fmt::Debug> {
	mmr: mmr_lib::MMR<
		MMRNodeOf<T, L>,
		MMRHasher<<T as Trait>::Hashing, L>,
		MMRIndexer<T, L>
	>,
	leaves: u64,
}

impl<T: Trait, L: codec::Codec + PartialEq + fmt::Debug + Clone> MMR<T, L> {
	/// Create a pointer to an existing MMR with given size.
	pub fn new(leaves: u64) -> Self {
		let size = mmr::NodesUtils::new(leaves).size();
		Self {
			mmr: mmr_lib::MMR::new(size, Default::default()),
			leaves,
		}
	}

	/// Push another item to the MMR.
	///
	/// Returns element position (index) in the MMR.
	pub fn push(&mut self, leaf: L) -> Option<u64> {
		let res = self.mmr.push(MMRNode::Leaf(leaf)).map_err(|e| {
			debug::native::error!("Error while pushing MMR node: {:?}", e);
			()
		}).map_err(|e| Error::Push.debug(e)).ok();

		if res.is_some() {
			self.leaves += 1;
		}

		res
	}

	/// Return the internal size of the MMR (number of nodes).
	#[cfg(test)]
	pub fn size(&self) -> u64 {
		self.mmr.mmr_size()
	}

	/// Commit the changes to underlying storage and calculate MMR's size & root hash.
	pub fn finalize(self) -> Result<(u64, <T as Trait>::Hash), Error> {
		let root = self.mmr.get_root().map_err(|e| Error::GetRoot.debug(e))?;
		self.mmr.commit().map_err(|e| Error::Commit.debug(e))?;
		Ok((self.leaves, root.hash()))
	}
}

/// Error during MMR
#[derive(RuntimeDebug)]
pub enum Error {
	Push,
	GetRoot,
	Commit
}

impl Error {
	/// Replace given error `e` with `self` and generate a log entry with error details.
	pub(crate) fn debug(self, e: impl fmt::Debug) -> Self {
		debug::native::error!("[{:?}] MMR error: {:?}", self, e);
		self
	}
}

impl<H: traits::Hash, L: codec::Encode> MMRNode<H, L> {
	/// Retrieve a hash of the node.
	///
	/// Depending on the node type it's going to either be a contained value for `Inner` node,
	/// or a hash of SCALE-encoded `Leaf` data.
	pub fn hash(&self) -> H::Output {
		match *self {
			MMRNode::Leaf(ref leaf) => H::hash_of(leaf),
			MMRNode::Inner(ref hash) => hash.clone(),
		}
	}
}

/// A storage layer for MMR.
pub struct MMRIndexer<T, L>(PhantomData<(T, L)>);

impl<T, L> Default for MMRIndexer<T, L> {
	fn default() -> Self {
		Self(Default::default())
	}
}

impl<T: Trait, L: codec::Codec + fmt::Debug> mmr_lib::MMRStore<MMRNodeOf<T, L>> for MMRIndexer<T, L> {
	fn get_elem(&self, pos: u64) -> mmr_lib::Result<Option<MMRNodeOf<T, L>>> {
		Ok(<Nodes<T>>::get(pos)
			.map(MMRNode::Inner)
		)
	}

	fn append(&mut self, pos: u64, elems: Vec<MMRNodeOf<T, L>>) -> mmr_lib::Result<()> {
		let mut leaves = NumberOfLeaves::get();
		let mut size = mmr::NodesUtils::new(leaves).size();
		if pos != size {
			return Err(mmr_lib::Error::InconsistentStore);
		}

		for elem in elems {
			<Nodes<T>>::insert(size, elem.hash());
			// Indexing API used to store the full leaf content.
			elem.using_encoded(|elem| {
				sp_io::offchain_index::set(&Module::<T>::offchain_key(size), elem)
			});
			size += 1;

			if let MMRNode::Leaf(..) = elem {
				leaves += 1;
			}
		}

		NumberOfLeaves::put(leaves);

		Ok(())
	}
}

/// Hasher type for MMR.
pub struct MMRHasher<H, L>(PhantomData<(H, L)>);

impl<H: traits::Hash, L: codec::Codec> mmr_lib::Merge for MMRHasher<H, L> {
	type Item = MMRNode<H, L>;

	fn merge(left: &Self::Item, right: &Self::Item) -> Self::Item {
		MMRNode::Inner(H::hash_of(&(left.hash(), right.hash())))
	}
}

