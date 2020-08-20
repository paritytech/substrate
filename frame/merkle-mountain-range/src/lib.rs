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

use codec::{Encode, Decode};
use frame_support::{
	debug, decl_module, decl_storage,
	dispatch::Parameter,
	weights::Weight,
};
use sp_runtime::traits;
use sp_std::marker::PhantomData;

mod primitives;
#[cfg(test)]
mod tests;

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
	type Hashing: traits::Hash;

	/// Data stored in the leaf nodes.
	///
	/// By default every leaf node will always include a (parent) block hash and
	/// any additional `LeafData` defined by this type.
	type LeafData: Parameter;
}

decl_storage! {
	trait Store for Module<T: Trait> as MerkleMountainRange {
	}
}

decl_module! {
	/// A public part of the pallet.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn on_initialize(block_number: T::BlockNumber) -> Weight {
			debug::native::info!("Hello World from MMR");
			todo!()
		}
	}
}

impl<T: Trait> Module<T> {
}

#[derive(Debug, codec::Encode, codec::Decode)]
pub enum MMRNode<H: traits::Hash, L> {
	Leaf(L),
	Inner(H::Output),
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
pub struct MMRIndexer<H, L>(PhantomData<(H, L)>);

impl<H: traits::Hash, L: codec::Codec> mmr::MMRStore<MMRNode<H, L>> for MMRIndexer<H, L> {
	fn get_elem(&self, pos: u64) -> mmr::Result<Option<MMRNode<H, L>>> {
		todo!()
	}
	fn append(&mut self, pos: u64, elems: Vec<MMRNode<H, L>>) -> mmr::Result<()> {
		todo!()
	}
}

/// Hasher type for MMR.
pub struct MMRHasher<H, L>(PhantomData<(H, L)>);

impl<H: traits::Hash, L: codec::Codec> mmr::Merge for MMRHasher<H, L> {
	type Item = MMRNode<H, L>;

	fn merge(left: &Self::Item, right: &Self::Item) -> Self::Item {
		MMRNode::Inner(H::hash_of(&(left.hash(), right.hash())))
	}
}

