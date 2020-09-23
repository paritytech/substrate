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

pub mod storage;
pub mod utils;
mod mmr;

use crate::primitives::LeafData;
use frame_support::RuntimeDebug;
use sp_runtime::traits;

pub use self::mmr::{MMR, Error};

/// Node type for runtime `T`.
pub type NodeOf<T, L> = Node<<T as crate::Trait>::Hashing, L>;

/// Default Merging & Hashing behavior for MMR.
pub struct Hasher<H, L>(sp_std::marker::PhantomData<(H, L)>);

impl<H: traits::Hash, L: LeafData<H>> mmr_lib::Merge for Hasher<H, L> {
	type Item = Node<H, L>;

	fn merge(left: &Self::Item, right: &Self::Item) -> Self::Item {
		Node::Inner(H::hash_of(&(left.hash(), right.hash())))
	}
}

// TODO Rename to DataOrHash

/// A node stored in the MMR.
#[derive(RuntimeDebug, Clone, PartialEq, codec::Decode)]
pub enum Node<H: traits::Hash, L: LeafData<H>> {
	/// A terminal leaf node, storing arbitrary content.
	Leaf(L),
	/// An inner node - always just a hash.
	Inner(H::Output),
}

impl<H: traits::Hash, L: LeafData<H>> codec::Encode for Node<H, L> {
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		match *self {
			Node::Leaf(ref leaf) => leaf.data().using_encoded(f),
			Node::Inner(ref hash) => hash.using_encoded(f),
		}
	}
}

impl<H: traits::Hash, L: LeafData<H>> Node<H, L> {
	/// Retrieve a hash of the node.
	///
	/// Depending on the node type it's going to either be a contained value for [Node::Inner]
	/// node, or a hash of SCALE-encoded [Node::Leaf] data.
	pub fn hash(&self) -> H::Output {
		match *self {
			Node::Leaf(ref leaf) => leaf.hash(),
			Node::Inner(ref hash) => hash.clone(),
		}
	}
}

impl<H: traits::Hash, L: LeafData<H>> LeafData<H> for Node<H, L> {
	type Data = L;

	fn hash(&self) -> H::Output {
		Node::hash(self)
	}

	fn data(&self) ->
}
