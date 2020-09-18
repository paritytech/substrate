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

use frame_support::RuntimeDebug;
use sp_runtime::traits;

pub use self::mmr::{MMR, Error};

/// Node type for runtime `T`.
pub type NodeOf<T, L> = Node<<T as crate::Trait>::Hashing, L>;

/// Hasher type for MMR.
pub struct Hasher<H, L>(sp_std::marker::PhantomData<(H, L)>);

impl<H: traits::Hash, L: codec::Codec> mmr_lib::Merge for Hasher<H, L> {
	type Item = Node<H, L>;

	fn merge(left: &Self::Item, right: &Self::Item) -> Self::Item {
		Node::Inner(H::hash_of(&(left.hash(), right.hash())))
	}
}

/// A node stored in the MMR.
#[derive(RuntimeDebug, Clone, PartialEq, codec::Encode, codec::Decode)]
pub enum Node<H: traits::Hash, L> {
	Leaf(L),
	Inner(H::Output),
}

impl<H: traits::Hash, L: codec::Encode> Node<H, L> {
	/// Retrieve a hash of the node.
	///
	/// Depending on the node type it's going to either be a contained value for `Inner` node,
	/// or a hash of SCALE-encoded `Leaf` data.
	pub fn hash(&self) -> H::Output {
		match *self {
			Node::Leaf(ref leaf) => H::hash_of(leaf),
			Node::Inner(ref hash) => hash.clone(),
		}
	}
}
