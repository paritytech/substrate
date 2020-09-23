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

use frame_support::{
	RuntimeDebug,
	dispatch::Parameter,
	traits::Get,
	weights::Weight,
};
use sp_runtime::traits;

/// A SCALE-encodable object with hashing customisation.
///
/// This type is automatically implemented for any type that implements
/// [frame_support::dispatch::Parameter] so usually you don't have to care about it.
///
/// The point of the trait is to allow better composition of multiple [LeafDataProvider]s,
/// for efficient proving. See [LeafTuple] implementation for details.
pub trait LeafData<H: traits::Hash>: codec::Decode + sp_std::fmt::Debug + PartialEq + Clone {
	type Data: Parameter;

	/// Get the hash of the object.
	fn hash(&self) -> H::Output {
		H::hash_of(self.data())
	}

	fn data(&self) -> &Self::Data;
}

impl<H: traits::Hash, T: Parameter> LeafData<H> for T {
	type Data = T;

	fn data(&self) -> &Self::Data { self }
}

/// A provider of the MMR's leaf data.
pub trait LeafDataProvider<H: traits::Hash> {
	/// A type that should end up in the leaf of MMR.
	type LeafData: LeafData<H>;

	/// The method to return leaf data that should be placed
	/// in the leaf node appended MMR at this block.
	///
	/// This is being called by the `on_initialize` method of
	/// this pallet at the very beginning of each block.
	/// The second return value should indicate how much [Weight]
	/// was required to retrieve the data.
	fn leaf_data() -> (Self::LeafData, Weight);
}

impl<H: traits::Hash> LeafDataProvider<H> for () {
	type LeafData = ();

	fn leaf_data() -> (Self::LeafData, Weight) {
		((), 0)
	}
}

impl<T: frame_system::Trait + crate::Trait> LeafDataProvider<crate::HashingOf<T>> for frame_system::Module<T> {
	type LeafData = <T as frame_system::Trait>::Hash;

	fn leaf_data() -> (Self::LeafData, Weight) {
		let hash = Self::parent_hash();
		(hash, T::DbWeight::get().reads(1))
	}
}

impl<A, B, H> LeafData<H> for (A, B) where
	A: codec::Encode,
	B: codec::Encode,
	H: traits::Hash,
{
	fn hash(&self) -> H::Output {
		(self.0.hash(), self.1.hash())
	}
}


// TODO [ToDr] Impl for all tuples
impl<A, B, H> LeafDataProvider<H> for (A, B) where
	A: LeafDataProvider<H>,
	B: LeafDataProvider<H>,
	H: traits::Hash,
{
	type LeafData = (A::LeafData, B::LeafData);

	fn leaf_data() -> (Self::LeafData, Weight) {
		let (a_leaf, a_weight) = A::leaf_data();
		let (b_leaf, b_weight) = B::leaf_data();

		(LeafTuple::new((a_leaf, b_leaf)), a_weight.saturating_add(b_weight))
	}
}

/// A MMR proof data for one of the leaves.
#[derive(codec::Encode, codec::Decode, RuntimeDebug, Clone, PartialEq, Eq)]
pub struct Proof<Hash> {
	/// The index of the leaf the proof is for.
	pub leaf_index: u64,
	/// Number of leaves in MMR, when the proof was generated.
	pub leaf_count: u64,
	/// Proof elements (hashes of inner nodes on the path to the leaf).
	pub items: Vec<Hash>,
}

