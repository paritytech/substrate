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
	traits::Get,
	weights::Weight,
};
use sp_runtime::traits;
use sp_std::fmt;

/// A full leaf content stored in the offchain-db.
pub trait FullLeaf: Clone + PartialEq + fmt::Debug + codec::Decode {
	/// Encode the leaf either in it's full or compact form.
	///
	/// NOTE the encoding returned here MUST be `Decode`able into `FullLeaf`.
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F, compact: bool) -> R;
}

impl<T: codec::Encode + codec::Decode + Clone + PartialEq + fmt::Debug> FullLeaf for T {
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F, _compact: bool) -> R {
		codec::Encode::using_encoded(self,f )
	}
}

/// A provider of the MMR's leaf data.
pub trait LeafDataProvider {
	/// A type that should end up in the leaf of MMR.
	type LeafData: FullLeaf;

	/// The method to return leaf data that should be placed
	/// in the leaf node appended MMR at this block.
	///
	/// This is being called by the `on_initialize` method of
	/// this pallet at the very beginning of each block.
	/// The second return value should indicate how much [Weight]
	/// was required to retrieve the data.
	fn leaf_data() -> (Self::LeafData, Weight);
}

impl LeafDataProvider for () {
	type LeafData = ();

	fn leaf_data() -> (Self::LeafData, Weight) {
		((), 0)
	}
}

impl<T: frame_system::Trait + crate::Trait> LeafDataProvider for frame_system::Module<T> {
	type LeafData = <T as frame_system::Trait>::Hash;

	fn leaf_data() -> (Self::LeafData, Weight) {
		let hash = Self::parent_hash();
		(hash, T::DbWeight::get().reads(1))
	}
}

/// A node stored in the MMR.
#[derive(RuntimeDebug, Clone, PartialEq)]
pub enum DataOrHash<H: traits::Hash, L> {
	/// A terminal leaf node, storing arbitrary content.
	Data(L),
	/// An inner node - always just a hash.
	Hash(H::Output),
}

impl<H: traits::Hash, L> From<L> for DataOrHash<H, L> {
	fn from(l: L) -> Self {
		Self::Data(l)
	}
}
mod encoding {
	use super::*;

	/// A helper type to implement [codec::Codec] for [DataOrHash].
	#[derive(codec::Encode, codec::Decode)]
	enum Either<A, B> {
		Left(A),
		Right(B),
	}

	impl<H: traits::Hash, L: FullLeaf> codec::Encode for DataOrHash<H, L> {
		fn encode_to<T: codec::Output>(&self, dest: &mut T) {
			match self {
				Self::Data(l) => l.using_encoded(
					|data| Either::<&[u8], &H::Output>::Left(data).encode_to(dest), false
				),
				Self::Hash(h) => Either::<&[u8], &H::Output>::Right(h).encode_to(dest),
			}
		}
	}

	impl<H: traits::Hash, L: FullLeaf> codec::Decode for DataOrHash<H, L> {
		fn decode<I: codec::Input>(value: &mut I) -> Result<Self, codec::Error> {
			let decoded: Either<Vec<u8>, H::Output> = Either::decode(value)?;
			Ok(match decoded {
				Either::Left(l) => DataOrHash::Data(L::decode(&mut &*l)?),
				Either::Right(r) => DataOrHash::Hash(r),
			})
		}
	}
}

impl<H: traits::Hash, L: FullLeaf> DataOrHash<H, L> {
	/// Retrieve a hash of this item.
	///
	/// Depending on the node type it's going to either be a contained value for [DataOrHash::Hash]
	/// node, or a hash of SCALE-encoded [DataOrHash::Data] data.
	pub fn hash(&self) -> H::Output {
		match *self {
			Self::Data(ref leaf) => leaf.using_encoded(<H as traits::Hash>::hash, true),
			Self::Hash(ref hash) => hash.clone(),
		}
	}
}

// TODO [ToDr] Docs
#[derive(RuntimeDebug, Clone, PartialEq)]
pub struct Compact<H, T> {
	pub tuple: T,
	_hash: sp_std::marker::PhantomData<H>,
}

impl<H, T> sp_std::ops::Deref for Compact<H, T> {
	type Target = T;

	fn deref(&self) -> &Self::Target {
		&self.tuple
	}
}

impl<H, T> Compact<H, T> {
	pub fn new(tuple: T) -> Self {
		Self { tuple, _hash: Default::default() }
	}
}

impl<H, T: codec::Decode> codec::Decode for Compact<H, T> {
	fn decode<I: codec::Input>(value: &mut I) -> Result<Self, codec::Error> {
		T::decode(value).map(Compact::new)
	}
}

impl<A, B, H> FullLeaf for Compact<H, (DataOrHash<H, A>, DataOrHash<H, B>)> where
	A: FullLeaf,
	B: FullLeaf,
	H: traits::Hash,
{
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F, compact: bool) -> R {
		if compact {
			codec::Encode::using_encoded(&(self.tuple.0.hash(), self.tuple.1.hash()), f)
		} else {
			let a = self.tuple.0.using_encoded(|x| x.to_vec(), false);
			let b = self.tuple.1.using_encoded(|x| x.to_vec(), false);
			codec::Encode::using_encoded(&(a, b), f)
		}
	}
}

// TODO [ToDr] Impl for all tuples
impl<A, B, H> LeafDataProvider for Compact<H, (A, B)> where
	A: LeafDataProvider,
	B: LeafDataProvider,
	H: traits::Hash,
{
	type LeafData = Compact<H, (DataOrHash<H, A::LeafData>, DataOrHash<H, B::LeafData>)>;

	fn leaf_data() -> (Self::LeafData, Weight) {
		let (a_leaf, a_weight) = A::leaf_data();
		let (b_leaf, b_weight) = B::leaf_data();

		(
			Compact::new((a_leaf.into(), b_leaf.into())),
			a_weight.saturating_add(b_weight)
		)
	}
}

impl<A, B> LeafDataProvider for (A, B) where
	A: LeafDataProvider,
	B: LeafDataProvider,
	(A::LeafData, B::LeafData): FullLeaf,
{
	type LeafData = (A::LeafData, B::LeafData);

	fn leaf_data() -> (Self::LeafData, Weight) {
		let (a_leaf, a_weight) = A::leaf_data();
		let (b_leaf, b_weight) = B::leaf_data();

		(
			(a_leaf, b_leaf),
			a_weight.saturating_add(b_weight)
		)
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


#[cfg(test)]
mod tests {
	use super::*;

	use codec::Decode;
	use crate::tests::hex;
	use sp_runtime::traits::Keccak256;

	type Test = DataOrHash<Keccak256, String>;

	#[test]
	fn should_encode_decode_correctly_if_no_compact() {
		// given
		let cases = vec![
			Test::Data("Hello World!".into()),
			Test::Hash(hex("c3e7ba6b511162fead58f2c8b5764ce869ed1118011ac37392522ed16720bbcd")),
			Test::Data("".into()),
			Test::Data("3e48d6bcd417fb22e044747242451e2c0f3e602d1bcad2767c34808621956417".into()),
		];

		// when
		let encoded = cases
			.iter()
			.map(codec::Encode::encode)
			.collect::<Vec<_>>();

		let decoded = encoded
			.iter()
			.map(|x| Test::decode(&mut &**x))
			.collect::<Vec<_>>();

		// then
		assert_eq!(decoded, cases.into_iter().map(Result::<_, codec::Error>::Ok).collect::<Vec<_>>());
		// check encoding correctness
		assert_eq!(&encoded[0], &vec![0, 52, 48, 72, 101, 108, 108, 111, 32, 87, 111, 114, 108, 100, 33]);
		assert_eq!(&encoded[1], &vec![1, 195, 231, 186, 107, 81, 17, 98, 254, 173, 88, 242, 200, 181, 118, 76, 232, 105, 237, 17, 24, 1, 26, 195, 115, 146, 82, 46, 209, 103, 32, 187, 205]);
	}

	#[test]
	fn should_return_the_hash_correctly() {
		// given
		let a = Test::Data("Hello World!".into());
		let b = Test::Hash(hex("c3e7ba6b511162fead58f2c8b5764ce869ed1118011ac37392522ed16720bbcd"));

		// when
		let a = a.hash();
		let b = b.hash();

		// then
		assert_eq!(a, hex("a9c321be8c24ba4dc2bd73f5300bde67dc57228ab8b68b607bb4c39c5374fac9"));
		assert_eq!(b, hex("c3e7ba6b511162fead58f2c8b5764ce869ed1118011ac37392522ed16720bbcd"));
	}

	#[test]
	fn compact_should_work() {
		assert_eq!(true, false);
	}
}
