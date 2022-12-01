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

//! Merkle Mountain Range primitive types.

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

use frame_support::RuntimeDebug;
use sp_runtime::traits::{self, One, Saturating};
use sp_std::fmt;
#[cfg(not(feature = "std"))]
use sp_std::prelude::Vec;

/// A type to describe node position in the MMR (node index).
pub type NodeIndex = u64;

/// A type to describe leaf position in the MMR.
///
/// Note this is different from [`NodeIndex`], which can be applied to
/// both leafs and inner nodes. Leafs will always have consecutive `LeafIndex`,
/// but might be actually at different positions in the MMR `NodeIndex`.
pub type LeafIndex = u64;

/// A provider of the MMR's leaf data.
pub trait LeafDataProvider {
	/// A type that should end up in the leaf of MMR.
	type LeafData: FullLeaf + codec::Decode;

	/// The method to return leaf data that should be placed
	/// in the leaf node appended MMR at this block.
	///
	/// This is being called by the `on_initialize` method of
	/// this pallet at the very beginning of each block.
	fn leaf_data() -> Self::LeafData;
}

impl LeafDataProvider for () {
	type LeafData = ();

	fn leaf_data() -> Self::LeafData {
		()
	}
}

/// The most common use case for MMRs is to store historical block hashes,
/// so that any point in time in the future we can receive a proof about some past
/// blocks without using excessive on-chain storage.
///
/// Hence we implement the [LeafDataProvider] for [frame_system::Pallet]. Since the
/// current block hash is not available (since the block is not finished yet),
/// we use the `parent_hash` here along with parent block number.
impl<T: frame_system::Config> LeafDataProvider for frame_system::Pallet<T> {
	type LeafData = (<T as frame_system::Config>::BlockNumber, <T as frame_system::Config>::Hash);

	fn leaf_data() -> Self::LeafData {
		(Self::block_number().saturating_sub(One::one()), Self::parent_hash())
	}
}

/// New MMR root notification hook.
pub trait OnNewRoot<Hash> {
	/// Function called by the pallet in case new MMR root has been computed.
	fn on_new_root(root: &Hash);
}

/// No-op implementation of [OnNewRoot].
impl<Hash> OnNewRoot<Hash> for () {
	fn on_new_root(_root: &Hash) {}
}

/// A full leaf content stored in the offchain-db.
pub trait FullLeaf: Clone + PartialEq + fmt::Debug {
	/// Encode the leaf either in it's full or compact form.
	///
	/// NOTE the encoding returned here MUST be `Decode`able into `FullLeaf`.
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F, compact: bool) -> R;
}

impl<T: codec::Encode + codec::Decode + Clone + PartialEq + fmt::Debug> FullLeaf for T {
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F, _compact: bool) -> R {
		codec::Encode::using_encoded(self, f)
	}
}

/// An element representing either full data or it's hash.
///
/// See [Compact] to see how it may be used in practice to reduce the size
/// of proofs in case multiple [LeafDataProvider]s are composed together.
/// This is also used internally by the MMR to differentiate leaf nodes (data)
/// and inner nodes (hashes).
///
/// [DataOrHash::hash] method calculates the hash of this element in it's compact form,
/// so should be used instead of hashing the encoded form (which will always be non-compact).
#[derive(RuntimeDebug, Clone, PartialEq)]
pub enum DataOrHash<H: traits::Hash, L> {
	/// Arbitrary data in it's full form.
	Data(L),
	/// A hash of some data.
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
		fn encode_to<T: codec::Output + ?Sized>(&self, dest: &mut T) {
			match self {
				Self::Data(l) => l.using_encoded(
					|data| Either::<&[u8], &H::Output>::Left(data).encode_to(dest),
					false,
				),
				Self::Hash(h) => Either::<&[u8], &H::Output>::Right(h).encode_to(dest),
			}
		}
	}

	impl<H: traits::Hash, L: FullLeaf + codec::Decode> codec::Decode for DataOrHash<H, L> {
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

/// A composition of multiple leaf elements with compact form representation.
///
/// When composing together multiple [LeafDataProvider]s you will end up with
/// a tuple of `LeafData` that each element provides.
///
/// However this will cause the leaves to have significant size, while for some
/// use cases it will be enough to prove only one element of the tuple.
/// That's the rationale for [Compact] struct. We wrap each element of the tuple
/// into [DataOrHash] and each tuple element is hashed first before constructing
/// the final hash of the entire tuple. This allows you to replace tuple elements
/// you don't care about with their hashes.
#[derive(RuntimeDebug, Clone, PartialEq)]
pub struct Compact<H, T> {
	/// Internal tuple representation.
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
	/// Create a new [Compact] wrapper for a tuple.
	pub fn new(tuple: T) -> Self {
		Self { tuple, _hash: Default::default() }
	}
}

impl<H, T: codec::Decode> codec::Decode for Compact<H, T> {
	fn decode<I: codec::Input>(value: &mut I) -> Result<Self, codec::Error> {
		T::decode(value).map(Compact::new)
	}
}

macro_rules! impl_leaf_data_for_tuple {
	( $( $name:ident : $id:tt ),+ ) => {
		/// [FullLeaf] implementation for `Compact<H, (DataOrHash<H, Tuple>, ...)>`
		impl<H, $( $name ),+> FullLeaf for Compact<H, ( $( DataOrHash<H, $name>, )+ )> where
			H: traits::Hash,
			$( $name: FullLeaf ),+
		{
			fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F, compact: bool) -> R {
				if compact {
					codec::Encode::using_encoded(&(
						$( DataOrHash::<H, $name>::Hash(self.tuple.$id.hash()), )+
					), f)
				} else {
					codec::Encode::using_encoded(&self.tuple, f)
				}
			}
		}

		/// [LeafDataProvider] implementation for `Compact<H, (DataOrHash<H, Tuple>, ...)>`
		///
		/// This provides a compact-form encoding for tuples wrapped in [Compact].
		impl<H, $( $name ),+> LeafDataProvider for Compact<H, ( $( $name, )+ )> where
			H: traits::Hash,
			$( $name: LeafDataProvider ),+
		{
			type LeafData = Compact<
				H,
				( $( DataOrHash<H, $name::LeafData>, )+ ),
			>;

			fn leaf_data() -> Self::LeafData {
				let tuple = (
					$( DataOrHash::Data($name::leaf_data()), )+
				);
				Compact::new(tuple)
			}
		}

		/// [LeafDataProvider] implementation for `(Tuple, ...)`
		///
		/// This provides regular (non-compactable) composition of [LeafDataProvider]s.
		impl<$( $name ),+> LeafDataProvider for ( $( $name, )+ ) where
			( $( $name::LeafData, )+ ): FullLeaf,
			$( $name: LeafDataProvider ),+
		{
			type LeafData = ( $( $name::LeafData, )+ );

			fn leaf_data() -> Self::LeafData {
				(
					$( $name::leaf_data(), )+
				)
			}
		}
	}
}

/// Test functions implementation for `Compact<H, (DataOrHash<H, Tuple>, ...)>`
#[cfg(test)]
impl<H, A, B> Compact<H, (DataOrHash<H, A>, DataOrHash<H, B>)>
where
	H: traits::Hash,
	A: FullLeaf,
	B: FullLeaf,
{
	/// Retrieve a hash of this item in it's compact form.
	pub fn hash(&self) -> H::Output {
		self.using_encoded(<H as traits::Hash>::hash, true)
	}
}

impl_leaf_data_for_tuple!(A:0);
impl_leaf_data_for_tuple!(A:0, B:1);
impl_leaf_data_for_tuple!(A:0, B:1, C:2);
impl_leaf_data_for_tuple!(A:0, B:1, C:2, D:3);
impl_leaf_data_for_tuple!(A:0, B:1, C:2, D:3, E:4);

/// A MMR proof data for one of the leaves.
#[derive(codec::Encode, codec::Decode, RuntimeDebug, Clone, PartialEq, Eq)]
pub struct Proof<Hash> {
	/// The index of the leaf the proof is for.
	pub leaf_index: LeafIndex,
	/// Number of leaves in MMR, when the proof was generated.
	pub leaf_count: NodeIndex,
	/// Proof elements (hashes of siblings of inner nodes on the path to the leaf).
	pub items: Vec<Hash>,
}

/// Merkle Mountain Range operation error.
#[derive(RuntimeDebug, codec::Encode, codec::Decode, PartialEq, Eq)]
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
	#![allow(unused_variables)]
	/// Consume given error `e` with `self` and generate a native log entry with error details.
	pub fn log_error(self, e: impl fmt::Debug) -> Self {
		log::error!(
			target: "runtime::mmr",
			"[{:?}] MMR error: {:?}",
			self,
			e,
		);
		self
	}

	/// Consume given error `e` with `self` and generate a native log entry with error details.
	pub fn log_debug(self, e: impl fmt::Debug) -> Self {
		log::debug!(
			target: "runtime::mmr",
			"[{:?}] MMR error: {:?}",
			self,
			e,
		);
		self
	}
}

/// A helper type to allow using arbitrary SCALE-encoded leaf data in the RuntimeApi.
///
/// The point is to be able to verify MMR proofs from external MMRs, where we don't
/// know the exact leaf type, but it's enough for us to have it SCALE-encoded.
///
/// Note the leaf type should be encoded in its compact form when passed through this type.
/// See [FullLeaf] documentation for details.
///
/// This type does not implement SCALE encoding/decoding on purpose to avoid confusion,
/// it would have to be SCALE-compatible with the concrete leaf type, but due to SCALE limitations
/// it's not possible to know how many bytes the encoding of concrete leaf type uses.
#[cfg_attr(feature = "std", derive(serde::Serialize, serde::Deserialize))]
#[derive(RuntimeDebug, Clone, PartialEq)]
pub struct OpaqueLeaf(
	/// Raw bytes of the leaf type encoded in its compact form.
	///
	/// NOTE it DOES NOT include length prefix (like `Vec<u8>` encoding would).
	#[cfg_attr(feature = "std", serde(with = "sp_core::bytes"))]
	pub Vec<u8>,
);

impl OpaqueLeaf {
	/// Convert a concrete MMR leaf into an opaque type.
	pub fn from_leaf<T: FullLeaf>(leaf: &T) -> Self {
		let encoded_leaf = leaf.using_encoded(|d| d.to_vec(), true);
		OpaqueLeaf::from_encoded_leaf(encoded_leaf)
	}

	/// Create a `OpaqueLeaf` given raw bytes of compact-encoded leaf.
	pub fn from_encoded_leaf(encoded_leaf: Vec<u8>) -> Self {
		OpaqueLeaf(encoded_leaf)
	}

	/// Attempt to decode the leaf into expected concrete type.
	pub fn try_decode<T: codec::Decode>(&self) -> Option<T> {
		codec::Decode::decode(&mut &*self.0).ok()
	}
}

impl FullLeaf for OpaqueLeaf {
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F, _compact: bool) -> R {
		f(&self.0)
	}
}

/// A type-safe wrapper for the concrete leaf type.
///
/// This structure serves merely to avoid passing raw `Vec<u8>` around.
/// It must be `Vec<u8>`-encoding compatible.
///
/// It is different from [`OpaqueLeaf`], because it does implement `Codec`
/// and the encoding has to match raw `Vec<u8>` encoding.
#[derive(codec::Encode, codec::Decode, RuntimeDebug, PartialEq, Eq)]
pub struct EncodableOpaqueLeaf(pub Vec<u8>);

impl EncodableOpaqueLeaf {
	/// Convert a concrete leaf into encodable opaque version.
	pub fn from_leaf<T: FullLeaf>(leaf: &T) -> Self {
		let opaque = OpaqueLeaf::from_leaf(leaf);
		Self::from_opaque_leaf(opaque)
	}

	/// Given an opaque leaf, make it encodable.
	pub fn from_opaque_leaf(opaque: OpaqueLeaf) -> Self {
		Self(opaque.0)
	}

	/// Try to convert into a [OpaqueLeaf].
	pub fn into_opaque_leaf(self) -> OpaqueLeaf {
		// wrap into `OpaqueLeaf` type
		OpaqueLeaf::from_encoded_leaf(self.0)
	}
}

sp_api::decl_runtime_apis! {
	/// API to interact with MMR pallet.
	pub trait MmrApi<Hash: codec::Codec> {
		/// Generate MMR proof for a leaf under given index.
		fn generate_proof(leaf_index: LeafIndex) -> Result<(EncodableOpaqueLeaf, Proof<Hash>), Error>;

		/// Verify MMR proof against on-chain MMR.
		///
		/// Note this function will use on-chain MMR root hash and check if the proof
		/// matches the hash.
		/// See [Self::verify_proof_stateless] for a stateless verifier.
		fn verify_proof(leaf: EncodableOpaqueLeaf, proof: Proof<Hash>) -> Result<(), Error>;

		/// Verify MMR proof against given root hash.
		///
		/// Note this function does not require any on-chain storage - the
		/// proof is verified against given MMR root hash.
		///
		/// The leaf data is expected to be encoded in it's compact form.
		fn verify_proof_stateless(root: Hash, leaf: EncodableOpaqueLeaf, proof: Proof<Hash>)
			-> Result<(), Error>;
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use codec::Decode;
	use sp_core::H256;
	use sp_runtime::traits::Keccak256;

	pub(crate) fn hex(s: &str) -> H256 {
		s.parse().unwrap()
	}

	type Test = DataOrHash<Keccak256, String>;
	type TestCompact = Compact<Keccak256, (Test, Test)>;
	type TestProof = Proof<<Keccak256 as traits::Hash>::Output>;

	#[test]
	fn should_encode_decode_proof() {
		// given
		let proof: TestProof = Proof {
			leaf_index: 5,
			leaf_count: 10,
			items: vec![
				hex("c3e7ba6b511162fead58f2c8b5764ce869ed1118011ac37392522ed16720bbcd"),
				hex("d3e7ba6b511162fead58f2c8b5764ce869ed1118011ac37392522ed16720bbcd"),
				hex("e3e7ba6b511162fead58f2c8b5764ce869ed1118011ac37392522ed16720bbcd"),
			],
		};

		// when
		let encoded = codec::Encode::encode(&proof);
		let decoded = TestProof::decode(&mut &*encoded);

		// then
		assert_eq!(decoded, Ok(proof));
	}

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
		let encoded = cases.iter().map(codec::Encode::encode).collect::<Vec<_>>();

		let decoded = encoded.iter().map(|x| Test::decode(&mut &**x)).collect::<Vec<_>>();

		// then
		assert_eq!(
			decoded,
			cases.into_iter().map(Result::<_, codec::Error>::Ok).collect::<Vec<_>>()
		);
		// check encoding correctness
		assert_eq!(&encoded[0], &hex_literal::hex!("00343048656c6c6f20576f726c6421"));
		assert_eq!(
			encoded[1].as_slice(),
			hex_literal::hex!("01c3e7ba6b511162fead58f2c8b5764ce869ed1118011ac37392522ed16720bbcd")
				.as_ref()
		);
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
		// given
		let a = Test::Data("Hello World!".into());
		let b = Test::Data("".into());

		// when
		let c: TestCompact = Compact::new((a.clone(), b.clone()));
		let d: TestCompact = Compact::new((Test::Hash(a.hash()), Test::Hash(b.hash())));

		// then
		assert_eq!(c.hash(), d.hash());
	}

	#[test]
	fn compact_should_encode_decode_correctly() {
		// given
		let a = Test::Data("Hello World!".into());
		let b = Test::Data("".into());

		let c: TestCompact = Compact::new((a.clone(), b.clone()));
		let d: TestCompact = Compact::new((Test::Hash(a.hash()), Test::Hash(b.hash())));
		let cases = vec![c, d.clone()];

		// when
		let encoded_compact =
			cases.iter().map(|c| c.using_encoded(|x| x.to_vec(), true)).collect::<Vec<_>>();

		let encoded =
			cases.iter().map(|c| c.using_encoded(|x| x.to_vec(), false)).collect::<Vec<_>>();

		let decoded_compact = encoded_compact
			.iter()
			.map(|x| TestCompact::decode(&mut &**x))
			.collect::<Vec<_>>();

		let decoded = encoded.iter().map(|x| TestCompact::decode(&mut &**x)).collect::<Vec<_>>();

		// then
		assert_eq!(
			decoded,
			cases.into_iter().map(Result::<_, codec::Error>::Ok).collect::<Vec<_>>()
		);

		assert_eq!(decoded_compact, vec![Ok(d.clone()), Ok(d.clone())]);
	}

	#[test]
	fn opaque_leaves_should_be_full_leaf_compatible() {
		// given
		let a = Test::Data("Hello World!".into());
		let b = Test::Data("".into());

		let c: TestCompact = Compact::new((a.clone(), b.clone()));
		let d: TestCompact = Compact::new((Test::Hash(a.hash()), Test::Hash(b.hash())));
		let cases = vec![c, d.clone()];

		let encoded_compact = cases
			.iter()
			.map(|c| c.using_encoded(|x| x.to_vec(), true))
			.map(OpaqueLeaf::from_encoded_leaf)
			.collect::<Vec<_>>();

		let opaque = cases.iter().map(OpaqueLeaf::from_leaf).collect::<Vec<_>>();

		// then
		assert_eq!(encoded_compact, opaque);
	}

	#[test]
	fn encode_opaque_leaf_should_be_scale_compatible() {
		use codec::Encode;

		// given
		let a = Test::Data("Hello World!".into());
		let case1 = EncodableOpaqueLeaf::from_leaf(&a);
		let case2 = EncodableOpaqueLeaf::from_opaque_leaf(OpaqueLeaf(a.encode()));
		let case3 = a.encode().encode();

		// when
		let encoded = vec![&case1, &case2].into_iter().map(|x| x.encode()).collect::<Vec<_>>();
		let decoded = vec![&*encoded[0], &*encoded[1], &*case3]
			.into_iter()
			.map(|x| EncodableOpaqueLeaf::decode(&mut &*x))
			.collect::<Vec<_>>();

		// then
		assert_eq!(case1, case2);
		assert_eq!(encoded[0], encoded[1]);
		// then encoding should also match double-encoded leaf.
		assert_eq!(encoded[0], case3);

		assert_eq!(decoded[0], decoded[1]);
		assert_eq!(decoded[1], decoded[2]);
		assert_eq!(decoded[0], Ok(case2));
		assert_eq!(decoded[1], Ok(case1));
	}
}
