// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Testing utilities.

use serde::{Serialize, Serializer, Deserialize, de::Error as DeError, Deserializer};
use std::{fmt::Debug, ops::Deref, fmt};
use crate::codec::{Codec, Encode, Decode};
use crate::traits::{self, Checkable, Applyable, BlakeTwo256, OpaqueKeys};
use crate::generic;
use crate::weights::{Weighable, Weight};
pub use substrate_primitives::H256;
use substrate_primitives::U256;
use substrate_primitives::ed25519::{Public as AuthorityId};

/// Authority Id
#[derive(Default, PartialEq, Eq, Clone, Encode, Decode, Debug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct UintAuthorityId(pub u64);
impl Into<AuthorityId> for UintAuthorityId {
	fn into(self) -> AuthorityId {
		let bytes: [u8; 32] = U256::from(self.0).into();
		AuthorityId(bytes)
	}
}

impl OpaqueKeys for UintAuthorityId {
	fn count() -> usize { 1 }
	// Unsafe, i know, but it's test code and it's just there because it's really convenient to
	// keep `UintAuthorityId` as a u64 under the hood.
	fn get_raw(&self, _: usize) -> &[u8] { unsafe { &std::mem::transmute::<_, &[u8; 8]>(&self.0)[..] } }
	fn get<T: Decode>(&self, _: usize) -> Option<T> { self.0.using_encoded(|mut x| T::decode(&mut x)) }
}

/// Digest item
pub type DigestItem = generic::DigestItem<H256>;

/// Header Digest
pub type Digest = generic::Digest<H256>;

/// Block Header
#[derive(PartialEq, Eq, Clone, Serialize, Debug, Encode, Decode)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct Header {
	/// Parent hash
	pub parent_hash: H256,
	/// Block Number
	pub number: u64,
	/// Post-execution state trie root
	pub state_root: H256,
	/// Merkle root of block's extrinsics
	pub extrinsics_root: H256,
	/// Digest items
	pub digest: Digest,
}

impl traits::Header for Header {
	type Number = u64;
	type Hashing = BlakeTwo256;
	type Hash = H256;

	fn number(&self) -> &Self::Number { &self.number }
	fn set_number(&mut self, num: Self::Number) { self.number = num }

	fn extrinsics_root(&self) -> &Self::Hash { &self.extrinsics_root }
	fn set_extrinsics_root(&mut self, root: Self::Hash) { self.extrinsics_root = root }

	fn state_root(&self) -> &Self::Hash { &self.state_root }
	fn set_state_root(&mut self, root: Self::Hash) { self.state_root = root }

	fn parent_hash(&self) -> &Self::Hash { &self.parent_hash }
	fn set_parent_hash(&mut self, hash: Self::Hash) { self.parent_hash = hash }

	fn digest(&self) -> &Digest { &self.digest }
	fn digest_mut(&mut self) -> &mut Digest { &mut self.digest }

	fn new(
		number: Self::Number,
		extrinsics_root: Self::Hash,
		state_root: Self::Hash,
		parent_hash: Self::Hash,
		digest: Digest,
	) -> Self {
		Header {
			number,
			extrinsics_root,
			state_root,
			parent_hash,
			digest,
		}
	}
}

impl<'a> Deserialize<'a> for Header {
	fn deserialize<D: Deserializer<'a>>(de: D) -> Result<Self, D::Error> {
		let r = <Vec<u8>>::deserialize(de)?;
		Decode::decode(&mut &r[..]).ok_or(DeError::custom("Invalid value passed into decode"))
	}
}

/// An opaque extrinsic wrapper type.
#[derive(PartialEq, Eq, Clone, Debug, Encode, Decode)]
pub struct ExtrinsicWrapper<Xt>(Xt);

impl<Xt> traits::Extrinsic for ExtrinsicWrapper<Xt> {
	fn is_signed(&self) -> Option<bool> {
		None
	}
}

impl<Xt: Encode> serde::Serialize for ExtrinsicWrapper<Xt>
{
	fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error> where S: ::serde::Serializer {
		self.using_encoded(|bytes| seq.serialize_bytes(bytes))
	}
}

impl<Xt> From<Xt> for ExtrinsicWrapper<Xt> {
	fn from(xt: Xt) -> Self {
		ExtrinsicWrapper(xt)
	}
}

impl<Xt> Deref for ExtrinsicWrapper<Xt> {
	type Target = Xt;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

/// Testing block
#[derive(PartialEq, Eq, Clone, Serialize, Debug, Encode, Decode)]
pub struct Block<Xt> {
	/// Block header
	pub header: Header,
	/// List of extrinsics
	pub extrinsics: Vec<Xt>,
}

impl<Xt: 'static + Codec + Sized + Send + Sync + Serialize + Clone + Eq + Debug + traits::Extrinsic> traits::Block for Block<Xt> {
	type Extrinsic = Xt;
	type Header = Header;
	type Hash = <Header as traits::Header>::Hash;

	fn header(&self) -> &Self::Header {
		&self.header
	}
	fn extrinsics(&self) -> &[Self::Extrinsic] {
		&self.extrinsics[..]
	}
	fn deconstruct(self) -> (Self::Header, Vec<Self::Extrinsic>) {
		(self.header, self.extrinsics)
	}
	fn new(header: Self::Header, extrinsics: Vec<Self::Extrinsic>) -> Self {
		Block { header, extrinsics }
	}
}

impl<'a, Xt> Deserialize<'a> for Block<Xt> where Block<Xt>: Decode {
	fn deserialize<D: Deserializer<'a>>(de: D) -> Result<Self, D::Error> {
		let r = <Vec<u8>>::deserialize(de)?;
		Decode::decode(&mut &r[..]).ok_or(DeError::custom("Invalid value passed into decode"))
	}
}

/// Test transaction, tuple of (sender, index, call)
/// with index only used if sender is some.
///
/// If sender is some then the transaction is signed otherwise it is unsigned.
#[derive(PartialEq, Eq, Clone, Encode, Decode)]
pub struct TestXt<Call>(pub Option<u64>, pub u64, pub Call);

impl<Call> Serialize for TestXt<Call> where TestXt<Call>: Encode
{
	fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error> where S: Serializer {
		self.using_encoded(|bytes| seq.serialize_bytes(bytes))
	}
}

impl<Call> Debug for TestXt<Call> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "TestXt({:?}, {:?})", self.0, self.1)
	}
}

impl<Call: Codec + Sync + Send, Context> Checkable<Context> for TestXt<Call> {
	type Checked = Self;
	fn check(self, _: &Context) -> Result<Self::Checked, &'static str> { Ok(self) }
}
impl<Call: Codec + Sync + Send> traits::Extrinsic for TestXt<Call> {
	fn is_signed(&self) -> Option<bool> {
		Some(self.0.is_some())
	}
}
impl<Call> Applyable for TestXt<Call> where
	Call: 'static + Sized + Send + Sync + Clone + Eq + Codec + Debug,
{
	type AccountId = u64;
	type Index = u64;
	type Call = Call;
	fn sender(&self) -> Option<&u64> { self.0.as_ref() }
	fn index(&self) -> Option<&u64> { self.0.as_ref().map(|_| &self.1) }
	fn deconstruct(self) -> (Self::Call, Option<Self::AccountId>) {
		(self.2, self.0)
	}
}
impl<Call> Weighable for TestXt<Call> {
	fn weight(&self, len: usize) -> Weight {
		// for testing: weight == size.
		len as Weight
	}
}
