// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Generic implementations of Extrinsic/Header/Block.

#[cfg(feature = "std")] use serde::Serialize;
use rstd::prelude::*;
use rstd::marker::PhantomData;
use codec::{Slicable, Input};
use runtime_support::AuxDispatchable;
use traits::{self, Lookup};
use rstd::ops;

#[cfg(feature = "std")]
use std::fmt::{self, Debug};

#[cfg(feature = "std")]
pub trait MaybeSerializeDebug: Serialize + Debug {}
#[cfg(feature = "std")]
impl<T: Serialize + Debug> MaybeSerializeDebug for T {}

#[cfg(not(feature = "std"))]
pub trait MaybeSerializeDebug {}
#[cfg(not(feature = "std"))]
impl<T> MaybeSerializeDebug for T {}

pub trait Member: MaybeSerializeDebug + Eq + PartialEq + Clone {}
impl<T: MaybeSerializeDebug + Eq + PartialEq + Clone> Member for T {}

/// A vetted and verified extrinsic from the external world.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Debug))]
pub struct Extrinsic<AccountId, Index, Call> where
 	AccountId: Member,
 	Index: Member,
 	Call: Member,
{
	/// Who signed it (note this is not a signature).
	pub signed: AccountId,
	/// The number of extrinsics have come before from the same signer.
	pub index: Index,
	/// The function that should be called.
	pub function: Call,
}

impl<AccountId, Index, Call> Slicable for Extrinsic<AccountId, Index, Call> where
 	AccountId: Member + Slicable,
 	Index: Member + Slicable,
 	Call: Member + Slicable
{
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(Extrinsic {
			signed: Slicable::decode(input)?,
			index: Slicable::decode(input)?,
			function: Slicable::decode(input)?,
		})
	}

	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		self.signed.using_encoded(|s| v.extend(s));
		self.index.using_encoded(|s| v.extend(s));
		self.function.using_encoded(|s| v.extend(s));

		v
	}
}

/// An extrinsic right from the external world. Unchecked.
#[derive(Clone)]
#[cfg_attr(feature = "std", derive(Serialize))]
pub struct UncheckedExtrinsic<Address, Index, Call, Signature, DoLookup> where
	Address: Member,
	Index: Member,
	Call: Member,
	Signature: Member,			// TODO: should be Option<Signature>
{
	/// The actual extrinsic information.
	pub extrinsic: Extrinsic<Address, Index, Call>,
	/// The signature; should be an Ed25519 signature applied to the serialised `extrinsic` field.
	pub signature: Signature,
	pub dummy: PhantomData<DoLookup>,
}

// derive doesn't work since we have the null type `DoLookup` as a generic type param.
impl<Address, Index, Call, Signature, DoLookup> Eq for UncheckedExtrinsic<Address, Index, Call, Signature, DoLookup> where
 	Address: Member,
 	Index: Member,
 	Call: Member,
	Signature: Member,
{}
impl<Address, Index, Call, Signature, DoLookup> PartialEq for UncheckedExtrinsic<Address, Index, Call, Signature, DoLookup> where
 	Address: Member,
 	Index: Member,
 	Call: Member,
	Signature: Member,
{
	fn eq(&self, other: &Self) -> bool {
		self.extrinsic == other.extrinsic && self.signature == other.signature
	}
}

impl<Address, Index, Call, Signature, DoLookup> UncheckedExtrinsic<Address, Index, Call, Signature, DoLookup> where
 	Address: Member + Default,
 	Index: Member,
 	Call: Member,
	Signature: Member + Default,
{
	/// New instance.
	pub fn new(extrinsic: Extrinsic<Address, Index, Call>, signature: Signature) -> Self {
		UncheckedExtrinsic {
			extrinsic,
			signature,
			dummy: Default::default(),
		}
	}

	/// Is this extrinsic signed?
	pub fn is_signed(&self) -> bool {
		// TODO: should be Option<Signature> and Option<AccountId>
		self.signature != Default::default() || self.extrinsic.signed != Default::default()
	}
}

impl<Address, Index, Call, Signature, DoLookup> Slicable for UncheckedExtrinsic<Address, Index, Call, Signature, DoLookup> where
 	Address: Member + Default + Slicable,
 	Index: Member + Slicable,
 	Call: Member + Slicable,
	Signature: Member + Default + Slicable
{
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		// This is a little more complicated than usual since the binary format must be compatible
		// with substrate's generic `Vec<u8>` type. Basically this just means accepting that there
		// will be a prefix of u32, which has the total number of bytes following (we don't need
		// to use this).
		let _length_do_not_remove_me_see_above: u32 = Slicable::decode(input)?;

		Some(UncheckedExtrinsic::new(
			Slicable::decode(input)?,
			Slicable::decode(input)?
		))
	}

	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		// need to prefix with the total length as u32 to ensure it's binary comptible with
		// Vec<u8>. we'll make room for it here, then overwrite once we know the length.
		v.extend(&[0u8; 4]);

		self.extrinsic.signed.using_encoded(|s| v.extend(s));
		self.extrinsic.index.using_encoded(|s| v.extend(s));
		self.extrinsic.function.using_encoded(|s| v.extend(s));
		self.signature.using_encoded(|s| v.extend(s));

		let length = (v.len() - 4) as u32;
		length.using_encoded(|s| v[0..4].copy_from_slice(s));

		v
	}
}

#[cfg(feature = "std")]
impl<Address, Index, Call, Signature, DoLookup> fmt::Debug for UncheckedExtrinsic<Address, Index, Call, Signature, DoLookup> where
 	Address: Member,
 	Index: Member,
 	Call: Member,
	Signature: Member,
{
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "UncheckedExtrinsic({:?})", self.extrinsic)
	}
}

impl<Address, Index, Call, Signature, DoLookup> traits::Checkable for UncheckedExtrinsic<Address, Index, Call, Signature, DoLookup> where
 	Address: Member + Default,
 	Index: Member,
 	Call: Member,
	Signature: Member + Default + traits::Verify<Signer = <DoLookup as Lookup<Address>>::Target>,
	Extrinsic<<DoLookup as Lookup<Address>>::Target, Index, Call>: Slicable,
	DoLookup: Lookup<Address>,
	<DoLookup as Lookup<Address>>::Target: Member + Default,
{
	type Checked = CheckedExtrinsic<<DoLookup as Lookup<Address>>::Target, Index, Call>;

	fn check(self) -> Result<Self::Checked, &'static str> {
		if !self.is_signed() {
			Ok(CheckedExtrinsic(Extrinsic {
				signed: Default::default(),
				index: self.extrinsic.index,
				function: self.extrinsic.function,
			}))
		} else {
			let extrinsic: Extrinsic<<DoLookup as Lookup<Address>>::Target, Index, Call>
				= Extrinsic {
					signed: <DoLookup as Lookup<Address>>::lookup(self.extrinsic.signed).ok_or("bad address in extrinsic")?,
				 	index: self.extrinsic.index,
					function: self.extrinsic.function,
				};
			let sig = self.signature;
			if ::codec::Slicable::using_encoded(&extrinsic, |msg|
				sig.verify(msg, &extrinsic.signed)
			) {
				Ok(CheckedExtrinsic(extrinsic))
			} else {
				Err("bad signature in extrinsic")
			}
		}
	}
}

/// A type-safe indicator that an extrinsic has been checked.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct CheckedExtrinsic<AccountId, Index, Call>
	(Extrinsic<AccountId, Index, Call>)
where
 	AccountId: Member,
 	Index: Member,
 	Call: Member;

impl<AccountId, Index, Call> ops::Deref
	for CheckedExtrinsic<AccountId, Index, Call>
where
 	AccountId: Member,
 	Index: Member,
 	Call: Member,
{
	type Target = Extrinsic<AccountId, Index, Call>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl<AccountId, Index, Call> traits::Applyable
	for CheckedExtrinsic<AccountId, Index, Call>
where
 	AccountId: Member,
 	Index: Member,
 	Call: Member + AuxDispatchable<Aux = AccountId>,
{
	type Index = Index;
	type AccountId = AccountId;

	fn index(&self) -> &Self::Index {
		&self.0.index
	}

	fn sender(&self) -> &Self::AccountId {
		&self.0.signed
	}

	fn apply(self) -> Result<(), &'static str> {
		let xt = self.0;
		xt.function.dispatch(&xt.signed)
	}
}

#[derive(Default, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
pub struct Digest<Item: Member> {
	pub logs: Vec<Item>,
}
impl<Item> Slicable for Digest<Item> where
 	Item: Member + Slicable
{
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(Digest { logs: Slicable::decode(input)? })
	}
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.logs.using_encoded(f)
	}
}
impl<Item> traits::Digest for Digest<Item> where
 	Item: Member + Slicable
{
	type Item = Item;
	fn push(&mut self, item: Self::Item) {
		self.logs.push(item);
	}
}

/// Abstraction over a block header for a substrate chain.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub struct Header<Number, Hash, DigestItem> where
	Number: Member,
	Hash: Member,
	DigestItem: Member,
{
	/// The parent hash.
	pub parent_hash: Hash,
	/// The block number.
	pub number: Number,
	/// The state trie merkle root
	pub state_root: Hash,
	/// The merkle root of the extrinsics.
	pub extrinsics_root: Hash,
	/// A chain-specific digest of data useful for light clients or referencing auxiliary data.
	pub digest: Digest<DigestItem>,
}

impl<Number, Hash, DigestItem> Slicable for Header<Number, Hash, DigestItem> where
	Number: Member + Slicable,
 	Hash: Member + Slicable,
	DigestItem: Member + Slicable,
{
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(Header {
			parent_hash: Slicable::decode(input)?,
			number: Slicable::decode(input)?,
			state_root: Slicable::decode(input)?,
			extrinsics_root: Slicable::decode(input)?,
			digest: Slicable::decode(input)?,
		})
	}

	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();
		self.parent_hash.using_encoded(|s| v.extend(s));
		self.number.using_encoded(|s| v.extend(s));
		self.state_root.using_encoded(|s| v.extend(s));
		self.extrinsics_root.using_encoded(|s| v.extend(s));
		self.digest.using_encoded(|s| v.extend(s));
		v
	}
}
impl<Number, Hash, DigestItem> traits::Header for Header<Number, Hash, DigestItem> where
 	Number: Member + Slicable,
 	Hash: Member + Slicable,
	DigestItem: Member + Slicable,
 {
	type Number = Number;
	type Hash = Hash;
	type Digest = Digest<DigestItem>;

	fn number(&self) -> &Self::Number { &self.number }
	fn extrinsics_root(&self) -> &Self::Hash { &self.extrinsics_root }
	fn state_root(&self) -> &Self::Hash { &self.state_root }
	fn parent_hash(&self) -> &Self::Hash { &self.parent_hash }
	fn digest(&self) -> &Self::Digest { &self.digest }
	fn new(
		number: Self::Number,
		extrinsics_root: Self::Hash,
		state_root: Self::Hash,
		parent_hash: Self::Hash,
		digest: Self::Digest
	) -> Self {
		Header {
			number, extrinsics_root: extrinsics_root, state_root, parent_hash, digest
		}
	}
}

/// Abstraction over a substrate block.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub struct Block<Number, Hash, DigestItem, AccountId, Index, Call, Signature, DoLookup> where
	Number: Member,
	Hash: Member,
	DigestItem: Member,
 	AccountId: Member,
 	Index: Member,
 	Call: Member,
 	Signature: Member,
{
	/// The block header.
	pub header: Header<Number, Hash, DigestItem>,
	/// The accompanying extrinsics.
	pub extrinsics: Vec<UncheckedExtrinsic<AccountId, Index, Call, Signature, DoLookup>>,
}

impl<Number, Hash, DigestItem, AccountId, Index, Call, Signature, DoLookup> Slicable
	for Block<Number, Hash, DigestItem, AccountId, Index, Call, Signature, DoLookup>
where
	Number: Member,
	Hash: Member,
	DigestItem: Member,
 	AccountId: Member,
 	Index: Member,
 	Call: Member,
 	Signature: Member,
	Header<Number, Hash, DigestItem>: Slicable,
	UncheckedExtrinsic<AccountId, Index, Call, Signature, DoLookup>: Slicable,
{
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(Block {
			header: Slicable::decode(input)?,
			extrinsics: Slicable::decode(input)?,
		})
	}
	fn encode(&self) -> Vec<u8> {
		let mut v: Vec<u8> = Vec::new();
		v.extend(self.header.encode());
		v.extend(self.extrinsics.encode());
		v
	}
}

impl<Number, Hash, DigestItem, AccountId, Index, Call, Signature, DoLookup> traits::Block
	for Block<Number, Hash, DigestItem, AccountId, Index, Call, Signature, DoLookup>
where
	Number: Member + Slicable,
	Hash: Member + Slicable,
	DigestItem: Member + Slicable,
 	AccountId: Member,
 	Index: Member,
 	Call: Member,
 	Signature: Member
{
	type Extrinsic = UncheckedExtrinsic<AccountId, Index, Call, Signature, DoLookup>;
	type Header = Header<Number, Hash, DigestItem>;
	fn header(&self) -> &Self::Header {
		&self.header
	}
	fn extrinsics(&self) -> &[Self::Extrinsic] {
		&self.extrinsics[..]
	}
	fn deconstruct(self) -> (Self::Header, Vec<Self::Extrinsic>) {
		(self.header, self.extrinsics)
	}
}
