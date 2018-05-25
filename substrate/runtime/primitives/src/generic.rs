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

#[cfg(feature = "std")] use std::fmt;
use rstd::prelude::*;
use codec::{Slicable, Input};
use runtime_support::AuxDispatchable;
use traits::{self, Member, SimpleArithmetic, SimpleBitOps, MaybeDisplay, Block as BlockT,
	Header as HeaderT, Hashing as HashingT};
use rstd::ops;

/// A vetted and verified extrinsic from the external world.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Debug))]
pub struct Extrinsic<AccountId, Index, Call> where
 	AccountId: Member + MaybeDisplay,
 	Index: Member + MaybeDisplay + SimpleArithmetic,
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
 	AccountId: Member + Slicable + MaybeDisplay,
 	Index: Member + Slicable + MaybeDisplay + SimpleArithmetic,
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

/// A extrinsics right from the external world. Unchecked.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize))]
pub struct UncheckedExtrinsic<AccountId, Index, Call, Signature> where
 	AccountId: Member + MaybeDisplay,
 	Index: Member + MaybeDisplay + SimpleArithmetic,
 	Call: Member,
 	Signature: Member,			// TODO: should be Option<Signature>
{
	/// The actual extrinsic information.
	pub extrinsic: Extrinsic<AccountId, Index, Call>,
	/// The signature; should be an Ed25519 signature applied to the serialised `extrinsic` field.
	pub signature: Signature,
}

impl<AccountId, Index, Call, Signature> UncheckedExtrinsic<AccountId, Index, Call, Signature> where
 	AccountId: Member + Default + MaybeDisplay,
 	Index: Member + MaybeDisplay + SimpleArithmetic,
 	Call: Member,
	Signature: Member + Default,
{
	/// Is this extrinsic signed?
	pub fn is_signed(&self) -> bool {
		// TODO: should be Option<Signature> and Option<AccountId>
		self.signature != Signature::default() || self.extrinsic.signed != AccountId::default()
	}
}

impl<AccountId, Index, Call, Signature> Slicable for UncheckedExtrinsic<AccountId, Index, Call, Signature> where
 	AccountId: Member + MaybeDisplay,
 	Index: Member + MaybeDisplay + SimpleArithmetic,
 	Call: Member,
	Signature: Member + Slicable,
	Extrinsic<AccountId, Index, Call>: Slicable,
{
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		// This is a little more complicated than usual since the binary format must be compatible
		// with substrate's generic `Vec<u8>` type. Basically this just means accepting that there
		// will be a prefix of u32, which has the total number of bytes following (we don't need
		// to use this).
		let _length_do_not_remove_me_see_above: u32 = Slicable::decode(input)?;

		Some(UncheckedExtrinsic {
			extrinsic: Slicable::decode(input)?,
			signature: Slicable::decode(input)?,
		})
	}

	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		// need to prefix with the total length as u32 to ensure it's binary comptible with
		// Vec<u8>. we'll make room for it here, then overwrite once we know the length.
		v.extend(&[0u8; 4]);

/*		self.extrinsic.signed.using_encoded(|s| v.extend(s));
		self.extrinsic.index.using_encoded(|s| v.extend(s));
		self.extrinsic.function.using_encoded(|s| v.extend(s));*/
		self.extrinsic.using_encoded(|s| v.extend(s));

		self.signature.using_encoded(|s| v.extend(s));

		let length = (v.len() - 4) as u32;
		length.using_encoded(|s| v[0..4].copy_from_slice(s));

		v
	}
}

#[cfg(feature = "std")]
impl<AccountId, Index, Call, Signature> fmt::Debug for UncheckedExtrinsic<AccountId, Index, Call, Signature> where
 	AccountId: Member + MaybeDisplay,
 	Index: Member + MaybeDisplay + SimpleArithmetic,
 	Call: Member,
	Signature: Member,
{
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "UncheckedExtrinsic({:?})", self.extrinsic)
	}
}

impl<AccountId, Index, Call, Signature> traits::Checkable for UncheckedExtrinsic<AccountId, Index, Call, Signature> where
 	AccountId: Member + Default + MaybeDisplay,
 	Index: Member + MaybeDisplay + SimpleArithmetic,
 	Call: Member,
	Signature: Member + Default + traits::Verify<Signer = AccountId> + Slicable,
	Extrinsic<AccountId, Index, Call>: Slicable,
{
	type Checked = CheckedExtrinsic<AccountId, Index, Call, Signature>;

	fn check(self) -> Result<Self::Checked, Self> {
		if !self.is_signed() {
			Ok(CheckedExtrinsic(self))
		} else {
			if ::codec::Slicable::using_encoded(&self.extrinsic, |msg|
				self.signature.verify(msg, &self.extrinsic.signed)
			) {
				Ok(CheckedExtrinsic(self))
			} else {
				Err(self)
			}
		}
	}
}

/// A type-safe indicator that a extrinsic has been checked.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Debug))]
pub struct CheckedExtrinsic<AccountId, Index, Call, Signature>
	(UncheckedExtrinsic<AccountId, Index, Call, Signature>)
where
 	AccountId: Member + MaybeDisplay,
 	Index: Member + MaybeDisplay + SimpleArithmetic,
 	Call: Member,
	Signature: Member;

impl<AccountId, Index, Call, Signature> CheckedExtrinsic<AccountId, Index, Call, Signature>
where
 	AccountId: Member + MaybeDisplay,
 	Index: Member + MaybeDisplay + SimpleArithmetic,
 	Call: Member,
	Signature: Member
{
	/// Get a reference to the checked signature.
	pub fn signature(&self) -> &Signature {
		&self.0.signature
	}

	/// Get a reference to the checked signature.
	pub fn as_unchecked(&self) -> &UncheckedExtrinsic<AccountId, Index, Call, Signature> {
		&self.0
	}

	/// Get a reference to the checked signature.
	pub fn into_unchecked(self) -> UncheckedExtrinsic<AccountId, Index, Call, Signature> {
		self.0
	}
}

impl<AccountId, Index, Call, Signature> ops::Deref
	for CheckedExtrinsic<AccountId, Index, Call, Signature>
where
 	AccountId: Member + MaybeDisplay,
 	Index: Member + MaybeDisplay + SimpleArithmetic,
 	Call: Member,
	Signature: Member
{
	type Target = Extrinsic<AccountId, Index, Call>;

	fn deref(&self) -> &Self::Target {
		&self.0.extrinsic
	}
}

impl<AccountId, Index, Call, Signature> traits::Applyable
	for CheckedExtrinsic<AccountId, Index, Call, Signature>
where
 	AccountId: Member + MaybeDisplay,
 	Index: Member + MaybeDisplay + SimpleArithmetic,
 	Call: Member + AuxDispatchable<Aux = AccountId>,
	Signature: Member
{
	type Index = Index;
	type AccountId = AccountId;

	fn index(&self) -> &Self::Index {
		&self.0.extrinsic.index
	}

	fn sender(&self) -> &Self::AccountId {
		&self.0.extrinsic.signed
	}

	fn apply(self) {
		let xt = self.0.extrinsic;
		xt.function.dispatch(&xt.signed);
	}
}

#[derive(Default, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
pub struct Digest<Item: Member + Default> {
	pub logs: Vec<Item>,
}
impl<Item> Slicable for Digest<Item> where
 	Item: Member + Default + Slicable
{
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(Digest { logs: Slicable::decode(input)? })
	}
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.logs.using_encoded(f)
	}
}
impl<Item> traits::Digest for Digest<Item> where
 	Item: Member + Default + Slicable
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
pub struct Header<Number, Hashing, DigestItem> where
	Number: Member + MaybeDisplay + SimpleArithmetic + Slicable,
	Hashing: HashingT,
	DigestItem: Member + Default,
	<Hashing as HashingT>::Output: Default + Member + MaybeDisplay + SimpleBitOps + Slicable,
{
	/// The parent hash.
	pub parent_hash: <Hashing as HashingT>::Output,
	/// The block number.
	pub number: Number,
	/// The state trie merkle root
	pub state_root: <Hashing as HashingT>::Output,
	/// The merkle root of the extrinsics.
	pub extrinsics_root: <Hashing as HashingT>::Output,
	/// A chain-specific digest of data useful for light clients or referencing auxiliary data.
	pub digest: Digest<DigestItem>,
}

impl<Number, Hashing, DigestItem> Slicable for Header<Number, Hashing, DigestItem> where
	Number: Member + Slicable + MaybeDisplay + SimpleArithmetic + Slicable,
	Hashing: HashingT,
	DigestItem: Member + Default + Slicable,
	<Hashing as HashingT>::Output: Default + Member + MaybeDisplay + SimpleBitOps + Slicable,
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
impl<Number, Hashing, DigestItem> traits::Header for Header<Number, Hashing, DigestItem> where
 	Number: Member + Slicable + MaybeDisplay + SimpleArithmetic + Slicable,
	Hashing: HashingT,
	DigestItem: Member + Default + Slicable,
	<Hashing as HashingT>::Output: Default + Member + MaybeDisplay + SimpleBitOps + Slicable,
 {
	type Number = Number;
	type Hash = <Hashing as HashingT>::Output;
	type Hashing = Hashing;
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

/// Something to identify a block.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub enum BlockId<Block: BlockT> where {
	/// Identify by block header hash.
	Hash(<<Block as BlockT>::Header as HeaderT>::Hash),
	/// Identify by block number.
	Number(<<Block as BlockT>::Header as HeaderT>::Number),
}

#[cfg(feature = "std")]
impl<Block: BlockT> fmt::Display for BlockId<Block> {
	fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
		write!(f, "{:?}", self)
	}
}

/// Abstraction over a substrate block.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub struct Block<Number, Hashing, DigestItem, AccountId, Index, Call, Signature> where
	Number: Member + MaybeDisplay + SimpleArithmetic + Slicable,
	Hashing: HashingT,
	DigestItem: Member + Default,
	<Hashing as HashingT>::Output: Default + Member + MaybeDisplay + SimpleBitOps + Slicable,
 	AccountId: Member + MaybeDisplay,
 	Index: Member + MaybeDisplay + SimpleArithmetic,
 	Call: Member,
 	Signature: Member
{
	/// The block header.
	pub header: Header<Number, Hashing, DigestItem>,
	/// The accompanying extrinsics.
	pub extrinsics: Vec<UncheckedExtrinsic<AccountId, Index, Call, Signature>>,
}

impl<Number, Hashing, DigestItem, AccountId, Index, Call, Signature> Slicable
	for Block<Number, Hashing, DigestItem, AccountId, Index, Call, Signature>
where
	Number: Member + MaybeDisplay + SimpleArithmetic + Slicable,
	Hashing: HashingT,
	DigestItem: Member + Default,
	<Hashing as HashingT>::Output: Default + Member + MaybeDisplay + SimpleBitOps + Slicable,
 	AccountId: Member + MaybeDisplay,
 	Index: Member + MaybeDisplay + SimpleArithmetic,
 	Call: Member,
 	Signature: Member,
	Header<Number, Hashing, DigestItem>: Slicable,
	UncheckedExtrinsic<AccountId, Index, Call, Signature>: Slicable,
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

impl<Number, Hashing, DigestItem, AccountId, Index, Call, Signature> traits::Block
	for Block<Number, Hashing, DigestItem, AccountId, Index, Call, Signature>
where
	Number: Member + MaybeDisplay + SimpleArithmetic + Slicable,
	Hashing: HashingT,
	DigestItem: Member + Default,
	<Hashing as HashingT>::Output: Default + Member + MaybeDisplay + SimpleBitOps + Slicable,
 	AccountId: Member + MaybeDisplay,
 	Index: Member + MaybeDisplay + SimpleArithmetic,
 	Call: Member,
 	Signature: Member,
	Header<Number, Hashing, DigestItem>: traits::Header,
	UncheckedExtrinsic<AccountId, Index, Call, Signature>: Slicable,
{
	type Extrinsic = UncheckedExtrinsic<AccountId, Index, Call, Signature>;
	type Header = Header<Number, Hashing, DigestItem>;
	type Hash = <Self::Header as traits::Header>::Hash;

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
