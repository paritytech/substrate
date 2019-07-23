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
use crate::traits::{
	self, Checkable, Applyable, BlakeTwo256, OpaqueKeys, TypedKey, DispatchError, DispatchResult,
	ValidateUnsigned, SignedExtension, Dispatchable,
};
use crate::{generic, KeyTypeId};
use crate::weights::{GetDispatchInfo, DispatchInfo};
pub use substrate_primitives::H256;
use substrate_primitives::U256;
use substrate_primitives::ed25519::{Public as AuthorityId};
use crate::transaction_validity::TransactionValidity;

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

/// The key-type of the `UintAuthorityId`
pub const UINT_DUMMY_KEY: KeyTypeId = 0xdeadbeef;

impl TypedKey for UintAuthorityId {
	const KEY_TYPE: KeyTypeId = UINT_DUMMY_KEY;
}

impl AsRef<[u8]> for UintAuthorityId {
	fn as_ref(&self) -> &[u8] {
		let ptr = self.0 as *const _;
		// It's safe to do this here since `UintAuthorityId` is `u64`.
		unsafe { std::slice::from_raw_parts(ptr, 8) }
	}
}

impl OpaqueKeys for UintAuthorityId {
	type KeyTypeIds = std::iter::Cloned<std::slice::Iter<'static, KeyTypeId>>;

	fn key_ids() -> Self::KeyTypeIds { [UINT_DUMMY_KEY].iter().cloned() }
	// Unsafe, i know, but it's test code and it's just there because it's really convenient to
	// keep `UintAuthorityId` as a u64 under the hood.
	fn get_raw(&self, _: KeyTypeId) -> &[u8] {
		unsafe {
			std::slice::from_raw_parts(
				&self.0 as *const _ as *const u8,
				std::mem::size_of::<u64>(),
			)
		}
	}
	fn get<T: Decode>(&self, _: KeyTypeId) -> Option<T> { self.0.using_encoded(|mut x| T::decode(&mut x)) }
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
	type Call = ();

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

/// Test transaction, tuple of (sender, call, signed_extra)
/// with index only used if sender is some.
///
/// If sender is some then the transaction is signed otherwise it is unsigned.
#[derive(PartialEq, Eq, Clone, Encode, Decode)]
pub struct TestXt<Call, Extra>(pub Option<(u64, Extra)>, pub Call);

impl<Call, Extra> Serialize for TestXt<Call, Extra> where TestXt<Call, Extra>: Encode {
	fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error> where S: Serializer {
		self.using_encoded(|bytes| seq.serialize_bytes(bytes))
	}
}

impl<Call, Extra> Debug for TestXt<Call, Extra> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "TestXt({:?}, ...)", self.0.as_ref().map(|x| &x.0))
	}
}

impl<Call: Codec + Sync + Send, Context, Extra> Checkable<Context> for TestXt<Call, Extra> {
	type Checked = Self;
	fn check(self, _: &Context) -> Result<Self::Checked, &'static str> { Ok(self) }
}
impl<Call: Codec + Sync + Send, Extra> traits::Extrinsic for TestXt<Call, Extra> {
	type Call = Call;

	fn is_signed(&self) -> Option<bool> {
		Some(self.0.is_some())
	}

	fn new_unsigned(_c: Call) -> Option<Self> {
		None
	}
}

impl<Origin, Call, Extra> Applyable for TestXt<Call, Extra> where
	Call: 'static + Sized + Send + Sync + Clone + Eq + Codec + Debug + Dispatchable<Origin=Origin>,
	Extra: SignedExtension<AccountId=u64>,
	Origin: From<Option<u64>>
{
	type AccountId = u64;
	type Call = Call;

	fn sender(&self) -> Option<&u64> { self.0.as_ref().map(|x| &x.0) }

	/// Checks to see if this is a valid *transaction*. It returns information on it if so.
	fn validate<U: ValidateUnsigned<Call=Self::Call>>(&self,
		_info: DispatchInfo,
		_len: usize,
	) -> TransactionValidity {
		TransactionValidity::Valid(Default::default())
	}

	/// Executes all necessary logic needed prior to dispatch and deconstructs into function call,
	/// index and sender.
	fn dispatch(self,
		info: DispatchInfo,
		len: usize,
	) -> Result<DispatchResult, DispatchError> {
		let maybe_who = if let Some((who, extra)) = self.0 {
			Extra::pre_dispatch(extra, &who, info, len)?;
			Some(who)
		} else {
			Extra::pre_dispatch_unsigned(info, len)?;
			None
		};
		Ok(self.1.dispatch(maybe_who.into()))
	}
}

impl<Call: Encode, Extra: Encode> GetDispatchInfo for TestXt<Call, Extra> {
	fn get_dispatch_info(&self) -> DispatchInfo {
		// for testing: weight == size.
		DispatchInfo {
			weight: self.encode().len() as u32,
			..Default::default()
		}
	}
}
