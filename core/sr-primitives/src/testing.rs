// Copyright 2017 Parity Technologies (UK) Ltd.
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

use serde::{Serialize, de::DeserializeOwned};
use std::fmt::Debug;
use codec::Codec;
use traits::{self, Checkable, Applyable, BlakeTwo256};
use generic::DigestItem as GenDigestItem;

pub use substrate_primitives::H256;

pub type DigestItem = GenDigestItem<H256, u64>;

#[derive(Default, PartialEq, Eq, Clone, Serialize, Deserialize, Debug, Encode, Decode)]
pub struct Digest {
	pub logs: Vec<DigestItem>,
}

impl traits::Digest for Digest {
	type Hash = H256;
	type Item = DigestItem;

	fn logs(&self) -> &[Self::Item] {
		&self.logs
	}

	fn push(&mut self, item: Self::Item) {
		self.logs.push(item);
	}
}

#[derive(PartialEq, Eq, Clone, Serialize, Deserialize, Debug, Encode, Decode)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct Header {
	pub parent_hash: H256,
	pub number: u64,
	pub state_root: H256,
	pub extrinsics_root: H256,
	pub digest: Digest,
}

impl traits::Header for Header {
	type Number = u64;
	type Hashing = BlakeTwo256;
	type Hash = H256;
	type Digest = Digest;

	fn number(&self) -> &Self::Number { &self.number }
	fn set_number(&mut self, num: Self::Number) { self.number = num }

	fn extrinsics_root(&self) -> &Self::Hash { &self.extrinsics_root }
	fn set_extrinsics_root(&mut self, root: Self::Hash) { self.extrinsics_root = root }

	fn state_root(&self) -> &Self::Hash { &self.state_root }
	fn set_state_root(&mut self, root: Self::Hash) { self.state_root = root }

	fn parent_hash(&self) -> &Self::Hash { &self.parent_hash }
	fn set_parent_hash(&mut self, hash: Self::Hash) { self.parent_hash = hash }

	fn digest(&self) -> &Self::Digest { &self.digest }
	fn set_digest(&mut self, digest: Self::Digest) { self.digest = digest }

	fn new(
		number: Self::Number,
		extrinsics_root: Self::Hash,
		state_root: Self::Hash,
		parent_hash: Self::Hash,
		digest: Self::Digest
	) -> Self {
		Header {
			number,
			extrinsics_root: extrinsics_root,
			state_root,
			parent_hash,
			digest
		}
	}
}

#[derive(PartialEq, Eq, Clone, Serialize, Deserialize, Debug, Encode, Decode)]
pub struct Block<Xt> {
	pub header: Header,
	pub extrinsics: Vec<Xt>,
}

impl<Xt: 'static + Codec + Sized + Send + Sync + Serialize + DeserializeOwned + Clone + Eq + Debug> traits::Block for Block<Xt> {
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

#[derive(PartialEq, Eq, Clone, Serialize, Deserialize, Debug, Encode, Decode)]
pub struct TestXt<Call>(pub Option<u64>, pub u64, pub Call);

impl<Call: Codec + Sync + Send + Serialize, Context> Checkable<Context> for TestXt<Call> {
	type Checked = Self;
	fn check(self, _: &Context) -> Result<Self::Checked, &'static str> { Ok(self) }
}
impl<Call> Applyable for TestXt<Call> where
	Call: 'static + Sized + Send + Sync + Clone + Eq + Codec + Debug + Serialize + DeserializeOwned,
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
