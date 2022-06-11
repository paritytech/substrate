// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! MultiAddress type is a wrapper for multiple downstream account formats.

use codec::{Decode, Encode, MaxEncodedLen};

/// A numch of raw bytes.
#[derive(PartialEq, Eq, Clone, crate::RuntimeDebug, scale_info::TypeInfo)]
#[cfg_attr(feature = "std", derive(Hash))]
pub struct RawAddress(Vec<u8>);

impl Decode for RawAddress {
	fn decode<I: codec::Input>(value: &mut I) -> Result<Self, codec::Error> {
		let inner = Vec::<u8>::decode(value)?;
		if inner.len() > 64 {
			return Err("`RawAddress` too long".into())
		}
		Ok(Self(inner))
	}
}

impl Encode for RawAddress {
	fn encode_to<T: codec::Output + ?Sized>(&self, output: &mut T) {
		// ensure it's no greater than 64 bytes.
		(&self.0[0..64]).encode_to(output)
	}
}

impl MaxEncodedLen for RawAddress {
	fn max_encoded_len() -> usize {
		65
	}
}

/// A multi-format address wrapper for on-chain accounts.
#[derive(
	Encode, Decode, PartialEq, Eq, Clone, crate::RuntimeDebug, scale_info::TypeInfo, MaxEncodedLen,
)]
#[cfg_attr(feature = "std", derive(Hash))]
pub enum MultiAddress<AccountId, AccountIndex: MaxEncodedLen> {
	/// It's an account ID (pubkey).
	Id(AccountId),
	/// It's an account index.
	Index(#[codec(compact)] AccountIndex),
	/// It's up to 64 raw bytes.
	Raw(RawAddress),
	/// It's a 32 byte representation.
	Address32([u8; 32]),
	/// Its a 20 byte representation.
	Address20([u8; 20]),
}

#[cfg(feature = "std")]
impl<AccountId, AccountIndex> std::fmt::Display for MultiAddress<AccountId, AccountIndex>
where
	AccountId: std::fmt::Debug,
	AccountIndex: std::fmt::Debug + MaxEncodedLen,
{
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		use sp_core::hexdisplay::HexDisplay;
		match self {
			Self::Raw(inner) => write!(f, "MultiAddress::Raw({})", HexDisplay::from(&inner.0)),
			Self::Address32(inner) => {
				write!(f, "MultiAddress::Address32({})", HexDisplay::from(inner))
			},
			Self::Address20(inner) => {
				write!(f, "MultiAddress::Address20({})", HexDisplay::from(inner))
			},
			_ => write!(f, "{:?}", self),
		}
	}
}

impl<AccountId, AccountIndex: MaxEncodedLen> From<AccountId>
	for MultiAddress<AccountId, AccountIndex>
{
	fn from(a: AccountId) -> Self {
		Self::Id(a)
	}
}
