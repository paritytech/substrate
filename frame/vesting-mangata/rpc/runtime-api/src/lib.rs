// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Runtime API definition for transaction payment pallet.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Codec, Decode, Encode};

#[cfg(not(feature = "std"))]
use sp_std::{vec, vec::Vec};

#[cfg(feature = "std")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use sp_runtime::traits::{MaybeDisplay, MaybeFromStr};

pub use pallet_vesting_mangata::{VestingInfo};

sp_api::decl_runtime_apis! {
	pub trait VestingMangataApi<AccountId, TokenId, Balance, BlockNumber> where
		AccountId: Codec + MaybeDisplay,
		Balance: Codec + MaybeDisplay,
		TokenId: Codec + MaybeDisplay,
		BlockNumber: Codec + MaybeDisplay,
	{
		fn get_vesting_locked_at(who: AccountId, token_id: TokenId, at_block_number: Option<BlockNumber>) -> VestingInfosWithLockedAt<Balance, BlockNumber>;
	}
}

#[cfg(feature = "std")]
fn serialize_as_string<S: Serializer, T: std::fmt::Display>(
	t: &T,
	serializer: S,
) -> Result<S::Ok, S::Error> {
	serializer.serialize_str(&t.to_string())
}

#[cfg(feature = "std")]
fn deserialize_from_string<'de, D: Deserializer<'de>, T: std::str::FromStr>(
	deserializer: D,
) -> Result<T, D::Error> {
	let s = String::deserialize(deserializer)?;
	s.parse::<T>().map_err(|_| serde::de::Error::custom("Parse from string failed"))
}

// Workaround for substrate/serde issue
#[derive(Eq, PartialEq, Encode, Decode, Default)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
pub struct VestingInfosWithLockedAt<Balance, BlockNumber> {
	#[cfg_attr(feature = "std", serde(bound(serialize = "Vec<(VestingInfo<Balance, BlockNumber>, Balance)>: std::fmt::Display")))]
	#[cfg_attr(feature = "std", serde(serialize_with = "serialize_as_string"))]
	#[cfg_attr(feature = "std", serde(bound(deserialize = "Vec<(VestingInfo<Balance, BlockNumber>, Balance)>: std::str::FromStr")))]
	#[cfg_attr(feature = "std", serde(deserialize_with = "deserialize_from_string"))]
	pub vesting_infos_with_locked_at: Vec<(VestingInfo<Balance, BlockNumber>, Balance)>,
}

