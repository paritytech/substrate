// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Runtime API definition required by Balances RPC extensions.
//!
//! This API should be imported and implemented by the runtime,
//! of a node that wants to use the custom RPC extension
//! adding Balances access methods.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Used to workaround serde serialization/deserialization problems involving `u128`.
///
/// # Types
///
/// * `B`: Balance
#[derive(
    Clone,
    Copy,
    Debug,
    Default,
    Eq,
    Ord,
    PartialEq,
    PartialOrd,
    codec::Decode,
    codec::Encode,
)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
pub struct SerdeWrapper<B>(
    #[cfg_attr(feature = "std", serde(bound(serialize = "B: std::fmt::Display")))]
    #[cfg_attr(feature = "std", serde(serialize_with = "serialize_as_string"))]
    #[cfg_attr(feature = "std", serde(bound(deserialize = "B: std::str::FromStr")))]
    #[cfg_attr(feature = "std", serde(deserialize_with = "deserialize_from_string"))]
    pub B,
);

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

use codec::Codec;
use sp_runtime::traits::{MaybeDisplay, MaybeFromStr};

sp_api::decl_runtime_apis! {
	pub trait BalancesApi<AccountId, Balance> where
		AccountId: Codec,
		Balance: Codec + MaybeDisplay + MaybeFromStr,
	{
		fn free_balance(who: AccountId) -> SerdeWrapper<Balance>;
	}
}
