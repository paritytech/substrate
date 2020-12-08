// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! Runtime API definition for transaction payment module.

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use codec::{Encode, Codec, Decode};
#[cfg(feature = "std")]
use serde::{Serialize, Deserialize, Serializer, Deserializer};
use sp_runtime::traits::{MaybeDisplay, MaybeFromStr};

/// Information related to a dispatchable's class, weight, and fee that can be queried from the runtime.
#[derive(Eq, PartialEq, Encode, Decode, Default)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
pub struct RuntimeDispatchInfo<Weight, DispatchClass, Balance> {
	/// Weight of this dispatch.
	pub weight: Weight,
	/// Class of this dispatch.
	pub class: DispatchClass,
	/// The inclusion fee of this dispatch. This does not include a tip or anything else that
	/// depends on the signature (i.e. depends on a `SignedExtension`).
	#[cfg_attr(feature = "std", serde(bound(serialize = "Balance: std::fmt::Display")))]
	#[cfg_attr(feature = "std", serde(serialize_with = "serialize_as_string"))]
	#[cfg_attr(feature = "std", serde(bound(deserialize = "Balance: std::str::FromStr")))]
	#[cfg_attr(feature = "std", serde(deserialize_with = "deserialize_from_string"))]
	pub partial_fee: Balance,
}

#[cfg(feature = "std")]
fn serialize_as_string<S: Serializer, T: std::fmt::Display>(t: &T, serializer: S) -> Result<S::Ok, S::Error> {
	serializer.serialize_str(&t.to_string())
}

#[cfg(feature = "std")]
fn deserialize_from_string<'de, D: Deserializer<'de>, T: std::str::FromStr>(deserializer: D) -> Result<T, D::Error> {
	let s = String::deserialize(deserializer)?;
	s.parse::<T>().map_err(|_| serde::de::Error::custom("Parse from string failed"))
}

sp_api::decl_runtime_apis! {
	pub trait TransactionPaymentApi<Weight, DispatchClass, Balance> where
		Weight: Codec,
		DispatchClass: Codec,
		Balance: Codec + MaybeDisplay + MaybeFromStr,
	{
		fn query_info(uxt: Block::Extrinsic, len: u32) -> RuntimeDispatchInfo<Weight, DispatchClass, Balance>;
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use frame_support::weights::DispatchClass;

	#[test]
	fn should_serialize_and_deserialize_properly_with_string() {
		let info = RuntimeDispatchInfo {
			weight: 5,
			class: DispatchClass::Normal,
			partial_fee: 1_000_000_u64,
		};

		let json_str = r#"{"weight":5,"class":"normal","partialFee":"1000000"}"#;

		assert_eq!(serde_json::to_string(&info).unwrap(), json_str);
		assert_eq!(serde_json::from_str::<RuntimeDispatchInfo<u64, DispatchClass, u64>>(json_str).unwrap(), info);

		// should not panic
		serde_json::to_value(&info).unwrap();
	}

	#[test]
	fn should_serialize_and_deserialize_properly_large_value() {
		let info = RuntimeDispatchInfo {
			weight: 5,
			class: DispatchClass::Normal,
			partial_fee: u128::max_value(),
		};

		let json_str = r#"{"weight":5,"class":"normal","partialFee":"340282366920938463463374607431768211455"}"#;

		assert_eq!(serde_json::to_string(&info).unwrap(), json_str);
		assert_eq!(serde_json::from_str::<RuntimeDispatchInfo<u64, DispatchClass, u128>>(json_str).unwrap(), info);

		// should not panic
		serde_json::to_value(&info).unwrap();
	}
}
