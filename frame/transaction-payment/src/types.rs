// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! Types for transaction-payment RPC.

use codec::{Encode, Decode};
#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};

use sp_runtime::traits::{AtLeast32BitUnsigned, Zero};
use sp_std::prelude::*;

use frame_support::weights::{Weight, DispatchClass};

/// The base fee and adjusted weight and length fees constitute the _inclusion fee_.
#[derive(Encode, Decode, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
pub struct InclusionFee<Balance> {
	/// This is the minimum amount a user pays for a transaction. It is declared
	/// as a base _weight_ in the runtime and converted to a fee using `WeightToFee`.
	pub base_fee: Balance,
	/// The length fee, the amount paid for the encoded length (in bytes) of the transaction.
	pub len_fee: Balance,
	/// - `targeted_fee_adjustment`: This is a multiplier that can tune the final fee based on
	///     the congestion of the network.
	/// - `weight_fee`: This amount is computed based on the weight of the transaction. Weight
	/// accounts for the execution time of a transaction.
	///
	/// adjusted_weight_fee = targeted_fee_adjustment * weight_fee
	pub adjusted_weight_fee: Balance,
}

impl<Balance: AtLeast32BitUnsigned + Copy> InclusionFee<Balance> {
	/// Returns the total of inclusion fee.
	///
	/// ```ignore
	/// inclusion_fee = base_fee + len_fee + adjusted_weight_fee
	/// ```
	pub fn inclusion_fee(&self) -> Balance {
		self.base_fee
			.saturating_add(self.len_fee)
			.saturating_add(self.adjusted_weight_fee)
	}
}

/// The `FeeDetails` is composed of:
///   - (Optional) `inclusion_fee`: Only the `Pays::Yes` transaction can have the inclusion fee.
///   - `tip`: If included in the transaction, the tip will be added on top. Only
///     signed transactions can have a tip.
#[derive(Encode, Decode, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
pub struct FeeDetails<Balance> {
	/// The minimum fee for a transaction to be included in a block.
	pub inclusion_fee: Option<InclusionFee<Balance>>,
	// Do not serialize and deserialize `tip` as we actually can not pass any tip to the RPC.
	#[cfg_attr(feature = "std", serde(skip))]
	pub tip: Balance,
}

impl<Balance: AtLeast32BitUnsigned + Copy> FeeDetails<Balance> {
	/// Returns the final fee.
	///
	/// ```ignore
	/// final_fee = inclusion_fee + tip;
	/// ```
	pub fn final_fee(&self) -> Balance {
		self.inclusion_fee.as_ref().map(|i| i.inclusion_fee()).unwrap_or_else(|| Zero::zero()).saturating_add(self.tip)
	}
}

/// Information related to a dispatchable's class, weight, and fee that can be queried from the runtime.
#[derive(Eq, PartialEq, Encode, Decode, Default)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(bound(serialize = "Balance: std::fmt::Display")))]
#[cfg_attr(feature = "std", serde(bound(deserialize = "Balance: std::str::FromStr")))]
pub struct RuntimeDispatchInfo<Balance> {
	/// Weight of this dispatch.
	pub weight: Weight,
	/// Class of this dispatch.
	pub class: DispatchClass,
	/// The inclusion fee of this dispatch.
	///
	/// This does not include a tip or anything else that
	/// depends on the signature (i.e. depends on a `SignedExtension`).
	#[cfg_attr(feature = "std", serde(with = "serde_balance"))]
	pub partial_fee: Balance,
}

#[cfg(feature = "std")]
mod serde_balance {
	use serde::{Deserialize, Serializer, Deserializer};

	pub fn serialize<S: Serializer, T: std::fmt::Display>(t: &T, serializer: S) -> Result<S::Ok, S::Error> {
		serializer.serialize_str(&t.to_string())
	}

	pub fn deserialize<'de, D: Deserializer<'de>, T: std::str::FromStr>(deserializer: D) -> Result<T, D::Error> {
		let s = String::deserialize(deserializer)?;
		s.parse::<T>().map_err(|_| serde::de::Error::custom("Parse from string failed"))
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn should_serialize_and_deserialize_properly_with_string() {
		let info = RuntimeDispatchInfo {
			weight: 5,
			class: DispatchClass::Normal,
			partial_fee: 1_000_000_u64,
		};

		let json_str = r#"{"weight":5,"class":"normal","partialFee":"1000000"}"#;

		assert_eq!(serde_json::to_string(&info).unwrap(), json_str);
		assert_eq!(serde_json::from_str::<RuntimeDispatchInfo<u64>>(json_str).unwrap(), info);

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
		assert_eq!(serde_json::from_str::<RuntimeDispatchInfo<u128>>(json_str).unwrap(), info);

		// should not panic
		serde_json::to_value(&info).unwrap();
	}
}
