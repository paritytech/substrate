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

//! A number type that can be serialized both as a number or a string that encodes a number in a
//! string.

use serde::{Deserialize, Serialize};
use sp_core::U256;
use std::{
	convert::{TryFrom, TryInto},
	fmt::Debug,
};

/// A number type that can be serialized both as a number or a string that encodes a number in a
/// string.
///
/// We allow two representations of the block number as input. Either we deserialize to the type
/// that is specified in the block type or we attempt to parse given hex value.
///
/// The primary motivation for having this type is to avoid overflows when using big integers in
/// JavaScript (which we consider as an important RPC API consumer).
#[derive(Copy, Clone, Serialize, Deserialize, Debug, PartialEq)]
#[serde(untagged)]
pub enum NumberOrHex {
	/// The number represented directly.
	Number(u64),
	/// Hex representation of the number.
	Hex(U256),
}

impl Default for NumberOrHex {
	fn default() -> Self {
		Self::Number(Default::default())
	}
}

impl NumberOrHex {
	/// Converts this number into an U256.
	pub fn into_u256(self) -> U256 {
		match self {
			NumberOrHex::Number(n) => n.into(),
			NumberOrHex::Hex(h) => h,
		}
	}
}

impl From<u32> for NumberOrHex {
	fn from(n: u32) -> Self {
		NumberOrHex::Number(n.into())
	}
}

impl From<u64> for NumberOrHex {
	fn from(n: u64) -> Self {
		NumberOrHex::Number(n)
	}
}

impl From<u128> for NumberOrHex {
	fn from(n: u128) -> Self {
		NumberOrHex::Hex(n.into())
	}
}

impl From<U256> for NumberOrHex {
	fn from(n: U256) -> Self {
		NumberOrHex::Hex(n)
	}
}

/// An error type that signals an out-of-range conversion attempt.
pub struct TryFromIntError(pub(crate) ());

impl TryFrom<NumberOrHex> for u32 {
	type Error = TryFromIntError;
	fn try_from(num_or_hex: NumberOrHex) -> Result<u32, Self::Error> {
		num_or_hex.into_u256().try_into().map_err(|_| TryFromIntError(()))
	}
}

impl TryFrom<NumberOrHex> for u64 {
	type Error = TryFromIntError;
	fn try_from(num_or_hex: NumberOrHex) -> Result<u64, Self::Error> {
		num_or_hex.into_u256().try_into().map_err(|_| TryFromIntError(()))
	}
}

impl TryFrom<NumberOrHex> for u128 {
	type Error = TryFromIntError;
	fn try_from(num_or_hex: NumberOrHex) -> Result<u128, Self::Error> {
		num_or_hex.into_u256().try_into().map_err(|_| TryFromIntError(()))
	}
}

impl From<NumberOrHex> for U256 {
	fn from(num_or_hex: NumberOrHex) -> U256 {
		num_or_hex.into_u256()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::assert_deser;

	#[test]
	fn should_serialize_and_deserialize() {
		assert_deser(r#""0x1234""#, NumberOrHex::Hex(0x1234.into()));
		assert_deser(r#""0x0""#, NumberOrHex::Hex(0.into()));
		assert_deser(r#"5"#, NumberOrHex::Number(5));
		assert_deser(r#"10000"#, NumberOrHex::Number(10000));
		assert_deser(r#"0"#, NumberOrHex::Number(0));
		assert_deser(r#"1000000000000"#, NumberOrHex::Number(1000000000000));
	}
}
