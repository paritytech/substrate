// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Chain RPC Block number type.

use serde::{Serialize, Deserialize};
use std::{convert::TryFrom, fmt::Debug};
use sp_core::U256;

/// RPC Block number type
///
/// We allow two representations of the block number as input.
/// Either we deserialize to the type that is specified in the block type
/// or we attempt to parse given hex value.
/// We do that for consistency with the returned type, default generic header
/// serializes block number as hex to avoid overflows in JavaScript.
#[derive(Serialize, Deserialize, Debug, PartialEq)]
#[serde(untagged)]
pub enum NumberOrHex<Number> {
	/// The original header number type of block.
	Number(Number),
	/// Hex representation of the block number.
	Hex(U256),
}

impl<Number: TryFrom<u64> + From<u32> + Debug + PartialOrd> NumberOrHex<Number> {
	/// Attempts to convert into concrete block number.
	///
	/// Fails in case hex number is too big.
	pub fn to_number(self) -> Result<Number, String> {
		let num = match self {
			NumberOrHex::Number(n) => n,
			NumberOrHex::Hex(h) => {
				let l = h.low_u64();
				if U256::from(l) != h {
					return Err(format!("`{}` does not fit into u64 type; unsupported for now.", h))
				} else {
					Number::try_from(l)
						.map_err(|_| format!("`{}` does not fit into block number type.", h))?
				}
			},
		};
		// FIXME <2329>: Database seems to limit the block number to u32 for no reason
		if num > Number::from(u32::max_value()) {
			return Err(format!("`{:?}` > u32::max_value(), the max block number is u32.", num))
		}
		Ok(num)
	}
}

impl From<u64> for NumberOrHex<u64> {
	fn from(n: u64) -> Self {
		NumberOrHex::Number(n)
	}
}

impl<Number> From<U256> for NumberOrHex<Number> {
	fn from(n: U256) -> Self {
		NumberOrHex::Hex(n)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::assert_deser;

	#[test]
	fn should_serialize_and_deserialize() {
		assert_deser(r#""0x1234""#, NumberOrHex::<u128>::Hex(0x1234.into()));
		assert_deser(r#""0x0""#, NumberOrHex::<u64>::Hex(0.into()));
		assert_deser(r#"5"#, NumberOrHex::Number(5_u64));
		assert_deser(r#"10000"#, NumberOrHex::Number(10000_u32));
		assert_deser(r#"0"#, NumberOrHex::Number(0_u16));
	}
}
