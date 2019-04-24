// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
use serde_derive::Deserialize;
use primitives::U256;
use runtime_primitives::traits;

/// RPC Block number type
///
/// We allow two representations of the block number as input.
/// Either we deserialize to the type that is specified in the block type
/// or we attempt to parse given hex value.
/// We do that for consistency with the returned type, default generic header
/// serializes block number as hex to avoid overflows in JavaScript.
#[derive(Deserialize)]
#[serde(untagged)]
pub enum NumberOrHex<Number> {
	/// The original header number type of block.
	Number(Number),
	/// Hex representation of the block number.
	Hex(U256),
}

impl<Number: traits::As<u64>> NumberOrHex<Number> {
	/// Attempts to convert into concrete block number.
	///
	/// Fails in case hex number is too big.
	pub fn to_number(self) -> Result<Number, String> {
		match self {
			NumberOrHex::Number(n) => Ok(n),
			NumberOrHex::Hex(h) => {
				// FIXME #1377 this only supports `u64` since `BlockNumber`
				// is `As<u64>` we could possibly go with `u128`.
				let l = h.low_u64();
				if U256::from(l) != h {
					Err(format!("`{}` does not fit into the block number type.", h))
				} else {
					Ok(traits::As::sa(l))
				}
			},
		}
	}
}

#[cfg(test)]
impl From<u64> for NumberOrHex<u64> {
	fn from(n: u64) -> Self {
		NumberOrHex::Number(n)
	}
}

#[cfg(test)]
impl<Number> From<U256> for NumberOrHex<Number> {
	fn from(n: U256) -> Self {
		NumberOrHex::Hex(n)
	}
}
