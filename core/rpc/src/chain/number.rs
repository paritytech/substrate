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

use primitives::U256;
use runtime_primitives::traits;
use serde_derive::Deserialize;

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
            }
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
