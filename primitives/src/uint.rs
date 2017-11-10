// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! An unsigned fixed-size integer.

use std::fmt;
use serde::{de, Serialize, Serializer, Deserialize, Deserializer};

macro_rules! impl_serde {
	($name: ident, $len: expr) => {
		impl Serialize for $name {
			fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: Serializer {
				// TODO [ToDr] Use raw bytes if we switch to RLP / binencoding
				// (serialize_bytes)
				if self.is_zero() {
					// TODO [ToDr] LowerHex of 0 is broken
					serializer.serialize_str("0x0")
				} else {
					serializer.serialize_str(&format!("{:#x}", self))
				}
			}
		}

		impl<'de> Deserialize<'de> for $name {
			fn deserialize<D>(deserializer: D) -> Result<Self, D::Error> where D: Deserializer<'de> {
				struct Visitor;
				impl<'a> de::Visitor<'a> for Visitor {
					type Value = $name;

					fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
						write!(formatter, "a 0x-prefixed hex string")
					}

					fn visit_str<E: de::Error>(self, v: &str) -> Result<Self::Value, E> {
						if v.len() < 2  || &v[0..2] != "0x" {
							return Err(E::custom("prefix is missing"))
						}

						// 0x + len
						if v.len() > 2 + $len * 16 {
							return Err(E::invalid_length(v.len() - 2, &self));
						}

						let v = if v.len() % 2 == 0 { v[2..].to_owned() } else { format!("0{}", &v[2..]) };
						let bytes = ::rustc_hex::FromHex::from_hex(v.as_str())
							.map_err(|e| E::custom(&format!("invalid hex value: {:?}", e)))?;
						Ok((&*bytes).into())
					}

					fn visit_string<E: de::Error>(self, v: String) -> Result<Self::Value, E> {
						self.visit_str(&v)
					}
				}
				// TODO [ToDr] Use raw bytes if we switch to RLP / binencoding
				// (visit_bytes, visit_bytes_buf)
				deserializer.deserialize_str(Visitor)
			}
		}
	}
}

construct_uint!(U256, 4);
impl_serde!(U256, 4);
construct_uint!(U512, 8);
impl_serde!(U512, 8);

#[cfg(test)]
mod tests {
	use super::*;
	use polkadot_serializer as ser;

	macro_rules! test {
		($name: ident, $test_name: ident) => {
			#[test]
			fn $test_name() {
				let tests = vec![
					($name::from(0), "0x0"),
					($name::from(1), "0x1"),
					($name::from(2), "0x2"),
					($name::from(10), "0xa"),
					($name::from(15), "0xf"),
					($name::from(15), "0xf"),
					($name::from(16), "0x10"),
					($name::from(1_000), "0x3e8"),
					($name::from(100_000), "0x186a0"),
					($name::from(u64::max_value()), "0xffffffffffffffff"),
					($name::from(u64::max_value()) + 1.into(), "0x10000000000000000"),
				];

				for (number, expected) in tests {
					assert_eq!(format!("{:?}", expected), ser::to_string_pretty(&number));
					assert_eq!(number, ser::from_str(&format!("{:?}", expected)).unwrap());
				}
			}
		}
	}

	test!(U256, test_u256);
	test!(U512, test_u512);
}
