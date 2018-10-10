// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! An unsigned fixed-size integer.

#[cfg(feature = "std")]
use serde::{Serialize, Serializer, Deserialize, Deserializer};

#[cfg(feature = "std")]
use bytes;

macro_rules! impl_serde {
	($name: ident, $len: expr) => {
		#[cfg(feature = "std")]
		impl Serialize for $name {
			fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: Serializer {
				let mut bytes = [0u8; $len * 8];
				self.to_big_endian(&mut bytes);
				bytes::serialize_uint(&bytes, serializer)
			}
		}

		#[cfg(feature = "std")]
		impl<'de> Deserialize<'de> for $name {
			fn deserialize<D>(deserializer: D) -> Result<Self, D::Error> where D: Deserializer<'de> {
				bytes::deserialize_check_len(deserializer, bytes::ExpectedLen::Between(0, $len * 8))
					.map(|x| (&*x).into())
			}
		}
	}
}

macro_rules! impl_codec {
	($name: ident, $len: expr) => {
		impl ::codec::Encode for $name {
			fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
				let mut bytes = [0u8; $len * 8];
				self.to_little_endian(&mut bytes);
				bytes.using_encoded(f)
			}
		}

		impl ::codec::Decode for $name {
			fn decode<I: ::codec::Input>(input: &mut I) -> Option<Self> {
				<[u8; $len * 8] as ::codec::Decode>::decode(input)
					.map(|b| $name::from_little_endian(&b))
			}
		}
	}
}

construct_uint!(U256, 4);
impl_serde!(U256, 4);
impl_codec!(U256, 4);

#[cfg(test)]
mod tests {
	use super::*;
	use codec::{Encode, Decode};
	use substrate_serializer as ser;

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
					($name::from(u64::max_value()) + $name::from(1), "0x10000000000000000"),
				];

				for (number, expected) in tests {
					assert_eq!(format!("{:?}", expected), ser::to_string_pretty(&number));
					assert_eq!(number, ser::from_str(&format!("{:?}", expected)).unwrap());
				}

				// Invalid examples
				assert!(ser::from_str::<$name>("\"0x\"").unwrap_err().is_data());
				assert!(ser::from_str::<$name>("\"0xg\"").unwrap_err().is_data());
				assert!(ser::from_str::<$name>("\"\"").unwrap_err().is_data());
				assert!(ser::from_str::<$name>("\"10\"").unwrap_err().is_data());
				assert!(ser::from_str::<$name>("\"0\"").unwrap_err().is_data());
			}
		}
	}

	test!(U256, test_u256);

	#[test]
	fn test_u256_codec() {
		let res1 = vec![120, 0, 0, 0, 0, 0, 0, 0,
						0, 0, 0, 0, 0, 0, 0, 0,
						0, 0, 0, 0, 0, 0, 0, 0,
						0, 0, 0, 0, 0, 0, 0, 0];
		let res2 = vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
						0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
						0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
						0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff];

		assert_eq!(
			U256::from(120).encode(),
			res1);
		assert_eq!(
			U256::max_value().encode(),
			res2);
		assert_eq!(
			U256::decode(&mut &res1[..]),
			Some(U256::from(120)));
		assert_eq!(
			U256::decode(&mut &res2[..]),
			Some(U256::max_value()));
	}

	#[test]
	fn test_large_values() {
		assert_eq!(
			ser::to_string_pretty(&!U256::zero()),
			"\"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff\""
		);
		assert!(
			ser::from_str::<U256>("\"0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff\"").unwrap_err().is_data()
		);
	}
}
