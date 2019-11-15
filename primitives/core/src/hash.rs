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

//! A fixed hash type.

pub use primitive_types::{H160, H256, H512};

/// Hash conversion. Used to convert between unbound associated hash types in traits,
/// implemented by the same hash type.
/// Panics if used to convert between different hash types.
pub fn convert_hash<H1: Default + AsMut<[u8]>, H2: AsRef<[u8]>>(src: &H2) -> H1 {
	let mut dest = H1::default();
	assert_eq!(dest.as_mut().len(), src.as_ref().len());
	dest.as_mut().copy_from_slice(src.as_ref());
	dest
}

#[cfg(test)]
mod tests {
	use super::*;
	use substrate_serializer as ser;

	#[test]
	fn test_h160() {
		let tests = vec![
			(Default::default(), "0x0000000000000000000000000000000000000000"),
			(H160::from_low_u64_be(2), "0x0000000000000000000000000000000000000002"),
			(H160::from_low_u64_be(15), "0x000000000000000000000000000000000000000f"),
			(H160::from_low_u64_be(16), "0x0000000000000000000000000000000000000010"),
			(H160::from_low_u64_be(1_000), "0x00000000000000000000000000000000000003e8"),
			(H160::from_low_u64_be(100_000), "0x00000000000000000000000000000000000186a0"),
			(H160::from_low_u64_be(u64::max_value()), "0x000000000000000000000000ffffffffffffffff"),
		];

		for (number, expected) in tests {
			assert_eq!(format!("{:?}", expected), ser::to_string_pretty(&number));
			assert_eq!(number, ser::from_str(&format!("{:?}", expected)).unwrap());
		}
	}

	#[test]
	fn test_h256() {
		let tests = vec![
			(Default::default(), "0x0000000000000000000000000000000000000000000000000000000000000000"),
			(H256::from_low_u64_be(2), "0x0000000000000000000000000000000000000000000000000000000000000002"),
			(H256::from_low_u64_be(15), "0x000000000000000000000000000000000000000000000000000000000000000f"),
			(H256::from_low_u64_be(16), "0x0000000000000000000000000000000000000000000000000000000000000010"),
			(H256::from_low_u64_be(1_000), "0x00000000000000000000000000000000000000000000000000000000000003e8"),
			(H256::from_low_u64_be(100_000), "0x00000000000000000000000000000000000000000000000000000000000186a0"),
			(H256::from_low_u64_be(u64::max_value()), "0x000000000000000000000000000000000000000000000000ffffffffffffffff"),
		];

		for (number, expected) in tests {
			assert_eq!(format!("{:?}", expected), ser::to_string_pretty(&number));
			assert_eq!(number, ser::from_str(&format!("{:?}", expected)).unwrap());
		}
	}

	#[test]
	fn test_invalid() {
		assert!(ser::from_str::<H256>("\"0x000000000000000000000000000000000000000000000000000000000000000\"").unwrap_err().is_data());
		assert!(ser::from_str::<H256>("\"0x000000000000000000000000000000000000000000000000000000000000000g\"").unwrap_err().is_data());
		assert!(ser::from_str::<H256>("\"0x00000000000000000000000000000000000000000000000000000000000000000\"").unwrap_err().is_data());
		assert!(ser::from_str::<H256>("\"\"").unwrap_err().is_data());
		assert!(ser::from_str::<H256>("\"0\"").unwrap_err().is_data());
		assert!(ser::from_str::<H256>("\"10\"").unwrap_err().is_data());
	}
}
