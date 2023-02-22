// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
	use sp_serializer as ser;

	#[test]
	fn test_h160() {
		let tests = vec![
			(Default::default(), "0x0000000000000000000000000000000000000000"),
			(H160::from_low_u64_be(2), "0x0000000000000000000000000000000000000002"),
			(H160::from_low_u64_be(15), "0x000000000000000000000000000000000000000f"),
			(H160::from_low_u64_be(16), "0x0000000000000000000000000000000000000010"),
			(H160::from_low_u64_be(1_000), "0x00000000000000000000000000000000000003e8"),
			(H160::from_low_u64_be(100_000), "0x00000000000000000000000000000000000186a0"),
			(H160::from_low_u64_be(u64::MAX), "0x000000000000000000000000ffffffffffffffff"),
		];

		for (number, expected) in tests {
			assert_eq!(format!("{:?}", expected), ser::to_string_pretty(&number));
			assert_eq!(number, ser::from_str(&format!("{:?}", expected)).unwrap());
		}
	}

	#[test]
	fn test_h256() {
		let tests = vec![
			(
				Default::default(),
				"0x0000000000000000000000000000000000000000000000000000000000000000",
			),
			(
				H256::from_low_u64_be(2),
				"0x0000000000000000000000000000000000000000000000000000000000000002",
			),
			(
				H256::from_low_u64_be(15),
				"0x000000000000000000000000000000000000000000000000000000000000000f",
			),
			(
				H256::from_low_u64_be(16),
				"0x0000000000000000000000000000000000000000000000000000000000000010",
			),
			(
				H256::from_low_u64_be(1_000),
				"0x00000000000000000000000000000000000000000000000000000000000003e8",
			),
			(
				H256::from_low_u64_be(100_000),
				"0x00000000000000000000000000000000000000000000000000000000000186a0",
			),
			(
				H256::from_low_u64_be(u64::MAX),
				"0x000000000000000000000000000000000000000000000000ffffffffffffffff",
			),
		];

		for (number, expected) in tests {
			assert_eq!(format!("{:?}", expected), ser::to_string_pretty(&number));
			assert_eq!(number, ser::from_str(&format!("{:?}", expected)).unwrap());
		}
	}

	#[test]
	fn test_invalid() {
		assert!(ser::from_str::<H256>(
			"\"0x000000000000000000000000000000000000000000000000000000000000000\""
		)
		.unwrap_err()
		.is_data());
		assert!(ser::from_str::<H256>(
			"\"0x000000000000000000000000000000000000000000000000000000000000000g\""
		)
		.unwrap_err()
		.is_data());
		assert!(ser::from_str::<H256>(
			"\"0x00000000000000000000000000000000000000000000000000000000000000000\""
		)
		.unwrap_err()
		.is_data());
		assert!(ser::from_str::<H256>("\"\"").unwrap_err().is_data());
		assert!(ser::from_str::<H256>("\"0\"").unwrap_err().is_data());
		assert!(ser::from_str::<H256>("\"10\"").unwrap_err().is_data());
	}
}
