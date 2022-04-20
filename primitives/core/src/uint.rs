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

//! An unsigned fixed-size integer.

pub use primitive_types::{U256, U512};

#[cfg(test)]
mod tests {
	use super::*;
	use codec::{Decode, Encode};
	use sp_serializer as ser;

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
					($name::from(u64::MAX), "0xffffffffffffffff"),
					($name::from(u64::MAX) + $name::from(1), "0x10000000000000000"),
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
		};
	}

	test!(U256, test_u256);

	#[test]
	fn test_u256_codec() {
		let res1 = vec![
			120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
			0, 0, 0, 0,
		];
		let res2 = vec![
			0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
			0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
			0xff, 0xff, 0xff, 0xff,
		];

		assert_eq!(U256::from(120).encode(), res1);
		assert_eq!(U256::max_value().encode(), res2);
		assert_eq!(U256::decode(&mut &res1[..]), Ok(U256::from(120)));
		assert_eq!(U256::decode(&mut &res2[..]), Ok(U256::max_value()));
	}

	#[test]
	fn test_large_values() {
		assert_eq!(
			ser::to_string_pretty(&!U256::zero()),
			"\"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff\""
		);
		assert!(ser::from_str::<U256>(
			"\"0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff\""
		)
		.unwrap_err()
		.is_data());
	}
}
