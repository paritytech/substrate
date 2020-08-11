// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! The for various partial storage decoders

use super::*;
use frame_support::storage::{migration, StorageMap, unhashed};

#[test]
fn test_decode_compact_u32_at() {
	new_test_ext().execute_with(|| {
		let v = codec::Compact(u64::max_value());
		migration::put_storage_value(b"test", b"", &[], v);
		assert_eq!(decode_compact_u32_at(b"test"), None);

		for v in vec![0, 10, u32::max_value()] {
			let compact_v = codec::Compact(v);
			unhashed::put(b"test", &compact_v);
			assert_eq!(decode_compact_u32_at(b"test"), Some(v));
		}

		unhashed::kill(b"test");
		assert_eq!(decode_compact_u32_at(b"test"), None);
	})
}

#[test]
fn len_of_deposit_of() {
	new_test_ext().execute_with(|| {
		for l in vec![0, 1, 200, 1000] {
			let value: (Vec<u64>, u64) = ((0..l).map(|_| Default::default()).collect(), 3u64);
			DepositOf::<Test>::insert(2, value);
			assert_eq!(Democracy::len_of_deposit_of(2), Some(l));
		}

		DepositOf::<Test>::remove(2);
		assert_eq!(Democracy::len_of_deposit_of(2), None);
	})
}

#[test]
fn pre_image() {
	new_test_ext().execute_with(|| {
		let key = Default::default();
		let missing = PreimageStatus::Missing(0);
		Preimages::<Test>::insert(key, missing);
		assert!(Democracy::pre_image_data_len(key).is_err());
		assert_eq!(Democracy::check_pre_image_is_missing(key), Ok(()));

		Preimages::<Test>::remove(key);
		assert!(Democracy::pre_image_data_len(key).is_err());
		assert!(Democracy::check_pre_image_is_missing(key).is_err());

		for l in vec![0, 10, 100, 1000u32] {
			let available = PreimageStatus::Available{
				data: (0..l).map(|i| i as u8).collect(),
				provider: 0,
				deposit: 0,
				since: 0,
				expiry: None,
			};

			Preimages::<Test>::insert(key, available);
			assert_eq!(Democracy::pre_image_data_len(key), Ok(l));
			assert!(Democracy::check_pre_image_is_missing(key).is_err());
		}
	})
}
