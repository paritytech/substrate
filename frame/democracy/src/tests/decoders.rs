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

//! The for various partial storage decoders

use super::*;
use frame_support::{storage::migration, storage::{StorageMap, StorageValue}};

#[test]
fn len_of_public_props() {
	new_test_ext().execute_with(|| {
		let value: Vec<(PropIndex, H256, u64)> = (0..10).map(|_| Default::default()).collect();
		PublicProps::<Test>::put(value);
		assert_eq!(Democracy::len_of_public_props(), 10);

		PublicProps::<Test>::kill();
		assert_eq!(Democracy::len_of_public_props(), 0);

		let v = codec::Compact(u64::max_value());
		migration::put_storage_value(b"Democracy", b"PublicProps", &[], v);
		assert_eq!(Democracy::len_of_public_props(), 0);
	})
}

#[test]
fn len_of_deposit_of() {
	new_test_ext().execute_with(|| {
		let value: (Vec<u64>, u64) = ((0..3).map(|_| Default::default()).collect(), 3u64);
		DepositOf::<Test>::insert(2, value);
		assert_eq!(Democracy::len_of_deposit_of(2), Some(3));

		DepositOf::<Test>::remove(2);
		assert_eq!(Democracy::len_of_deposit_of(2), None);
	})
}

#[test]
fn pre_image() {
	new_test_ext().execute_with(|| {
		let key = Default::default();
		let missing = PreimageStatus::Missing(0);
		let available = PreimageStatus::Available{
			data: (0..10u8).collect(),
			provider: 0,
			deposit: 0,
			since: 0,
			expiry: None,
		};

		Preimages::<Test>::insert(key, missing);
		assert!(Democracy::pre_image_data_len(key).is_err());
		assert_eq!(Democracy::check_pre_image_is_missing(key), Ok(()));

		Preimages::<Test>::remove(key);
		assert!(Democracy::pre_image_data_len(key).is_err());
		assert!(Democracy::check_pre_image_is_missing(key).is_err());

		Preimages::<Test>::insert(key, available);
		assert_eq!(Democracy::pre_image_data_len(key), Ok(10));
		assert!(Democracy::check_pre_image_is_missing(key).is_err());
	})
}
