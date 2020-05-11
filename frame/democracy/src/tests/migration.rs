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

//! The tests for migration.

use super::*;
use frame_support::{storage::migration, Hashable, traits::OnRuntimeUpgrade};
use substrate_test_utils::assert_eq_uvec;

#[test]
fn migration() {
	new_test_ext().execute_with(|| {
		for i in 0..3 {
			let k = i.twox_64_concat();
			let v: (BalanceOf<Test>, Vec<u64>) = (i * 1000, vec![i]);
			migration::put_storage_value(b"Democracy", b"DepositOf", &k, v);
		}
		StorageVersion::kill();

		Democracy::on_runtime_upgrade();

		assert_eq!(StorageVersion::get(), Some(Releases::V1));
		assert_eq_uvec!(
			DepositOf::<Test>::iter().collect::<Vec<_>>(),
			vec![
				(0, (vec![0u64], <BalanceOf<Test>>::from(0u32))),
				(1, (vec![1u64], <BalanceOf<Test>>::from(1000u32))),
				(2, (vec![2u64], <BalanceOf<Test>>::from(2000u32))),
			]
		);
	})
}
