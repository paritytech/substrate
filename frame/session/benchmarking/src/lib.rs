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

//! Benchmarks for the Session Pallet.
// This is separated into its own crate due to cyclic dependency issues.

#![cfg_attr(not(feature = "std"), no_std)]

mod mock;

use sp_std::prelude::*;
use sp_std::vec;

use frame_system::RawOrigin;
use frame_benchmarking::benchmarks;

use pallet_session::*;
use pallet_session::Module as Session;

use pallet_staking::{
	MAX_NOMINATIONS,
	benchmarking::create_validator_with_nominators,
};

pub struct Module<T: Trait>(pallet_session::Module<T>);

pub trait Trait: pallet_session::Trait + pallet_staking::Trait {}

benchmarks! {
	_ {	}

	set_keys {
		let n in 1 .. MAX_NOMINATIONS as u32;
		let v_stash = create_validator_with_nominators::<T>(n, MAX_NOMINATIONS as u32)?;
		let v_controller = pallet_staking::Module::<T>::bonded(&v_stash).ok_or("not stash")?;
		let keys = T::Keys::default();
		let proof: Vec<u8> = vec![0,1,2,3];
	}: _(RawOrigin::Signed(v_controller), keys, proof)

	purge_keys {
		let n in 1 .. MAX_NOMINATIONS as u32;
		let v_stash = create_validator_with_nominators::<T>(n, MAX_NOMINATIONS as u32)?;
		let v_controller = pallet_staking::Module::<T>::bonded(&v_stash).ok_or("not stash")?;
		let keys = T::Keys::default();
		let proof: Vec<u8> = vec![0,1,2,3];
		Session::<T>::set_keys(RawOrigin::Signed(v_controller.clone()).into(), keys, proof)?;
	}: _(RawOrigin::Signed(v_controller))
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::mock::{new_test_ext, Test};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_set_keys::<Test>());
			assert_ok!(test_benchmark_purge_keys::<Test>());
		});
	}
}
