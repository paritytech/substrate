// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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
