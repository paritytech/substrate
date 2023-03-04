// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

//! Salary pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use crate::Pallet as CoreFellowship;

use frame_benchmarking::v2::*;
use frame_system::RawOrigin;
use sp_arithmetic::traits::Bounded;

const SEED: u32 = 0;

#[instance_benchmarks]
mod benchmarks {
	use super::*;

	#[benchmark]
	fn set_params() {
		let params = ParamsType {
			active_salary: [100u32.into(); 9],
			passive_salary: [10u32.into(); 9],
			demotion_period: [100u32.into(); 9],
			min_promotion_period: [100u32.into(); 9],
		};

		#[extrinsic_call]
		_(RawOrigin::Root, params.clone());

		assert_eq!(Params::<T, I>::get(), params);
	}

	#[benchmark]
	fn bump_offboard() {
		let member = account("member", 0, SEED);
		T::Members::induct(&member).unwrap();
		T::Members::promote(&member).unwrap();
		CoreFellowship::<T, I>::prove(RawOrigin::Root.into(), member.clone(), 1u8.into()).unwrap();

		// Set it to the max value to ensure that any possible auto-demotion period has passed.
		frame_system::Pallet::<T>::set_block_number(T::BlockNumber::max_value());
		assert!(Member::<T, I>::contains_key(&member));

		#[extrinsic_call]
		CoreFellowship::<T, I>::bump(RawOrigin::Signed(member.clone()), member.clone());

		assert!(!Member::<T, I>::contains_key(&member));
	}

	#[benchmark]
	fn bump_demote() {
		let member = account("member", 0, SEED);
		T::Members::induct(&member).unwrap();
		T::Members::promote(&member).unwrap();
		T::Members::promote(&member).unwrap();
		CoreFellowship::<T, I>::prove(RawOrigin::Root.into(), member.clone(), 2u8.into()).unwrap();

		// Set it to the max value to ensure that any possible auto-demotion period has passed.
		frame_system::Pallet::<T>::set_block_number(T::BlockNumber::max_value());
		assert!(Member::<T, I>::contains_key(&member));
		assert_eq!(T::Members::rank_of(&member), Some(2));

		#[extrinsic_call]
		CoreFellowship::<T, I>::bump(RawOrigin::Signed(member.clone()), member.clone());

		assert!(Member::<T, I>::contains_key(&member));
		assert_eq!(T::Members::rank_of(&member), Some(1));
	}

	#[benchmark]
	fn set_active() {
		let member = account("member", 0, SEED);
		T::Members::induct(&member).unwrap();
		T::Members::promote(&member).unwrap();
		CoreFellowship::<T, I>::prove(RawOrigin::Root.into(), member.clone(), 1u8.into()).unwrap();
		assert!(Member::<T, I>::get(&member).unwrap().is_active);

		#[extrinsic_call]
		_(RawOrigin::Signed(member.clone()), false);

		assert!(!Member::<T, I>::get(&member).unwrap().is_active);
	}

	#[benchmark]
	fn induct() {
		let candidate = account("candidate", 0, SEED);
		T::Members::induct(&candidate).unwrap();
		assert_eq!(T::Members::rank_of(&candidate), Some(0));

		#[extrinsic_call]
		_(RawOrigin::Root, candidate.clone());

		assert_eq!(T::Members::rank_of(&candidate), Some(1));
	}

	#[benchmark]
	fn promote() {
		let member = account("member", 0, SEED);
		T::Members::induct(&member).unwrap();
		T::Members::promote(&member).unwrap();
		CoreFellowship::<T, I>::prove(RawOrigin::Root.into(), member.clone(), 1u8.into()).unwrap();
		assert_eq!(T::Members::rank_of(&member), Some(1));

		#[extrinsic_call]
		_(RawOrigin::Root, member.clone(), 2u8.into());

		assert_eq!(T::Members::rank_of(&member), Some(2));
	}

	#[benchmark]
	fn offboard() {
		let member = account("member", 0, SEED);
		T::Members::induct(&member).unwrap();
		T::Members::promote(&member).unwrap();
		CoreFellowship::<T, I>::prove(RawOrigin::Root.into(), member.clone(), 1u8.into()).unwrap();
		T::Members::demote(&member).unwrap();

		assert_eq!(T::Members::rank_of(&member), Some(0));
		assert!(Member::<T, I>::contains_key(&member));

		#[extrinsic_call]
		_(RawOrigin::Signed(member.clone()), member.clone());

		assert!(!Member::<T, I>::contains_key(&member));
	}

	#[benchmark]
	fn prove_new() {
		let member = account("member", 0, SEED);
		T::Members::induct(&member).unwrap();
		T::Members::promote(&member).unwrap();
		assert!(!Member::<T, I>::contains_key(&member));

		#[extrinsic_call]
		CoreFellowship::<T, I>::prove(RawOrigin::Root, member.clone(), 1u8.into());

		assert!(Member::<T, I>::contains_key(&member));
	}

	#[benchmark]
	fn prove_existing() {
		let member = account("member", 0, SEED);
		T::Members::induct(&member).unwrap();
		T::Members::promote(&member).unwrap();
		CoreFellowship::<T, I>::prove(RawOrigin::Root.into(), member.clone(), 1u8.into()).unwrap();

		let then = frame_system::Pallet::<T>::block_number();
		let now = then.saturating_plus_one();
		frame_system::Pallet::<T>::set_block_number(now);

		assert_eq!(Member::<T, I>::get(&member).unwrap().last_proof, then);

		#[extrinsic_call]
		CoreFellowship::<T, I>::prove(RawOrigin::Root, member.clone(), 1u8.into());

		assert_eq!(Member::<T, I>::get(&member).unwrap().last_proof, now);
	}

	impl_benchmark_test_suite! {
		CoreFellowship,
		crate::tests::new_test_ext(),
		crate::tests::Test,
	}
}
