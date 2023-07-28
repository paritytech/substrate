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

//! Salary pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use crate::Pallet as CoreFellowship;

use frame_benchmarking::v2::*;
use frame_system::{pallet_prelude::BlockNumberFor, RawOrigin};
use sp_arithmetic::traits::Bounded;

const SEED: u32 = 0;

type BenchResult = Result<(), BenchmarkError>;

#[instance_benchmarks]
mod benchmarks {
	use super::*;

	fn ensure_evidence<T: Config<I>, I: 'static>(who: &T::AccountId) -> BenchResult {
		let evidence = BoundedVec::try_from(vec![0; Evidence::<T, I>::bound()]).unwrap();
		let wish = Wish::Retention;
		let origin = RawOrigin::Signed(who.clone()).into();
		CoreFellowship::<T, I>::submit_evidence(origin, wish, evidence)?;
		assert!(MemberEvidence::<T, I>::contains_key(who));
		Ok(())
	}

	fn make_member<T: Config<I>, I: 'static>(rank: u16) -> Result<T::AccountId, BenchmarkError> {
		let member = account("member", 0, SEED);
		T::Members::induct(&member)?;
		for _ in 0..rank {
			T::Members::promote(&member)?;
		}
		CoreFellowship::<T, I>::import(RawOrigin::Signed(member.clone()).into())?;
		Ok(member)
	}

	#[benchmark]
	fn set_params() -> Result<(), BenchmarkError> {
		let params = ParamsType {
			active_salary: [100u32.into(); 9],
			passive_salary: [10u32.into(); 9],
			demotion_period: [100u32.into(); 9],
			min_promotion_period: [100u32.into(); 9],
			offboard_timeout: 1u32.into(),
		};

		#[extrinsic_call]
		_(RawOrigin::Root, Box::new(params.clone()));

		assert_eq!(Params::<T, I>::get(), params);
		Ok(())
	}

	#[benchmark]
	fn bump_offboard() -> Result<(), BenchmarkError> {
		let member = make_member::<T, I>(0)?;

		// Set it to the max value to ensure that any possible auto-demotion period has passed.
		frame_system::Pallet::<T>::set_block_number(BlockNumberFor::<T>::max_value());
		ensure_evidence::<T, I>(&member)?;
		assert!(Member::<T, I>::contains_key(&member));

		#[extrinsic_call]
		CoreFellowship::<T, I>::bump(RawOrigin::Signed(member.clone()), member.clone());

		assert!(!Member::<T, I>::contains_key(&member));
		assert!(!MemberEvidence::<T, I>::contains_key(&member));
		Ok(())
	}

	#[benchmark]
	fn bump_demote() -> Result<(), BenchmarkError> {
		let member = make_member::<T, I>(2)?;

		// Set it to the max value to ensure that any possible auto-demotion period has passed.
		frame_system::Pallet::<T>::set_block_number(BlockNumberFor::<T>::max_value());
		ensure_evidence::<T, I>(&member)?;
		assert!(Member::<T, I>::contains_key(&member));
		assert_eq!(T::Members::rank_of(&member), Some(2));

		#[extrinsic_call]
		CoreFellowship::<T, I>::bump(RawOrigin::Signed(member.clone()), member.clone());

		assert!(Member::<T, I>::contains_key(&member));
		assert_eq!(T::Members::rank_of(&member), Some(1));
		assert!(!MemberEvidence::<T, I>::contains_key(&member));
		Ok(())
	}

	#[benchmark]
	fn set_active() -> Result<(), BenchmarkError> {
		let member = make_member::<T, I>(1)?;
		assert!(Member::<T, I>::get(&member).unwrap().is_active);

		#[extrinsic_call]
		_(RawOrigin::Signed(member.clone()), false);

		assert!(!Member::<T, I>::get(&member).unwrap().is_active);
		Ok(())
	}

	#[benchmark]
	fn induct() -> Result<(), BenchmarkError> {
		let candidate: T::AccountId = account("candidate", 0, SEED);

		#[extrinsic_call]
		_(RawOrigin::Root, candidate.clone());

		assert_eq!(T::Members::rank_of(&candidate), Some(0));
		assert!(Member::<T, I>::contains_key(&candidate));
		Ok(())
	}

	#[benchmark]
	fn promote() -> Result<(), BenchmarkError> {
		let member = make_member::<T, I>(1)?;
		ensure_evidence::<T, I>(&member)?;

		#[extrinsic_call]
		_(RawOrigin::Root, member.clone(), 2u8.into());

		assert_eq!(T::Members::rank_of(&member), Some(2));
		assert!(!MemberEvidence::<T, I>::contains_key(&member));
		Ok(())
	}

	#[benchmark]
	fn offboard() -> Result<(), BenchmarkError> {
		let member = make_member::<T, I>(0)?;
		T::Members::demote(&member)?;
		ensure_evidence::<T, I>(&member)?;

		assert!(T::Members::rank_of(&member).is_none());
		assert!(Member::<T, I>::contains_key(&member));
		assert!(MemberEvidence::<T, I>::contains_key(&member));

		#[extrinsic_call]
		_(RawOrigin::Signed(member.clone()), member.clone());

		assert!(!Member::<T, I>::contains_key(&member));
		assert!(!MemberEvidence::<T, I>::contains_key(&member));
		Ok(())
	}

	#[benchmark]
	fn import() -> Result<(), BenchmarkError> {
		let member = account("member", 0, SEED);
		T::Members::induct(&member)?;
		T::Members::promote(&member)?;

		assert!(!Member::<T, I>::contains_key(&member));

		#[extrinsic_call]
		_(RawOrigin::Signed(member.clone()));

		assert!(Member::<T, I>::contains_key(&member));
		Ok(())
	}

	#[benchmark]
	fn approve() -> Result<(), BenchmarkError> {
		let member = make_member::<T, I>(1)?;
		let then = frame_system::Pallet::<T>::block_number();
		let now = then.saturating_plus_one();
		frame_system::Pallet::<T>::set_block_number(now);
		ensure_evidence::<T, I>(&member)?;

		assert_eq!(Member::<T, I>::get(&member).unwrap().last_proof, then);

		#[extrinsic_call]
		_(RawOrigin::Root, member.clone(), 1u8.into());

		assert_eq!(Member::<T, I>::get(&member).unwrap().last_proof, now);
		assert!(!MemberEvidence::<T, I>::contains_key(&member));
		Ok(())
	}

	#[benchmark]
	fn submit_evidence() -> Result<(), BenchmarkError> {
		let member = make_member::<T, I>(1)?;
		let evidence = vec![0; Evidence::<T, I>::bound()].try_into().unwrap();

		assert!(!MemberEvidence::<T, I>::contains_key(&member));

		#[extrinsic_call]
		_(RawOrigin::Signed(member.clone()), Wish::Retention, evidence);

		assert!(MemberEvidence::<T, I>::contains_key(&member));
		Ok(())
	}

	impl_benchmark_test_suite! {
		CoreFellowship,
		crate::tests::new_test_ext(),
		crate::tests::Test,
	}
}
