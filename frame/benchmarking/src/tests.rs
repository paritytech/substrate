// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Tests for the module.

#![cfg(test)]

use super::*;
use frame_support::parameter_types;
use sp_runtime::{
	testing::{Header, H256},
	traits::{BlakeTwo256, IdentityLookup},
	BuildStorage,
};
use sp_std::prelude::*;

mod pallet_test {
	use frame_support::pallet_prelude::Get;

	frame_support::decl_storage! {
		trait Store for Module<T: Config> as Test where
			<T as OtherConfig>::OtherEvent: Into<<T as Config>::Event>
		{
			pub Value get(fn value): Option<u32>;
		}
	}

	frame_support::decl_module! {
		pub struct Module<T: Config> for enum Call where
			origin: T::Origin, <T as OtherConfig>::OtherEvent: Into<<T as Config>::Event>
		{
			#[weight = 0]
			fn set_value(origin, n: u32) -> frame_support::dispatch::DispatchResult {
				let _sender = frame_system::ensure_signed(origin)?;
				Value::put(n);
				Ok(())
			}

			#[weight = 0]
			fn dummy(origin, _n: u32) -> frame_support::dispatch::DispatchResult {
				let _sender = frame_system::ensure_none(origin)?;
				Ok(())
			}
		}
	}

	pub trait OtherConfig {
		type OtherEvent;
	}

	pub trait Config: frame_system::Config + OtherConfig
	where
		Self::OtherEvent: Into<<Self as Config>::Event>,
	{
		type Event;
		type LowerBound: Get<u32>;
		type UpperBound: Get<u32>;
	}
}

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		TestPallet: pallet_test::{Pallet, Call, Storage},
	}
);

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::AllowAll;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Call = Call;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
}

parameter_types! {
	pub const LowerBound: u32 = 1;
	pub const UpperBound: u32 = 100;
}

impl pallet_test::Config for Test {
	type Event = Event;
	type LowerBound = LowerBound;
	type UpperBound = UpperBound;
}

impl pallet_test::OtherConfig for Test {
	type OtherEvent = Event;
}

fn new_test_ext() -> sp_io::TestExternalities {
	GenesisConfig::default().build_storage().unwrap().into()
}

mod benchmarks {
	use super::{
		new_test_ext,
		pallet_test::{self, Value},
		Test,
	};
	use crate::{account, BenchmarkParameter, BenchmarkingSetup};
	use frame_support::{assert_err, assert_ok, ensure, traits::Get, StorageValue};
	use frame_system::RawOrigin;
	use sp_std::prelude::*;

	// Additional used internally by the benchmark macro.
	use super::pallet_test::{Call, Config, Pallet};

	crate::benchmarks! {
		where_clause {
			where
				<T as pallet_test::OtherConfig>::OtherEvent: Into<<T as pallet_test::Config>::Event> + Clone,
				<T as pallet_test::Config>::Event: Clone,
		}

		set_value {
			let b in 1 .. 1000;
			let caller = account::<T::AccountId>("caller", 0, 0);
		}: _ (RawOrigin::Signed(caller), b.into())
		verify {
			assert_eq!(Value::get(), Some(b));
		}

		other_name {
			let b in 1 .. 1000;
		}: dummy (RawOrigin::None, b.into())

		sort_vector {
			let x in 1 .. 10000;
			let mut m = Vec::<u32>::new();
			for i in (0..x).rev() {
				m.push(i);
			}
		}: {
			m.sort();
		} verify {
			ensure!(m[0] == 0, "You forgot to sort!")
		}

		bad_origin {
			let b in 1 .. 1000;
			let caller = account::<T::AccountId>("caller", 0, 0);
		}: dummy (RawOrigin::Signed(caller), b.into())

		bad_verify {
			let x in 1 .. 10000;
			let mut m = Vec::<u32>::new();
			for i in (0..x).rev() {
				m.push(i);
			}
		}: { }
		verify {
			ensure!(m[0] == 0, "You forgot to sort!")
		}

		no_components {
			let caller = account::<T::AccountId>("caller", 0, 0);
		}: set_value(RawOrigin::Signed(caller), 0)

		variable_components {
			let b in ( T::LowerBound::get() ) .. T::UpperBound::get();
		}: dummy (RawOrigin::None, b.into())

		#[extra]
		extra_benchmark {
			let b in 1 .. 1000;
			let caller = account::<T::AccountId>("caller", 0, 0);
		}: set_value(RawOrigin::Signed(caller), b.into())
		verify {
			assert_eq!(Value::get(), Some(b));
		}

		#[skip_meta]
		skip_meta_benchmark {
			let b in 1 .. 1000;
			let caller = account::<T::AccountId>("caller", 0, 0);
		}: set_value(RawOrigin::Signed(caller), b.into())
		verify {
			assert_eq!(Value::get(), Some(b));
		}
	}

	#[test]
	fn benchmarks_macro_works() {
		// Check benchmark creation for `set_value`.
		let selected = SelectedBenchmark::set_value;

		let components = <SelectedBenchmark as BenchmarkingSetup<Test>>::components(&selected);
		assert_eq!(components, vec![(BenchmarkParameter::b, 1, 1000)]);

		let closure = <SelectedBenchmark as BenchmarkingSetup<Test>>::instance(
			&selected,
			&[(BenchmarkParameter::b, 1)],
			true,
		)
		.expect("failed to create closure");

		new_test_ext().execute_with(|| {
			assert_ok!(closure());
		});
	}

	#[test]
	fn benchmarks_macro_rename_works() {
		// Check benchmark creation for `other_dummy`.
		let selected = SelectedBenchmark::other_name;
		let components = <SelectedBenchmark as BenchmarkingSetup<Test>>::components(&selected);
		assert_eq!(components, vec![(BenchmarkParameter::b, 1, 1000)]);

		let closure = <SelectedBenchmark as BenchmarkingSetup<Test>>::instance(
			&selected,
			&[(BenchmarkParameter::b, 1)],
			true,
		)
		.expect("failed to create closure");

		new_test_ext().execute_with(|| {
			assert_ok!(closure());
		});
	}

	#[test]
	fn benchmarks_macro_works_for_non_dispatchable() {
		let selected = SelectedBenchmark::sort_vector;

		let components = <SelectedBenchmark as BenchmarkingSetup<Test>>::components(&selected);
		assert_eq!(components, vec![(BenchmarkParameter::x, 1, 10000)]);

		let closure = <SelectedBenchmark as BenchmarkingSetup<Test>>::instance(
			&selected,
			&[(BenchmarkParameter::x, 1)],
			true,
		)
		.expect("failed to create closure");

		assert_ok!(closure());
	}

	#[test]
	fn benchmarks_macro_verify_works() {
		// Check postcondition for benchmark `set_value` is valid.
		let selected = SelectedBenchmark::set_value;

		let closure = <SelectedBenchmark as BenchmarkingSetup<Test>>::instance(
			&selected,
			&[(BenchmarkParameter::b, 1)],
			true,
		)
		.expect("failed to create closure");

		new_test_ext().execute_with(|| {
			assert_ok!(closure());
		});

		// Check postcondition for benchmark `bad_verify` is invalid.
		let selected = SelectedBenchmark::bad_verify;

		let closure = <SelectedBenchmark as BenchmarkingSetup<Test>>::instance(
			&selected,
			&[(BenchmarkParameter::x, 10000)],
			true,
		)
		.expect("failed to create closure");

		new_test_ext().execute_with(|| {
			assert_err!(closure(), "You forgot to sort!");
		});
	}

	#[test]
	fn benchmarks_generate_unit_tests() {
		new_test_ext().execute_with(|| {
			assert_ok!(Pallet::<Test>::test_benchmark_set_value());
			assert_ok!(Pallet::<Test>::test_benchmark_other_name());
			assert_ok!(Pallet::<Test>::test_benchmark_sort_vector());
			assert_err!(Pallet::<Test>::test_benchmark_bad_origin(), "Bad origin");
			assert_err!(Pallet::<Test>::test_benchmark_bad_verify(), "You forgot to sort!");
			assert_ok!(Pallet::<Test>::test_benchmark_no_components());
			assert_ok!(Pallet::<Test>::test_benchmark_variable_components());
		});
	}
}
