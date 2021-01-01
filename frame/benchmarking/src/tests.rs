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

//! Tests for the module.

#![cfg(test)]

use super::*;
use sp_std::prelude::*;
use sp_runtime::{traits::{BlakeTwo256, IdentityLookup}, testing::{H256, Header}};
use frame_support::{
	dispatch::DispatchResult,
	decl_module, decl_storage, impl_outer_origin, assert_ok, assert_err, ensure
};
use frame_system::{RawOrigin, ensure_signed, ensure_none};

decl_storage! {
	trait Store for Module<T: Config> as Test where
		<T as OtherConfig>::OtherEvent: Into<<T as Config>::Event>
	{
		Value get(fn value): Option<u32>;
	}
}

decl_module! {
	pub struct Module<T: Config> for enum Call where
		origin: T::Origin, <T as OtherConfig>::OtherEvent: Into<<T as Config>::Event>
	{
		#[weight = 0]
		fn set_value(origin, n: u32) -> DispatchResult {
			let _sender = ensure_signed(origin)?;
			Value::put(n);
			Ok(())
		}

		#[weight = 0]
		fn dummy(origin, _n: u32) -> DispatchResult {
			let _sender = ensure_none(origin)?;
			Ok(())
		}
	}
}

impl_outer_origin! {
	pub enum Origin for Test where system = frame_system {}
}

pub trait OtherConfig {
	type OtherEvent;
}

pub trait Config: frame_system::Config + OtherConfig
	where Self::OtherEvent: Into<<Self as Config>::Event>
{
	type Event;
}

#[derive(Clone, Eq, PartialEq)]
pub struct Test;

impl frame_system::Config for Test {
	type BaseCallFilter = ();
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Call = ();
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = ();
	type BlockHashCount = ();
	type Version = ();
	type PalletInfo = ();
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
}

impl Config for Test {
	type Event = ();
}

impl OtherConfig for Test {
	type OtherEvent = ();
}

fn new_test_ext() -> sp_io::TestExternalities {
	frame_system::GenesisConfig::default().build_storage::<Test>().unwrap().into()
}

benchmarks!{
	where_clause { where <T as OtherConfig>::OtherEvent: Into<<T as Config>::Event> }
	,
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
	).expect("failed to create closure");

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
	).expect("failed to create closure");

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
	).expect("failed to create closure");

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
	).expect("failed to create closure");

	new_test_ext().execute_with(|| {
		assert_ok!(closure());
	});

	// Check postcondition for benchmark `bad_verify` is invalid.
	let selected = SelectedBenchmark::bad_verify;

	let closure = <SelectedBenchmark as BenchmarkingSetup<Test>>::instance(
		&selected,
		&[(BenchmarkParameter::x, 10000)],
		true,
	).expect("failed to create closure");

	new_test_ext().execute_with(|| {
		assert_err!(closure(), "You forgot to sort!");
	});
}

#[test]
fn benchmarks_generate_unit_tests() {
	new_test_ext().execute_with(|| {
		assert_ok!(test_benchmark_set_value::<Test>());
		assert_ok!(test_benchmark_other_name::<Test>());
		assert_ok!(test_benchmark_sort_vector::<Test>());
		assert_err!(test_benchmark_bad_origin::<Test>(), "Bad origin");
		assert_err!(test_benchmark_bad_verify::<Test>(), "You forgot to sort!");
		assert_ok!(test_benchmark_no_components::<Test>());
	});
}
