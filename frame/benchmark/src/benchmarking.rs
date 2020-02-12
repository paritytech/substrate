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

//! Identity pallet benchmarking.

use super::*;

use codec::{Encode, Decode};
use frame_system::RawOrigin;
use sp_io::hashing::blake2_256;
use sp_runtime::{BenchmarkResults, BenchmarkParameter};
use sp_runtime::traits::{Benchmarking, BenchmarkingSetup, Dispatchable};
use sp_std::prelude::*;

use crate::Module as Benchmark;

fn account<T: Trait>(index: u32) -> T::AccountId {
	let entropy = (b"benchmark", index).using_encoded(blake2_256);
	T::AccountId::decode(&mut &entropy[..]).unwrap_or_default()
}

// Custom implementation to handle benchmarking of calling a host function.
fn time_host(steps: u32, repeat: u32) -> Result<Vec<BenchmarkResults>, &'static str> {
	let mut results: Vec<BenchmarkResults> = Vec::new();

	for _ in 0..steps {
		let start = sp_io::benchmarking::current_time();
		for _ in 0..repeat {
			let _ = sp_io::benchmarking::current_time();
		}
		let finish = sp_io::benchmarking::current_time();
		let elapsed = finish - start;

		results.push((vec![(BenchmarkParameter::L, repeat)], elapsed));
	}

	return Ok(results);
}

struct AddMemberList;
impl<T: Trait> BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>> for AddMemberList {

	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
		vec![
			// Member Count
			(BenchmarkParameter::M, 1, 1000),
		]
	}

	fn instance(&self, components: &[(BenchmarkParameter, u32)]) -> Result<(crate::Call<T>, RawOrigin<T::AccountId>), &'static str>
	{
		// Add m `members`
		let m = components.iter().find(|&c| c.0 == BenchmarkParameter::M).unwrap().1;
		for i in 0..m {
			let _ = Benchmark::<T>::add_member_list(RawOrigin::Signed(account::<T>(i)).into());
		}

		sp_std::if_std!{
			println!("# Users {:?}", MyMemberList::<T>::get().len());
		}

		// Return the `add_member_list` m + 1 call
		Ok((crate::Call::<T>::add_member_list(), RawOrigin::Signed(account::<T>(m + 1))))
	}
}

struct AppendMemberList;
impl<T: Trait> BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>> for AppendMemberList {

	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
		vec![
			// Member Count
			(BenchmarkParameter::M, 1, 1000),
		]
	}

	fn instance(&self, components: &[(BenchmarkParameter, u32)]) -> Result<(crate::Call<T>, RawOrigin<T::AccountId>), &'static str>
	{
		// Add m members
		let m = components.iter().find(|&c| c.0 == BenchmarkParameter::M).unwrap().1;
		for i in 0..m {
			let _ = Benchmark::<T>::append_member_list(RawOrigin::Signed(account::<T>(i)).into());
		}

		sp_std::if_std!{
			println!("# Users {:?}", MyMemberList::<T>::get().len());
		}

		// Return the `append_member_list` m + 1 call
		Ok((crate::Call::<T>::append_member_list(), RawOrigin::Signed(account::<T>(m + 1))))
	}
}

struct ReadValue;
impl<T: Trait> BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>> for ReadValue {

	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
		vec![
			// Number of reads
			(BenchmarkParameter::N, 1, 1000),
		]
	}

	fn instance(&self, components: &[(BenchmarkParameter, u32)]) -> Result<(crate::Call<T>, RawOrigin<T::AccountId>), &'static str>
	{
		// Get N
		let n = components.iter().find(|&c| c.0 == BenchmarkParameter::N).unwrap().1;

		// Add a value to storage
		MyValue::put(n);

		// Return the `read_value` n times call
		Ok((crate::Call::<T>::read_value(n), RawOrigin::Signed(account::<T>(n))))
	}
}

struct PutValue;
impl<T: Trait> BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>> for PutValue {

	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
		vec![
			// Number of reads
			(BenchmarkParameter::N, 1, 1000),
		]
	}

	fn instance(&self, components: &[(BenchmarkParameter, u32)]) -> Result<(crate::Call<T>, RawOrigin<T::AccountId>), &'static str>
	{
		// Get N
		let n = components.iter().find(|&c| c.0 == BenchmarkParameter::N).unwrap().1;

		// Return the `put_value` n times call
		Ok((crate::Call::<T>::put_value(n), RawOrigin::Signed(account::<T>(n))))
	}
}

struct InsertMap;
impl<T: Trait> BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>> for InsertMap {

	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
		vec![
			// Number of reads
			(BenchmarkParameter::N, 1, 1000),
		]
	}

	fn instance(&self, components: &[(BenchmarkParameter, u32)]) -> Result<(crate::Call<T>, RawOrigin<T::AccountId>), &'static str>
	{
		// Get N
		let n = components.iter().find(|&c| c.0 == BenchmarkParameter::N).unwrap().1;

		// Return the `put_value` n times call
		Ok((crate::Call::<T>::insert_map(n), RawOrigin::Signed(account::<T>(n))))
	}
}

enum SelectedBenchmark {
	ReadValue,
	PutValue,
	RemoveValue,
	ExistsValue,
	ReadMap,
	InsertMap,
	ExistsMap,
	RemovePrefix,
	AddMemberList,
	AppendMemberList,
}

impl<T: Trait> BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>> for SelectedBenchmark {
	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)>
	{
		match self {
			Self::AddMemberList => <AddMemberList as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::components(&AddMemberList),
			Self::AppendMemberList => <AppendMemberList as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::components(&AppendMemberList),
			Self::ReadValue => <ReadValue as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::components(&ReadValue),
			Self::PutValue => <PutValue as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::components(&PutValue),
			Self::InsertMap => <InsertMap as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::components(&InsertMap),

		}
	}

	fn instance(&self, components: &[(BenchmarkParameter, u32)]) -> Result<(crate::Call<T>, RawOrigin<T::AccountId>), &'static str>
	{
		match self {
			Self::AddMemberList => <AddMemberList as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::instance(&AddMemberList, components),
			Self::AppendMemberList => <AppendMemberList as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::instance(&AppendMemberList, components),
			Self::ReadValue => <ReadValue as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::instance(&ReadValue, components),
			Self::PutValue => <PutValue as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::instance(&PutValue, components),
			Self::InsertMap => <InsertMap as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::instance(&InsertMap, components),

		}
	}
}

impl<T: Trait> Benchmarking<BenchmarkResults> for Module<T> {
	fn run_benchmark(extrinsic: Vec<u8>, steps: u32, repeat: u32) -> Result<Vec<BenchmarkResults>, &'static str> {

		let selected_benchmark = match extrinsic.as_slice() {
			b"time_host" => return benchmarking::time_host(steps, repeat),
			b"add_member_list" => SelectedBenchmark::AddMemberList,
			b"append_member_list" => SelectedBenchmark::AppendMemberList,
			b"read_value" => SelectedBenchmark::ReadValue,
			_ => return Err("Extrinsic not found."),
		};

		// Warm up the DB?
		sp_io::benchmarking::commit_db();
		sp_io::benchmarking::wipe_db();

		// first one is set_identity.		
		let components = <SelectedBenchmark as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::components(&selected_benchmark);		
		// results go here
		let mut results: Vec<BenchmarkResults> = Vec::new();
		// Select the component we will be benchmarking. Each component will be benchmarked.
		for (name, low, high) in components.iter() {
			// Create up to `STEPS` steps for that component between high and low.
			let step_size = ((high - low) / steps).max(1);
			let num_of_steps = (high - low) / step_size;
			for s in 0..num_of_steps {
				// This is the value we will be testing for component `name`
				let component_value = low + step_size * s;

				// Select the mid value for all the other components.
				let c: Vec<(BenchmarkParameter, u32)> = components.iter()
					.map(|(n, l, h)|
						(*n, if n == name { component_value } else { (h - l) / 2 + l })
					).collect();

				for r in 0..repeat {
					sp_std::if_std!{
						println!("STEP {:?} REPEAT {:?}", s, r);
					}
					let (call, caller) = <SelectedBenchmark as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::instance(&selected_benchmark, &c)?;
					sp_io::benchmarking::commit_db();
					let start = sp_io::benchmarking::current_time();
					assert_eq!(call.dispatch(caller.into()), Ok(()));
					let finish = sp_io::benchmarking::current_time();
					let elapsed = finish - start;
					sp_io::benchmarking::wipe_db();
					results.push((c.clone(), elapsed));
				}
			}
		}
		return Ok(results);
	}
}
