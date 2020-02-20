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

use frame_system::RawOrigin;
use frame_benchmarking::{
	BenchmarkResults, BenchmarkParameter, benchmarking, Benchmarking,
    BenchmarkingSetup,
};

use sp_runtime::traits::{Dispatchable, Header};




const MAX_UNCLES : u32 = 10;

// Support Functions
fn spawn_header<T: Trait>(_name: &'static str, index: u32) -> T::Header {
	<T::Header as Header>::new(index.into(), Default::default(), Default::default(), Default::default(), Default::default())
}


// Benchmark `add_registrar` extrinsic.
struct SetUncles;
impl<T: Trait> BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>> for SetUncles {
	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
		vec![
			// uncles
			(BenchmarkParameter::U, 1, MAX_UNCLES),
		]
	}

	fn instance(&self, _components: &[(BenchmarkParameter, u32)])
		-> Result<(crate::Call<T>, RawOrigin<T::AccountId>), &'static str>
	{
        let headers = (0..10).into_iter().map(|idx| {
            spawn_header::<T>("TODO no idea about this", idx as u32)
        }).collect::<Vec<T::Header>>();

		Ok(
            (crate::Call::<T>::set_uncles(headers), RawOrigin::None)
        )
	}
}

// The list of available benchmarks for this pallet.
// At the moment it's just one.
enum SelectedBenchmark {
	SetUncles,
}

// Allow us to select a benchmark from the list of available benchmarks.

impl<T: Trait> BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>> for SelectedBenchmark {
	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
		match self {
			Self::SetUncles => <SetUncles as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::components(&SetUncles),
		}
	}

	fn instance(&self, components: &[(BenchmarkParameter, u32)])
		-> Result<(crate::Call<T>, RawOrigin<T::AccountId>), &'static str>
	{
		match self {
			Self::SetUncles => <SetUncles as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::instance(&SetUncles, components),
		}
	}
}

impl<T: Trait> Benchmarking<BenchmarkResults> for Module<T> {
	fn run_benchmark(extrinsic: Vec<u8>, steps: u32, repeat: u32) -> Result<Vec<BenchmarkResults>, &'static str> {
		// Map the input to the selected benchmark.
		let selected_benchmark = match extrinsic.as_slice() {
			b"set_uncles" => SelectedBenchmark::SetUncles,
			_ => return Err("Could not find extrinsic."),
		};

		// Warm up the DB
		benchmarking::commit_db();
		benchmarking::wipe_db();

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

				// Run the benchmark `repeat` times.
				for _ in 0..repeat {
					// Set up the externalities environment for the setup we want to benchmark.
					let (call, caller) = <SelectedBenchmark as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::instance(&selected_benchmark, &c)?;
					// Commit the externalities to the database, flushing the DB cache.
					// This will enable worst case scenario for reading from the database.
					benchmarking::commit_db();
					// Run the benchmark.
					let start = benchmarking::current_time();
					call.dispatch(caller.into())?;
					let finish = benchmarking::current_time();
					let elapsed = finish - start;
					results.push((c.clone(), elapsed));
					// Wipe the DB back to the genesis state.
					benchmarking::wipe_db();
				}
			}
		}
		return Ok(results);
	}
}
