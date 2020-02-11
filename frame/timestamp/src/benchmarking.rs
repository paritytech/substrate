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

//! Timestamp pallet benchmarking.

use super::*;

use sp_std::prelude::*;

use frame_system::RawOrigin;
use sp_runtime::{BenchmarkResults, BenchmarkParameter, selected_benchmark};
use sp_runtime::traits::{Benchmarking, BenchmarkingSetup, Dispatchable};

// Benchmark `set` extrinsic.
struct Set;
impl<T: Trait> BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>> for Set {
	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
		vec![]
	}

	fn instance(&self, _components: &[(BenchmarkParameter, u32)])
		-> Result<(crate::Call<T>, RawOrigin<T::AccountId>), &'static str>
	{
		let user_origin = RawOrigin::None;
		let now = 1.into();

		// Return the `set` call
		Ok((crate::Call::<T>::set(now), user_origin))
	}
}

selected_benchmark!(Set);

impl<T: Trait> Benchmarking<BenchmarkResults> for Module<T> {
	fn run_benchmark(extrinsic: Vec<u8>, _steps: u32, repeat: u32) -> Result<Vec<BenchmarkResults>, &'static str> {
		// Map the input to the selected benchmark.
		let selected_benchmark = match extrinsic.as_slice() {
			b"set" => SelectedBenchmark::Set,
			_ => return Err("Could not find extrinsic."),
		};
		
		// Warm up the DB
		sp_io::benchmarking::commit_db();
		sp_io::benchmarking::wipe_db();

		// results go here
		let mut results: Vec<BenchmarkResults> = Vec::new();
		// Run the benchmark `repeat` times.
		for _r in 0..repeat {
			// Set up the externalities environment for the setup we want to benchmark.
			let (call, caller) = <SelectedBenchmark as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::instance(&selected_benchmark, &[])?;
			// Commit the externalities to the database, flushing the DB cache.
			// This will enable worst case scenario for reading from the database.
			sp_io::benchmarking::commit_db();
			// Run the benchmark.
			let start = sp_io::benchmarking::current_time();
			call.dispatch(caller.clone().into())?;
			let finish = sp_io::benchmarking::current_time();
			let elapsed = finish - start;
			results.push((vec![], elapsed));
			// Wipe the DB back to the genesis state.
			sp_io::benchmarking::wipe_db();
		}

		return Ok(results);
	}
}
