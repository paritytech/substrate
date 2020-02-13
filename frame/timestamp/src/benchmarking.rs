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
use sp_runtime::{BenchmarkResults, BenchmarkParameter, selected_benchmarks};
use sp_runtime::traits::{BenchmarkingSetup, Dispatchable};

/// Benchmark `set` extrinsic.
struct Set;
impl<T: Trait> BenchmarkingSetup<T, Call<T>, RawOrigin<T::AccountId>> for Set {
	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
		vec![
			// Current time ("Now")
			(BenchmarkParameter::N, 1, 100),
		]
	}

	fn instance(&self, components: &[(BenchmarkParameter, u32)])
		-> Result<(Call<T>, RawOrigin<T::AccountId>), &'static str>
	{
		let user_origin = RawOrigin::None;
		let now = components.iter().find(|&c| c.0 == BenchmarkParameter::N).unwrap().1;

		// Return the `set` call
		Ok((Call::<T>::set(now.into()), user_origin))
	}
}

selected_benchmarks!([Set]);
