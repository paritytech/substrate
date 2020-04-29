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

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use sp_std::prelude::*;
use frame_system::RawOrigin;
use frame_support::{ensure, traits::OnFinalize};
use frame_benchmarking::benchmarks;

use crate::Module as Timestamp;

const MAX_TIME: u32 = 100;

benchmarks! {
	_ { }

	set {
		let t in 1 .. MAX_TIME;
	}: _(RawOrigin::None, t.into())
	verify {
		ensure!(Timestamp::<T>::now() == t.into(), "Time was not set.");
	}

	on_finalize {
		let t in 1 .. MAX_TIME;
		Timestamp::<T>::set(RawOrigin::None.into(), t.into())?;
		ensure!(DidUpdate::exists(), "Time was not set.");
	}: { Timestamp::<T>::on_finalize(t.into()); }
	verify {
		ensure!(!DidUpdate::exists(), "Time was not removed.");
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::{new_test_ext, Test};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_set::<Test>());
			assert_ok!(test_benchmark_on_finalize::<Test>());
		});
	}
}
