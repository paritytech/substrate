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
use frame_benchmarking::benchmarks;
use sp_runtime::traits::Dispatchable;

const MAX_TIME: u32 = 100;

benchmarks! {
	_ {
		let n in 1 .. MAX_TIME => ();
	}

	set {
		let n in ...;
	}: _(RawOrigin::None, n.into())
}
