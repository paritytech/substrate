// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

// Benchmarks for Utility Pallet

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use sp_std::prelude::*;
use frame_system::RawOrigin;
use frame_benchmarking::{benchmarks, account};

const SEED: u32 = 0;

benchmarks! {
	_ { }

	batch {
		let c in 0 .. 1000;
		let mut calls: Vec<<T as Trait>::Call> = Vec::new();
		for i in 0 .. c {
			let call = frame_system::Call::remark(vec![]).into();
			calls.push(call);
		}

		let caller = account("caller", 0, SEED);

	}: _(RawOrigin::Signed(caller), calls)

	as_sub {
		let u in 0 .. 1000;
		let caller = account("caller", u, SEED);
		let call = Box::new(frame_system::Call::remark(vec![]).into());
	}: _(RawOrigin::Signed(caller), u as u16, call)
}
