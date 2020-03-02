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
use sp_std::prelude::*;
use frame_benchmarking::{benchmarks, account, BenchmarkResults, BenchmarkParameter};


use crate::Module as Benchmark;

const SEED: u32 = 0;

benchmarks! {
	_ {
		let m in 1 .. 1000 => {
			let origin = RawOrigin::Signed(account("member", m, SEED));
			Benchmark::<T>::add_member_list(origin.into())?
		};
		let i in 1 .. 1000 => {
			MyMap::insert(i, i);
		};
		let d in 1 .. 1000 => {
			for i in 0..d {
				for j in 0..100 {
					MyDoubleMap::insert(i, j, d);
				}
			}
		};
	}

	add_member_list {
		let m in ...;
	}: _(RawOrigin::Signed(account("member", m + 1, SEED)))

	append_member_list {
		let m in ...;
	}: _(RawOrigin::Signed(account("member", m + 1, SEED)))

	read_value {
		let n in 1 .. 1000;
		MyValue::put(n);
	}: _(RawOrigin::Signed(account("user", 0, SEED)), n)

	put_value {
		let n in 1 .. 1000;
	}: _(RawOrigin::Signed(account("user", 0, SEED)), n)

	exists_value {
		let n in 1 .. 1000;
		MyValue::put(n);
	}: _(RawOrigin::Signed(account("user", 0, SEED)), n)

	remove_value {
		let i in ...;
	}: _(RawOrigin::Signed(account("user", 0, SEED)), i)

	read_map {
		let i in ...;
	}: _(RawOrigin::Signed(account("user", 0, SEED)), i)

	insert_map {
		let n in 1 .. 1000;
	}: _(RawOrigin::Signed(account("user", 0, SEED)), n)

	contains_key_map {
		let i in ...;
	}: _(RawOrigin::Signed(account("user", 0, SEED)), i)

	remove_prefix {
		let d in ...;
	}: _(RawOrigin::Signed(account("user", 0, SEED)), d)

	do_nothing {
		let n in 1 .. 1000;
	}: _(RawOrigin::Signed(account("user", 0, SEED)), n)

	encode_accounts {
		let a in 1 .. 1000;
		let mut accounts = Vec::new();
		for _ in 0..a {
			accounts.push(account::<T::AccountId>("encode", a, SEED));
		}
	}: _(RawOrigin::Signed(account("user", 0, SEED)), accounts)

	decode_accounts {
		let a in 1 .. 1000;
		let mut accounts = Vec::new();
		for _ in 0..a {
			accounts.push(account::<T::AccountId>("encode", a, SEED));
		}
		let bytes = accounts.encode();
	}: _(RawOrigin::Signed(account("user", 0, SEED)), bytes)

	storage_recalc(steps, repeat)

	current_time(steps, repeat)
}

// Custom implementation to handle benchmarking of storage recalculation.
// Puts `repeat` number of items into random storage keys, and then times how
// long it takes to recalculate the storage root.
fn storage_recalc(steps: Vec<u32>, repeat: u32) -> Result<Vec<BenchmarkResults>, &'static str> {
	let mut results: Vec<BenchmarkResults> = Vec::new();

	let s = if steps.is_empty() { 10 } else { steps[0] };

	for step in 0 .. s {
		for index in 0 .. repeat {
			let random = (index, step).using_encoded(sp_io::hashing::blake2_256);
			sp_io::storage::set(&random, &random);
		}
		let start = frame_benchmarking::benchmarking::current_time();
		frame_benchmarking::storage_root();
		let finish = frame_benchmarking::benchmarking::current_time();
		let elapsed = finish - start;
	
		results.push((vec![(BenchmarkParameter::r, repeat)], 0, elapsed));
	}

	return Ok(results)
}

// Custom implementation to handle benchmarking of calling a host function.
// Will check how long it takes to call `current_time()`.
fn current_time(steps: Vec<u32>, repeat: u32) -> Result<Vec<BenchmarkResults>, &'static str> {
	let mut results: Vec<BenchmarkResults> = Vec::new();

	let s = if steps.is_empty() { 10 } else { steps[0] };

	for _ in 0..s {
		let start = frame_benchmarking::benchmarking::current_time();
		for _ in 0..repeat {
			let _ = frame_benchmarking::benchmarking::current_time();
		}
		let finish = frame_benchmarking::benchmarking::current_time();
		let elapsed = finish - start;

		results.push((vec![(BenchmarkParameter::r, repeat)], elapsed, 0));
	}

	return Ok(results);
}
