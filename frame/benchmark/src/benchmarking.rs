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

//! Benchmarks for common FRAME Pallet operations.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use frame_system::RawOrigin;
use sp_std::prelude::*;
use frame_benchmarking::{benchmarks, account};

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

	// Custom implementation to handle benchmarking of storage recalculation.
	// Puts `repeat` number of items into random storage keys, and then times how
	// long it takes to recalculate the storage root.
	storage_root {
		let z in 0 .. 10000;
	}: {
		for index in 0 .. z {
			let random = (index).using_encoded(sp_io::hashing::blake2_256);
			sp_io::storage::set(&random, &random);
		}
	}

	// Custom implementation to handle benchmarking of calling a host function.
	// Will check how long it takes to call `current_time()`.
	current_time {
		let z in 0 .. 1000;
	}: {
		for _ in 0 .. z {
			let _ = frame_benchmarking::benchmarking::current_time();
		}
	}
}
