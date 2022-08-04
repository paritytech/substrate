// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Benchmarks for the Sassafras pallet.

use super::*;
use frame_benchmarking::benchmarks;
use frame_system::RawOrigin;
use sp_io::hashing;

fn make_dummy_ticket(i: usize) -> Ticket {
	let buf = i.to_le_bytes();
	hashing::twox_256(&buf).try_into().unwrap()
}

benchmarks! {
	submit_tickets {
		let x in 0 .. 100;

		// Almost fill the available tickets space.

		let max_tickets: u32 = <T as crate::Config>::MaxTickets::get() - 10;
		let tickets: Vec<Ticket> = (0..max_tickets as usize).into_iter().map(|i| {
			make_dummy_ticket(i)
		}).collect();
		let _ = Pallet::<T>::submit_tickets(RawOrigin::None.into(), tickets);

		// Create the tickets to submit during the benchmark

		let tickets: Vec<Ticket> = (0..x as usize).into_iter().map(|i| {
			make_dummy_ticket(i + max_tickets as usize)
		}).collect();
	}: _(RawOrigin::None, tickets)

	impl_benchmark_test_suite!(
		Pallet,
		crate::mock::new_test_ext(3),
		crate::mock::Test,
	)
}
