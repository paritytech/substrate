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
use sp_consensus_sassafras::VrfOutput;

// Makes a dummy ticket envelope.
// The resulting ticket-id is not very important and is expected to be below the
// configured threshold (which is guaranteed because we are using mock::TEST_EPOCH_CONFIGURATION).
fn make_dummy_ticket(attempt_idx: u32) -> TicketEnvelope {
	let mut output_enc: &[u8] = &[
		0x0c, 0x1a, 0x83, 0x5e, 0x56, 0x9b, 0x18, 0xa0, 0xd9, 0x13, 0x39, 0x7e, 0xb9, 0x5a, 0x39,
		0x83, 0xf3, 0xc5, 0x73, 0xf6, 0xb1, 0x35, 0xa6, 0x48, 0xa3, 0x83, 0xac, 0x3b, 0xb8, 0x43,
		0xa7, 0x3d,
	];
	let output = VrfOutput::decode(&mut output_enc).unwrap();
	let data = TicketData { attempt_idx, erased_public: Default::default() };
	TicketEnvelope { data, vrf_preout: output, ring_proof: () }
}

benchmarks! {
	submit_tickets {
		let x in 0 .. <T as Config>::MaxTickets::get();

		let tickets: BoundedVec<TicketEnvelope, <T as Config>::MaxTickets> =
			(0..x).map(make_dummy_ticket).collect::<Vec<_>>().try_into().unwrap();
	}: _(RawOrigin::None, tickets)

	impl_benchmark_test_suite!(
		Pallet,
		crate::mock::new_test_ext(1),
		crate::mock::Test,
	)
}
