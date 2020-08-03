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

//! Weights for the Democracy Pallet

use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};

pub struct WeightInfo;
impl pallet_democracy::WeightInfo for WeightInfo {
	fn propose() -> Weight {
		(59363000 as Weight) // TODO: all those weight must be generated from parity machine.
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn second(s: u32, ) -> Weight {
		(48099000 as Weight)
			.saturating_add((297000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn vote_new(r: u32, ) -> Weight {
		(59267000 as Weight)
			.saturating_add((388000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn vote_existing(r: u32, ) -> Weight {
		(56325000 as Weight)
			.saturating_add((535000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn emergency_cancel() -> Weight {
		(34918000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn external_propose(v: u32, ) -> Weight {
		(15943000 as Weight)
			.saturating_add((137000 as Weight).saturating_mul(v as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn external_propose_majority() -> Weight {
		(3642000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn external_propose_default() -> Weight {
		(3615000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn fast_track() -> Weight {
		(32443000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn veto_external(v: u32, ) -> Weight {
		(33990000 as Weight)
			.saturating_add((242000 as Weight).saturating_mul(v as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn cancel_referendum() -> Weight {
		(21739000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn cancel_queued(r: u32, ) -> Weight {
		(43377000 as Weight)
			.saturating_add((5057000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn on_initialize_base(r: u32, ) -> Weight {
		(73901000 as Weight)
			.saturating_add((12599000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(6 as Weight))
			.saturating_add(DbWeight::get().reads((2 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(5 as Weight))
	}
	fn delegate(r: u32, ) -> Weight {
		(77305000 as Weight)
			.saturating_add((8863000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(4 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	fn undelegate(r: u32, ) -> Weight {
		(44791000 as Weight)
			.saturating_add((8811000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(2 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	fn clear_public_proposals() -> Weight {
		(3982000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn note_preimage(b: u32, ) -> Weight {
		(46711000 as Weight)
			.saturating_add((6000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn note_imminent_preimage(b: u32, ) -> Weight {
		(35368000 as Weight)
			.saturating_add((5000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn reap_preimage(b: u32, ) -> Weight {
		(44919000 as Weight)
			.saturating_add((5000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn unlock_remove(r: u32, ) -> Weight {
		(52727000 as Weight)
			.saturating_add((170000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn unlock_set(r: u32, ) -> Weight {
		(50141000 as Weight)
			.saturating_add((396000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn remove_vote(r: u32, ) -> Weight {
		(31107000 as Weight)
			.saturating_add((410000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn remove_other_vote(r: u32, ) -> Weight {
		(31004000 as Weight)
			.saturating_add((370000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
}
