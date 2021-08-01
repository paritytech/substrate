// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Autogenerated weights for pallet_collective
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2021-07-31, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 128

// Executed Command:
// target/release/substrate
// benchmark
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_collective
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/collective/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs


#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_collective.
pub trait WeightInfo {
	fn set_members(m: u32, n: u32, p: u32, ) -> Weight;
	fn execute(b: u32, m: u32, ) -> Weight;
	fn propose_execute(b: u32, m: u32, ) -> Weight;
	fn propose_proposed(b: u32, m: u32, p: u32, ) -> Weight;
	fn vote(m: u32, ) -> Weight;
	fn close_early_disapproved(m: u32, p: u32, ) -> Weight;
	fn close_early_approved(b: u32, m: u32, p: u32, ) -> Weight;
	fn close_disapproved(m: u32, p: u32, ) -> Weight;
	fn close_approved(b: u32, m: u32, p: u32, ) -> Weight;
	fn disapprove_proposal(p: u32, ) -> Weight;
}

/// Weights for pallet_collective using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	// Storage: Instance1Collective Prime (r:0 w:1)
	// Storage: Instance1Collective Voting (r:100 w:100)
	// Storage: Instance1Collective Proposals (r:1 w:0)
	// Storage: Instance1Collective Members (r:1 w:1)
	fn set_members(m: u32, _n: u32, p: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 12_000
			.saturating_add((14_135_000 as Weight).saturating_mul(m as Weight))
			// Standard Error: 12_000
			.saturating_add((19_664_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().reads((1 as Weight).saturating_mul(p as Weight)))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(p as Weight)))
	}
	// Storage: Instance1Collective Members (r:1 w:0)
	fn execute(b: u32, m: u32, ) -> Weight {
		(23_981_000 as Weight)
			// Standard Error: 0
			.saturating_add((3_000 as Weight).saturating_mul(b as Weight))
			// Standard Error: 0
			.saturating_add((95_000 as Weight).saturating_mul(m as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
	}
	// Storage: Instance1Collective ProposalOf (r:1 w:0)
	// Storage: Instance1Collective Members (r:1 w:0)
	fn propose_execute(b: u32, m: u32, ) -> Weight {
		(28_557_000 as Weight)
			// Standard Error: 0
			.saturating_add((3_000 as Weight).saturating_mul(b as Weight))
			// Standard Error: 0
			.saturating_add((184_000 as Weight).saturating_mul(m as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
	}
	// Storage: Instance1Collective Members (r:1 w:0)
	// Storage: Instance1Collective ProposalCount (r:1 w:1)
	// Storage: Instance1Collective Voting (r:0 w:1)
	// Storage: Instance1Collective ProposalOf (r:1 w:1)
	// Storage: Instance1Collective Proposals (r:1 w:1)
	fn propose_proposed(b: u32, m: u32, p: u32, ) -> Weight {
		(48_668_000 as Weight)
			// Standard Error: 0
			.saturating_add((1_000 as Weight).saturating_mul(b as Weight))
			// Standard Error: 4_000
			.saturating_add((119_000 as Weight).saturating_mul(m as Weight))
			// Standard Error: 4_000
			.saturating_add((430_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(4 as Weight))
	}
	// Storage: Instance1Collective Members (r:1 w:0)
	// Storage: Instance1Collective Voting (r:1 w:1)
	fn vote(m: u32, ) -> Weight {
		(37_802_000 as Weight)
			// Standard Error: 3_000
			.saturating_add((250_000 as Weight).saturating_mul(m as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: Instance1Collective ProposalOf (r:0 w:1)
	// Storage: Instance1Collective Members (r:1 w:0)
	// Storage: Instance1Collective Voting (r:1 w:1)
	// Storage: Instance1Collective Proposals (r:1 w:1)
	fn close_early_disapproved(m: u32, p: u32, ) -> Weight {
		(40_274_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((210_000 as Weight).saturating_mul(m as Weight))
			// Standard Error: 1_000
			.saturating_add((376_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	// Storage: Instance1Collective Members (r:1 w:0)
	// Storage: Instance1Collective Proposals (r:1 w:1)
	// Storage: Instance1Collective Voting (r:1 w:1)
	// Storage: Instance1Collective ProposalOf (r:1 w:1)
	fn close_early_approved(_b: u32, m: u32, p: u32, ) -> Weight {
		(63_058_000 as Weight)
			// Standard Error: 3_000
			.saturating_add((207_000 as Weight).saturating_mul(m as Weight))
			// Standard Error: 3_000
			.saturating_add((429_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	// Storage: Instance1Collective Proposals (r:1 w:1)
	// Storage: Instance1Collective Members (r:1 w:0)
	// Storage: Instance1Collective Prime (r:1 w:0)
	// Storage: Instance1Collective Voting (r:1 w:1)
	// Storage: Instance1Collective ProposalOf (r:0 w:1)
	fn close_disapproved(m: u32, p: u32, ) -> Weight {
		(37_697_000 as Weight)
			// Standard Error: 3_000
			.saturating_add((300_000 as Weight).saturating_mul(m as Weight))
			// Standard Error: 3_000
			.saturating_add((514_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	// Storage: Instance1Collective ProposalOf (r:1 w:1)
	// Storage: Instance1Collective Proposals (r:1 w:1)
	// Storage: Instance1Collective Voting (r:1 w:1)
	// Storage: Instance1Collective Prime (r:1 w:0)
	// Storage: Instance1Collective Members (r:1 w:0)
	fn close_approved(_b: u32, m: u32, p: u32, ) -> Weight {
		(70_418_000 as Weight)
			// Standard Error: 4_000
			.saturating_add((197_000 as Weight).saturating_mul(m as Weight))
			// Standard Error: 3_000
			.saturating_add((410_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	// Storage: Instance1Collective ProposalOf (r:0 w:1)
	// Storage: Instance1Collective Voting (r:0 w:1)
	// Storage: Instance1Collective Proposals (r:1 w:1)
	fn disapprove_proposal(p: u32, ) -> Weight {
		(27_955_000 as Weight)
			// Standard Error: 2_000
			.saturating_add((526_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	// Storage: Instance1Collective Prime (r:0 w:1)
	// Storage: Instance1Collective Voting (r:100 w:100)
	// Storage: Instance1Collective Proposals (r:1 w:0)
	// Storage: Instance1Collective Members (r:1 w:1)
	fn set_members(m: u32, _n: u32, p: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 12_000
			.saturating_add((14_135_000 as Weight).saturating_mul(m as Weight))
			// Standard Error: 12_000
			.saturating_add((19_664_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(p as Weight)))
	}
	// Storage: Instance1Collective Members (r:1 w:0)
	fn execute(b: u32, m: u32, ) -> Weight {
		(23_981_000 as Weight)
			// Standard Error: 0
			.saturating_add((3_000 as Weight).saturating_mul(b as Weight))
			// Standard Error: 0
			.saturating_add((95_000 as Weight).saturating_mul(m as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
	}
	// Storage: Instance1Collective ProposalOf (r:1 w:0)
	// Storage: Instance1Collective Members (r:1 w:0)
	fn propose_execute(b: u32, m: u32, ) -> Weight {
		(28_557_000 as Weight)
			// Standard Error: 0
			.saturating_add((3_000 as Weight).saturating_mul(b as Weight))
			// Standard Error: 0
			.saturating_add((184_000 as Weight).saturating_mul(m as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
	}
	// Storage: Instance1Collective Members (r:1 w:0)
	// Storage: Instance1Collective ProposalCount (r:1 w:1)
	// Storage: Instance1Collective Voting (r:0 w:1)
	// Storage: Instance1Collective ProposalOf (r:1 w:1)
	// Storage: Instance1Collective Proposals (r:1 w:1)
	fn propose_proposed(b: u32, m: u32, p: u32, ) -> Weight {
		(48_668_000 as Weight)
			// Standard Error: 0
			.saturating_add((1_000 as Weight).saturating_mul(b as Weight))
			// Standard Error: 4_000
			.saturating_add((119_000 as Weight).saturating_mul(m as Weight))
			// Standard Error: 4_000
			.saturating_add((430_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))
	}
	// Storage: Instance1Collective Members (r:1 w:0)
	// Storage: Instance1Collective Voting (r:1 w:1)
	fn vote(m: u32, ) -> Weight {
		(37_802_000 as Weight)
			// Standard Error: 3_000
			.saturating_add((250_000 as Weight).saturating_mul(m as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: Instance1Collective ProposalOf (r:0 w:1)
	// Storage: Instance1Collective Members (r:1 w:0)
	// Storage: Instance1Collective Voting (r:1 w:1)
	// Storage: Instance1Collective Proposals (r:1 w:1)
	fn close_early_disapproved(m: u32, p: u32, ) -> Weight {
		(40_274_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((210_000 as Weight).saturating_mul(m as Weight))
			// Standard Error: 1_000
			.saturating_add((376_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	// Storage: Instance1Collective Members (r:1 w:0)
	// Storage: Instance1Collective Proposals (r:1 w:1)
	// Storage: Instance1Collective Voting (r:1 w:1)
	// Storage: Instance1Collective ProposalOf (r:1 w:1)
	fn close_early_approved(_b: u32, m: u32, p: u32, ) -> Weight {
		(63_058_000 as Weight)
			// Standard Error: 3_000
			.saturating_add((207_000 as Weight).saturating_mul(m as Weight))
			// Standard Error: 3_000
			.saturating_add((429_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	// Storage: Instance1Collective Proposals (r:1 w:1)
	// Storage: Instance1Collective Members (r:1 w:0)
	// Storage: Instance1Collective Prime (r:1 w:0)
	// Storage: Instance1Collective Voting (r:1 w:1)
	// Storage: Instance1Collective ProposalOf (r:0 w:1)
	fn close_disapproved(m: u32, p: u32, ) -> Weight {
		(37_697_000 as Weight)
			// Standard Error: 3_000
			.saturating_add((300_000 as Weight).saturating_mul(m as Weight))
			// Standard Error: 3_000
			.saturating_add((514_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	// Storage: Instance1Collective ProposalOf (r:1 w:1)
	// Storage: Instance1Collective Proposals (r:1 w:1)
	// Storage: Instance1Collective Voting (r:1 w:1)
	// Storage: Instance1Collective Prime (r:1 w:0)
	// Storage: Instance1Collective Members (r:1 w:0)
	fn close_approved(_b: u32, m: u32, p: u32, ) -> Weight {
		(70_418_000 as Weight)
			// Standard Error: 4_000
			.saturating_add((197_000 as Weight).saturating_mul(m as Weight))
			// Standard Error: 3_000
			.saturating_add((410_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	// Storage: Instance1Collective ProposalOf (r:0 w:1)
	// Storage: Instance1Collective Voting (r:0 w:1)
	// Storage: Instance1Collective Proposals (r:1 w:1)
	fn disapprove_proposal(p: u32, ) -> Weight {
		(27_955_000 as Weight)
			// Standard Error: 2_000
			.saturating_add((526_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
}
