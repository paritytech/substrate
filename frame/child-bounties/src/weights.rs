// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Autogenerated weights for pallet_child_bounties
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2022-05-23, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// ./target/production/substrate
// benchmark
// pallet
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_child_bounties
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --template=./.maintain/frame-weight-template.hbs
// --output=./frame/child-bounties/src/weights.rs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_child_bounties.
pub trait WeightInfo {
	fn add_child_bounty(d: u32, ) -> Weight;
	fn propose_curator() -> Weight;
	fn accept_curator() -> Weight;
	fn unassign_curator() -> Weight;
	fn award_child_bounty() -> Weight;
	fn claim_child_bounty() -> Weight;
	fn close_child_bounty_added() -> Weight;
	fn close_child_bounty_active() -> Weight;
}

/// Weights for pallet_child_bounties using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: System Account (r:2 w:2)
	// Storage: ChildBounties ChildBountyCount (r:1 w:1)
	// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	// Storage: ChildBounties ChildBounties (r:0 w:1)
	fn add_child_bounty(d: u32, ) -> Weight {
		(51_064_000 as Weight)
			// Standard Error: 0
			.saturating_add((1_000 as Weight).saturating_mul(d as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(6 as Weight))
	}
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: ChildBounties ChildrenCuratorFees (r:1 w:1)
	fn propose_curator() -> Weight {
		(15_286_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn accept_curator() -> Weight {
		(29_929_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: System Account (r:1 w:1)
	fn unassign_curator() -> Weight {
		(32_449_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	fn award_child_bounty() -> Weight {
		(23_793_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: System Account (r:3 w:3)
	// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	fn claim_child_bounty() -> Weight {
		(67_529_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(6 as Weight))
	}
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: ChildBounties ChildrenCuratorFees (r:1 w:1)
	// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	// Storage: System Account (r:2 w:2)
	// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	fn close_child_bounty_added() -> Weight {
		(48_436_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(6 as Weight))
			.saturating_add(T::DbWeight::get().writes(6 as Weight))
	}
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: System Account (r:3 w:3)
	// Storage: ChildBounties ChildrenCuratorFees (r:1 w:1)
	// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	fn close_child_bounty_active() -> Weight {
		(58_044_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(7 as Weight))
			.saturating_add(T::DbWeight::get().writes(7 as Weight))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: System Account (r:2 w:2)
	// Storage: ChildBounties ChildBountyCount (r:1 w:1)
	// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	// Storage: ChildBounties ChildBounties (r:0 w:1)
	fn add_child_bounty(d: u32, ) -> Weight {
		(51_064_000 as Weight)
			// Standard Error: 0
			.saturating_add((1_000 as Weight).saturating_mul(d as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(6 as Weight))
	}
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: ChildBounties ChildrenCuratorFees (r:1 w:1)
	fn propose_curator() -> Weight {
		(15_286_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn accept_curator() -> Weight {
		(29_929_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: System Account (r:1 w:1)
	fn unassign_curator() -> Weight {
		(32_449_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	fn award_child_bounty() -> Weight {
		(23_793_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: System Account (r:3 w:3)
	// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	fn claim_child_bounty() -> Weight {
		(67_529_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(6 as Weight))
	}
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: ChildBounties ChildrenCuratorFees (r:1 w:1)
	// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	// Storage: System Account (r:2 w:2)
	// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	fn close_child_bounty_added() -> Weight {
		(48_436_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(6 as Weight))
			.saturating_add(RocksDbWeight::get().writes(6 as Weight))
	}
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: System Account (r:3 w:3)
	// Storage: ChildBounties ChildrenCuratorFees (r:1 w:1)
	// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	fn close_child_bounty_active() -> Weight {
		(58_044_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(7 as Weight))
			.saturating_add(RocksDbWeight::get().writes(7 as Weight))
	}
}
