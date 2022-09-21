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
//! DATE: 2022-09-20, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! HOSTNAME: `bm2`, CPU: `Intel(R) Core(TM) i7-7700K CPU @ 4.20GHz`
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
// --heap-pages=4096
// --output=./frame/child-bounties/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs

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
	/// The range of component `d` is `[0, 300]`.
	fn add_child_bounty(d: u32, ) -> Weight {
		Weight::from_ref_time(57_890_000 as u64)
			// Standard Error: 93
			.saturating_add(Weight::from_ref_time(2_519 as u64).saturating_mul(d as u64))
			.saturating_add(T::DbWeight::get().reads(5 as u64))
			.saturating_add(T::DbWeight::get().writes(6 as u64))
	}
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: ChildBounties ChildrenCuratorFees (r:1 w:1)
	fn propose_curator() -> Weight {
		Weight::from_ref_time(21_226_000 as u64)
			.saturating_add(T::DbWeight::get().reads(3 as u64))
			.saturating_add(T::DbWeight::get().writes(2 as u64))
	}
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn accept_curator() -> Weight {
		Weight::from_ref_time(38_093_000 as u64)
			.saturating_add(T::DbWeight::get().reads(3 as u64))
			.saturating_add(T::DbWeight::get().writes(2 as u64))
	}
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: System Account (r:1 w:1)
	fn unassign_curator() -> Weight {
		Weight::from_ref_time(42_179_000 as u64)
			.saturating_add(T::DbWeight::get().reads(3 as u64))
			.saturating_add(T::DbWeight::get().writes(2 as u64))
	}
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	fn award_child_bounty() -> Weight {
		Weight::from_ref_time(30_963_000 as u64)
			.saturating_add(T::DbWeight::get().reads(2 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: System Account (r:3 w:3)
	// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	fn claim_child_bounty() -> Weight {
		Weight::from_ref_time(73_695_000 as u64)
			.saturating_add(T::DbWeight::get().reads(5 as u64))
			.saturating_add(T::DbWeight::get().writes(6 as u64))
	}
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: ChildBounties ChildrenCuratorFees (r:1 w:1)
	// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	// Storage: System Account (r:2 w:2)
	// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	fn close_child_bounty_added() -> Weight {
		Weight::from_ref_time(56_449_000 as u64)
			.saturating_add(T::DbWeight::get().reads(6 as u64))
			.saturating_add(T::DbWeight::get().writes(6 as u64))
	}
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: System Account (r:3 w:3)
	// Storage: ChildBounties ChildrenCuratorFees (r:1 w:1)
	// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	fn close_child_bounty_active() -> Weight {
		Weight::from_ref_time(66_822_000 as u64)
			.saturating_add(T::DbWeight::get().reads(7 as u64))
			.saturating_add(T::DbWeight::get().writes(7 as u64))
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
	/// The range of component `d` is `[0, 300]`.
	fn add_child_bounty(d: u32, ) -> Weight {
		Weight::from_ref_time(57_890_000 as u64)
			// Standard Error: 93
			.saturating_add(Weight::from_ref_time(2_519 as u64).saturating_mul(d as u64))
			.saturating_add(RocksDbWeight::get().reads(5 as u64))
			.saturating_add(RocksDbWeight::get().writes(6 as u64))
	}
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: ChildBounties ChildrenCuratorFees (r:1 w:1)
	fn propose_curator() -> Weight {
		Weight::from_ref_time(21_226_000 as u64)
			.saturating_add(RocksDbWeight::get().reads(3 as u64))
			.saturating_add(RocksDbWeight::get().writes(2 as u64))
	}
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn accept_curator() -> Weight {
		Weight::from_ref_time(38_093_000 as u64)
			.saturating_add(RocksDbWeight::get().reads(3 as u64))
			.saturating_add(RocksDbWeight::get().writes(2 as u64))
	}
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: System Account (r:1 w:1)
	fn unassign_curator() -> Weight {
		Weight::from_ref_time(42_179_000 as u64)
			.saturating_add(RocksDbWeight::get().reads(3 as u64))
			.saturating_add(RocksDbWeight::get().writes(2 as u64))
	}
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	fn award_child_bounty() -> Weight {
		Weight::from_ref_time(30_963_000 as u64)
			.saturating_add(RocksDbWeight::get().reads(2 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: System Account (r:3 w:3)
	// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	fn claim_child_bounty() -> Weight {
		Weight::from_ref_time(73_695_000 as u64)
			.saturating_add(RocksDbWeight::get().reads(5 as u64))
			.saturating_add(RocksDbWeight::get().writes(6 as u64))
	}
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: ChildBounties ChildrenCuratorFees (r:1 w:1)
	// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	// Storage: System Account (r:2 w:2)
	// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	fn close_child_bounty_added() -> Weight {
		Weight::from_ref_time(56_449_000 as u64)
			.saturating_add(RocksDbWeight::get().reads(6 as u64))
			.saturating_add(RocksDbWeight::get().writes(6 as u64))
	}
	// Storage: Bounties Bounties (r:1 w:0)
	// Storage: ChildBounties ChildBounties (r:1 w:1)
	// Storage: System Account (r:3 w:3)
	// Storage: ChildBounties ChildrenCuratorFees (r:1 w:1)
	// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	fn close_child_bounty_active() -> Weight {
		Weight::from_ref_time(66_822_000 as u64)
			.saturating_add(RocksDbWeight::get().reads(7 as u64))
			.saturating_add(RocksDbWeight::get().writes(7 as u64))
	}
}
