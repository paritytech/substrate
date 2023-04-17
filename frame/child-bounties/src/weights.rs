// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Autogenerated weights for pallet_child_bounties
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2023-04-17, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `runner-yu9ayb4d-project-145-concurrent-0`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// ./target/production/substrate
// benchmark
// pallet
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_child_bounties
// --no-storage-info
// --no-median-slopes
// --no-min-squares
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/child-bounties/src/weights.rs
// --header=./HEADER-APACHE2
// --template=./.maintain/frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use core::marker::PhantomData;

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
	/// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	/// Proof: ChildBounties ParentChildBounties (max_values: None, max_size: Some(16), added: 2491, mode: MaxEncodedLen)
	/// Storage: Bounties Bounties (r:1 w:0)
	/// Proof: Bounties Bounties (max_values: None, max_size: Some(177), added: 2652, mode: MaxEncodedLen)
	/// Storage: System Account (r:2 w:2)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBountyCount (r:1 w:1)
	/// Proof: ChildBounties ChildBountyCount (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	/// Proof: ChildBounties ChildBountyDescriptions (max_values: None, max_size: Some(314), added: 2789, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBounties (r:0 w:1)
	/// Proof: ChildBounties ChildBounties (max_values: None, max_size: Some(145), added: 2620, mode: MaxEncodedLen)
	/// The range of component `d` is `[0, 300]`.
	fn add_child_bounty(_d: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `678`
		//  Estimated: `6196`
		// Minimum execution time: 74_647_000 picoseconds.
		Weight::from_parts(77_552_132, 6196)
			.saturating_add(T::DbWeight::get().reads(5_u64))
			.saturating_add(T::DbWeight::get().writes(6_u64))
	}
	/// Storage: Bounties Bounties (r:1 w:0)
	/// Proof: Bounties Bounties (max_values: None, max_size: Some(177), added: 2652, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBounties (r:1 w:1)
	/// Proof: ChildBounties ChildBounties (max_values: None, max_size: Some(145), added: 2620, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildrenCuratorFees (r:1 w:1)
	/// Proof: ChildBounties ChildrenCuratorFees (max_values: None, max_size: Some(28), added: 2503, mode: MaxEncodedLen)
	fn propose_curator() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `732`
		//  Estimated: `3642`
		// Minimum execution time: 19_298_000 picoseconds.
		Weight::from_parts(20_130_000, 3642)
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
	/// Storage: Bounties Bounties (r:1 w:0)
	/// Proof: Bounties Bounties (max_values: None, max_size: Some(177), added: 2652, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBounties (r:1 w:1)
	/// Proof: ChildBounties ChildBounties (max_values: None, max_size: Some(145), added: 2620, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	fn accept_curator() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `878`
		//  Estimated: `3642`
		// Minimum execution time: 37_035_000 picoseconds.
		Weight::from_parts(37_980_000, 3642)
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
	/// Storage: ChildBounties ChildBounties (r:1 w:1)
	/// Proof: ChildBounties ChildBounties (max_values: None, max_size: Some(145), added: 2620, mode: MaxEncodedLen)
	/// Storage: Bounties Bounties (r:1 w:0)
	/// Proof: Bounties Bounties (max_values: None, max_size: Some(177), added: 2652, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	fn unassign_curator() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `878`
		//  Estimated: `3642`
		// Minimum execution time: 39_924_000 picoseconds.
		Weight::from_parts(40_709_000, 3642)
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
	/// Storage: Bounties Bounties (r:1 w:0)
	/// Proof: Bounties Bounties (max_values: None, max_size: Some(177), added: 2652, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBounties (r:1 w:1)
	/// Proof: ChildBounties ChildBounties (max_values: None, max_size: Some(145), added: 2620, mode: MaxEncodedLen)
	fn award_child_bounty() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `775`
		//  Estimated: `3642`
		// Minimum execution time: 23_197_000 picoseconds.
		Weight::from_parts(24_075_000, 3642)
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: ChildBounties ChildBounties (r:1 w:1)
	/// Proof: ChildBounties ChildBounties (max_values: None, max_size: Some(145), added: 2620, mode: MaxEncodedLen)
	/// Storage: System Account (r:3 w:3)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	/// Proof: ChildBounties ParentChildBounties (max_values: None, max_size: Some(16), added: 2491, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	/// Proof: ChildBounties ChildBountyDescriptions (max_values: None, max_size: Some(314), added: 2789, mode: MaxEncodedLen)
	fn claim_child_bounty() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `648`
		//  Estimated: `8799`
		// Minimum execution time: 125_790_000 picoseconds.
		Weight::from_parts(128_334_000, 8799)
			.saturating_add(T::DbWeight::get().reads(5_u64))
			.saturating_add(T::DbWeight::get().writes(6_u64))
	}
	/// Storage: Bounties Bounties (r:1 w:0)
	/// Proof: Bounties Bounties (max_values: None, max_size: Some(177), added: 2652, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBounties (r:1 w:1)
	/// Proof: ChildBounties ChildBounties (max_values: None, max_size: Some(145), added: 2620, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildrenCuratorFees (r:1 w:1)
	/// Proof: ChildBounties ChildrenCuratorFees (max_values: None, max_size: Some(28), added: 2503, mode: MaxEncodedLen)
	/// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	/// Proof: ChildBounties ParentChildBounties (max_values: None, max_size: Some(16), added: 2491, mode: MaxEncodedLen)
	/// Storage: System Account (r:2 w:2)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	/// Proof: ChildBounties ChildBountyDescriptions (max_values: None, max_size: Some(314), added: 2789, mode: MaxEncodedLen)
	fn close_child_bounty_added() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `978`
		//  Estimated: `6196`
		// Minimum execution time: 79_702_000 picoseconds.
		Weight::from_parts(81_413_000, 6196)
			.saturating_add(T::DbWeight::get().reads(6_u64))
			.saturating_add(T::DbWeight::get().writes(6_u64))
	}
	/// Storage: Bounties Bounties (r:1 w:0)
	/// Proof: Bounties Bounties (max_values: None, max_size: Some(177), added: 2652, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBounties (r:1 w:1)
	/// Proof: ChildBounties ChildBounties (max_values: None, max_size: Some(145), added: 2620, mode: MaxEncodedLen)
	/// Storage: System Account (r:3 w:3)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildrenCuratorFees (r:1 w:1)
	/// Proof: ChildBounties ChildrenCuratorFees (max_values: None, max_size: Some(28), added: 2503, mode: MaxEncodedLen)
	/// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	/// Proof: ChildBounties ParentChildBounties (max_values: None, max_size: Some(16), added: 2491, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	/// Proof: ChildBounties ChildBountyDescriptions (max_values: None, max_size: Some(314), added: 2789, mode: MaxEncodedLen)
	fn close_child_bounty_active() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1165`
		//  Estimated: `8799`
		// Minimum execution time: 96_885_000 picoseconds.
		Weight::from_parts(98_873_000, 8799)
			.saturating_add(T::DbWeight::get().reads(7_u64))
			.saturating_add(T::DbWeight::get().writes(7_u64))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	/// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	/// Proof: ChildBounties ParentChildBounties (max_values: None, max_size: Some(16), added: 2491, mode: MaxEncodedLen)
	/// Storage: Bounties Bounties (r:1 w:0)
	/// Proof: Bounties Bounties (max_values: None, max_size: Some(177), added: 2652, mode: MaxEncodedLen)
	/// Storage: System Account (r:2 w:2)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBountyCount (r:1 w:1)
	/// Proof: ChildBounties ChildBountyCount (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	/// Proof: ChildBounties ChildBountyDescriptions (max_values: None, max_size: Some(314), added: 2789, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBounties (r:0 w:1)
	/// Proof: ChildBounties ChildBounties (max_values: None, max_size: Some(145), added: 2620, mode: MaxEncodedLen)
	/// The range of component `d` is `[0, 300]`.
	fn add_child_bounty(_d: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `678`
		//  Estimated: `6196`
		// Minimum execution time: 74_647_000 picoseconds.
		Weight::from_parts(77_552_132, 6196)
			.saturating_add(RocksDbWeight::get().reads(5_u64))
			.saturating_add(RocksDbWeight::get().writes(6_u64))
	}
	/// Storage: Bounties Bounties (r:1 w:0)
	/// Proof: Bounties Bounties (max_values: None, max_size: Some(177), added: 2652, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBounties (r:1 w:1)
	/// Proof: ChildBounties ChildBounties (max_values: None, max_size: Some(145), added: 2620, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildrenCuratorFees (r:1 w:1)
	/// Proof: ChildBounties ChildrenCuratorFees (max_values: None, max_size: Some(28), added: 2503, mode: MaxEncodedLen)
	fn propose_curator() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `732`
		//  Estimated: `3642`
		// Minimum execution time: 19_298_000 picoseconds.
		Weight::from_parts(20_130_000, 3642)
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
	/// Storage: Bounties Bounties (r:1 w:0)
	/// Proof: Bounties Bounties (max_values: None, max_size: Some(177), added: 2652, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBounties (r:1 w:1)
	/// Proof: ChildBounties ChildBounties (max_values: None, max_size: Some(145), added: 2620, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	fn accept_curator() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `878`
		//  Estimated: `3642`
		// Minimum execution time: 37_035_000 picoseconds.
		Weight::from_parts(37_980_000, 3642)
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
	/// Storage: ChildBounties ChildBounties (r:1 w:1)
	/// Proof: ChildBounties ChildBounties (max_values: None, max_size: Some(145), added: 2620, mode: MaxEncodedLen)
	/// Storage: Bounties Bounties (r:1 w:0)
	/// Proof: Bounties Bounties (max_values: None, max_size: Some(177), added: 2652, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	fn unassign_curator() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `878`
		//  Estimated: `3642`
		// Minimum execution time: 39_924_000 picoseconds.
		Weight::from_parts(40_709_000, 3642)
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
	/// Storage: Bounties Bounties (r:1 w:0)
	/// Proof: Bounties Bounties (max_values: None, max_size: Some(177), added: 2652, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBounties (r:1 w:1)
	/// Proof: ChildBounties ChildBounties (max_values: None, max_size: Some(145), added: 2620, mode: MaxEncodedLen)
	fn award_child_bounty() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `775`
		//  Estimated: `3642`
		// Minimum execution time: 23_197_000 picoseconds.
		Weight::from_parts(24_075_000, 3642)
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: ChildBounties ChildBounties (r:1 w:1)
	/// Proof: ChildBounties ChildBounties (max_values: None, max_size: Some(145), added: 2620, mode: MaxEncodedLen)
	/// Storage: System Account (r:3 w:3)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	/// Proof: ChildBounties ParentChildBounties (max_values: None, max_size: Some(16), added: 2491, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	/// Proof: ChildBounties ChildBountyDescriptions (max_values: None, max_size: Some(314), added: 2789, mode: MaxEncodedLen)
	fn claim_child_bounty() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `648`
		//  Estimated: `8799`
		// Minimum execution time: 125_790_000 picoseconds.
		Weight::from_parts(128_334_000, 8799)
			.saturating_add(RocksDbWeight::get().reads(5_u64))
			.saturating_add(RocksDbWeight::get().writes(6_u64))
	}
	/// Storage: Bounties Bounties (r:1 w:0)
	/// Proof: Bounties Bounties (max_values: None, max_size: Some(177), added: 2652, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBounties (r:1 w:1)
	/// Proof: ChildBounties ChildBounties (max_values: None, max_size: Some(145), added: 2620, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildrenCuratorFees (r:1 w:1)
	/// Proof: ChildBounties ChildrenCuratorFees (max_values: None, max_size: Some(28), added: 2503, mode: MaxEncodedLen)
	/// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	/// Proof: ChildBounties ParentChildBounties (max_values: None, max_size: Some(16), added: 2491, mode: MaxEncodedLen)
	/// Storage: System Account (r:2 w:2)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	/// Proof: ChildBounties ChildBountyDescriptions (max_values: None, max_size: Some(314), added: 2789, mode: MaxEncodedLen)
	fn close_child_bounty_added() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `978`
		//  Estimated: `6196`
		// Minimum execution time: 79_702_000 picoseconds.
		Weight::from_parts(81_413_000, 6196)
			.saturating_add(RocksDbWeight::get().reads(6_u64))
			.saturating_add(RocksDbWeight::get().writes(6_u64))
	}
	/// Storage: Bounties Bounties (r:1 w:0)
	/// Proof: Bounties Bounties (max_values: None, max_size: Some(177), added: 2652, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBounties (r:1 w:1)
	/// Proof: ChildBounties ChildBounties (max_values: None, max_size: Some(145), added: 2620, mode: MaxEncodedLen)
	/// Storage: System Account (r:3 w:3)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildrenCuratorFees (r:1 w:1)
	/// Proof: ChildBounties ChildrenCuratorFees (max_values: None, max_size: Some(28), added: 2503, mode: MaxEncodedLen)
	/// Storage: ChildBounties ParentChildBounties (r:1 w:1)
	/// Proof: ChildBounties ParentChildBounties (max_values: None, max_size: Some(16), added: 2491, mode: MaxEncodedLen)
	/// Storage: ChildBounties ChildBountyDescriptions (r:0 w:1)
	/// Proof: ChildBounties ChildBountyDescriptions (max_values: None, max_size: Some(314), added: 2789, mode: MaxEncodedLen)
	fn close_child_bounty_active() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1165`
		//  Estimated: `8799`
		// Minimum execution time: 96_885_000 picoseconds.
		Weight::from_parts(98_873_000, 8799)
			.saturating_add(RocksDbWeight::get().reads(7_u64))
			.saturating_add(RocksDbWeight::get().writes(7_u64))
	}
}
