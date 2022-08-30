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

//! Autogenerated weights for pallet_alliance
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2022-08-26, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! HOSTNAME: `bm3`, CPU: `Intel(R) Core(TM) i7-7700K CPU @ 4.20GHz`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// /home/benchbot/cargo_target_dir/production/substrate
// benchmark
// pallet
// --steps=50
// --repeat=20
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --pallet=pallet_alliance
// --chain=dev
// --output=./frame/alliance/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_alliance.
pub trait WeightInfo {
	fn propose_proposed(b: u32, x: u32, y: u32, p: u32, ) -> Weight;
	fn vote(x: u32, y: u32, ) -> Weight;
	fn veto(p: u32, ) -> Weight;
	fn close_early_disapproved(x: u32, y: u32, p: u32, ) -> Weight;
	fn close_early_approved(b: u32, x: u32, y: u32, p: u32, ) -> Weight;
	fn close_disapproved(x: u32, y: u32, p: u32, ) -> Weight;
	fn close_approved(b: u32, x: u32, y: u32, p: u32, ) -> Weight;
	fn init_members(x: u32, y: u32, z: u32, ) -> Weight;
	fn set_rule() -> Weight;
	fn announce() -> Weight;
	fn remove_announcement() -> Weight;
	fn join_alliance() -> Weight;
	fn nominate_ally() -> Weight;
	fn elevate_ally() -> Weight;
	fn give_retirement_notice() -> Weight;
	fn retire() -> Weight;
	fn kick_member() -> Weight;
	fn add_unscrupulous_items(n: u32, l: u32, ) -> Weight;
	fn remove_unscrupulous_items(n: u32, l: u32, ) -> Weight;
}

/// Weights for pallet_alliance using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	// Storage: Alliance Members (r:1 w:0)
	// Storage: AllianceMotion ProposalOf (r:1 w:1)
	// Storage: AllianceMotion Proposals (r:1 w:1)
	// Storage: AllianceMotion ProposalCount (r:1 w:1)
	// Storage: AllianceMotion Voting (r:0 w:1)
	/// The range of component `b` is `[1, 1024]`.
	/// The range of component `x` is `[2, 10]`.
	/// The range of component `y` is `[0, 90]`.
	/// The range of component `p` is `[1, 100]`.
	fn propose_proposed(b: u32, x: u32, y: u32, p: u32, ) -> Weight {
		(22_575_000 as Weight)
			// Standard Error: 0
			.saturating_add((11_000 as Weight).saturating_mul(b as Weight))
			// Standard Error: 23_000
			.saturating_add((158_000 as Weight).saturating_mul(x as Weight))
			// Standard Error: 2_000
			.saturating_add((90_000 as Weight).saturating_mul(y as Weight))
			// Standard Error: 2_000
			.saturating_add((216_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(4 as Weight))
	}
	// Storage: Alliance Members (r:2 w:0)
	// Storage: AllianceMotion Voting (r:1 w:1)
	/// The range of component `x` is `[3, 10]`.
	/// The range of component `y` is `[2, 90]`.
	fn vote(x: u32, y: u32, ) -> Weight {
		(45_486_000 as Weight)
			// Standard Error: 29_000
			.saturating_add((78_000 as Weight).saturating_mul(x as Weight))
			// Standard Error: 2_000
			.saturating_add((128_000 as Weight).saturating_mul(y as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: Alliance Members (r:1 w:0)
	// Storage: AllianceMotion ProposalOf (r:1 w:1)
	// Storage: AllianceMotion Proposals (r:1 w:1)
	// Storage: AllianceMotion Voting (r:0 w:1)
	/// The range of component `p` is `[1, 100]`.
	fn veto(p: u32, ) -> Weight {
		(35_296_000 as Weight)
			// Standard Error: 2_000
			.saturating_add((171_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	// Storage: Alliance Members (r:1 w:0)
	// Storage: AllianceMotion Voting (r:1 w:1)
	// Storage: AllianceMotion Members (r:1 w:0)
	// Storage: AllianceMotion Proposals (r:1 w:1)
	// Storage: AllianceMotion ProposalOf (r:0 w:1)
	/// The range of component `x` is `[2, 10]`.
	/// The range of component `y` is `[2, 90]`.
	/// The range of component `p` is `[1, 100]`.
	fn close_early_disapproved(x: u32, y: u32, p: u32, ) -> Weight {
		(39_252_000 as Weight)
			// Standard Error: 18_000
			.saturating_add((75_000 as Weight).saturating_mul(x as Weight))
			// Standard Error: 1_000
			.saturating_add((107_000 as Weight).saturating_mul(y as Weight))
			// Standard Error: 1_000
			.saturating_add((170_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	// Storage: Alliance Members (r:1 w:0)
	// Storage: AllianceMotion Voting (r:1 w:1)
	// Storage: AllianceMotion Members (r:1 w:0)
	// Storage: AllianceMotion ProposalOf (r:1 w:1)
	// Storage: AllianceMotion Proposals (r:1 w:1)
	/// The range of component `b` is `[1, 1024]`.
	/// The range of component `x` is `[2, 10]`.
	/// The range of component `y` is `[2, 90]`.
	/// The range of component `p` is `[1, 100]`.
	fn close_early_approved(_b: u32, _x: u32, y: u32, p: u32, ) -> Weight {
		(50_357_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((103_000 as Weight).saturating_mul(y as Weight))
			// Standard Error: 1_000
			.saturating_add((204_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	// Storage: Alliance Members (r:1 w:0)
	// Storage: AllianceMotion Voting (r:1 w:1)
	// Storage: AllianceMotion Members (r:1 w:0)
	// Storage: AllianceMotion Prime (r:1 w:0)
	// Storage: AllianceMotion Proposals (r:1 w:1)
	// Storage: AllianceMotion ProposalOf (r:0 w:1)
	/// The range of component `x` is `[2, 10]`.
	/// The range of component `y` is `[2, 90]`.
	/// The range of component `p` is `[1, 100]`.
	fn close_disapproved(_x: u32, y: u32, p: u32, ) -> Weight {
		(41_258_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((111_000 as Weight).saturating_mul(y as Weight))
			// Standard Error: 1_000
			.saturating_add((186_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	// Storage: Alliance Members (r:1 w:0)
	// Storage: AllianceMotion Voting (r:1 w:1)
	// Storage: AllianceMotion Members (r:1 w:0)
	// Storage: AllianceMotion Prime (r:1 w:0)
	// Storage: AllianceMotion Proposals (r:1 w:1)
	// Storage: AllianceMotion ProposalOf (r:0 w:1)
	/// The range of component `b` is `[1, 1024]`.
	/// The range of component `x` is `[2, 10]`.
	/// The range of component `y` is `[2, 90]`.
	/// The range of component `p` is `[1, 100]`.
	fn close_approved(_b: u32, x: u32, y: u32, p: u32, ) -> Weight {
		(40_490_000 as Weight)
			// Standard Error: 16_000
			.saturating_add((119_000 as Weight).saturating_mul(x as Weight))
			// Standard Error: 1_000
			.saturating_add((93_000 as Weight).saturating_mul(y as Weight))
			// Standard Error: 1_000
			.saturating_add((195_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	// Storage: Alliance Members (r:2 w:3)
	// Storage: AllianceMotion Members (r:1 w:1)
	/// The range of component `x` is `[2, 10]`.
	/// The range of component `y` is `[0, 90]`.
	/// The range of component `z` is `[0, 100]`.
	fn init_members(_x: u32, y: u32, z: u32, ) -> Weight {
		(35_186_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((161_000 as Weight).saturating_mul(y as Weight))
			// Standard Error: 1_000
			.saturating_add((127_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(4 as Weight))
	}
	// Storage: Alliance Rule (r:0 w:1)
	fn set_rule() -> Weight {
		(18_189_000 as Weight)
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: Alliance Announcements (r:1 w:1)
	fn announce() -> Weight {
		(21_106_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: Alliance Announcements (r:1 w:1)
	fn remove_announcement() -> Weight {
		(22_208_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: Alliance Members (r:4 w:1)
	// Storage: Alliance UnscrupulousAccounts (r:1 w:0)
	// Storage: System Account (r:1 w:1)
	// Storage: Alliance DepositOf (r:0 w:1)
	fn join_alliance() -> Weight {
		(53_771_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(6 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	// Storage: Alliance Members (r:4 w:1)
	// Storage: Alliance UnscrupulousAccounts (r:1 w:0)
	fn nominate_ally() -> Weight {
		(41_912_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: Alliance Members (r:3 w:2)
	// Storage: AllianceMotion Proposals (r:1 w:0)
	// Storage: AllianceMotion Members (r:0 w:1)
	// Storage: AllianceMotion Prime (r:0 w:1)
	fn elevate_ally() -> Weight {
		(36_811_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(4 as Weight))
	}
	// Storage: Alliance Members (r:4 w:2)
	// Storage: AllianceMotion Proposals (r:1 w:0)
	// Storage: AllianceMotion Members (r:0 w:1)
	// Storage: AllianceMotion Prime (r:0 w:1)
	// Storage: Alliance RetiringMembers (r:0 w:1)
	fn give_retirement_notice() -> Weight {
		(41_079_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(5 as Weight))
	}
	// Storage: Alliance RetiringMembers (r:1 w:1)
	// Storage: Alliance Members (r:1 w:1)
	// Storage: Alliance DepositOf (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn retire() -> Weight {
		(42_703_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(4 as Weight))
	}
	// Storage: Alliance Members (r:3 w:1)
	// Storage: AllianceMotion Proposals (r:1 w:0)
	// Storage: Alliance DepositOf (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	// Storage: AllianceMotion Members (r:0 w:1)
	// Storage: AllianceMotion Prime (r:0 w:1)
	fn kick_member() -> Weight {
		(61_370_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(6 as Weight))
			.saturating_add(T::DbWeight::get().writes(5 as Weight))
	}
	// Storage: Alliance UnscrupulousAccounts (r:1 w:1)
	// Storage: Alliance UnscrupulousWebsites (r:1 w:1)
	/// The range of component `n` is `[1, 100]`.
	/// The range of component `l` is `[1, 255]`.
	fn add_unscrupulous_items(n: u32, l: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 2_000
			.saturating_add((1_385_000 as Weight).saturating_mul(n as Weight))
			// Standard Error: 1_000
			.saturating_add((119_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	// Storage: Alliance UnscrupulousAccounts (r:1 w:1)
	// Storage: Alliance UnscrupulousWebsites (r:1 w:1)
	/// The range of component `n` is `[1, 100]`.
	/// The range of component `l` is `[1, 255]`.
	fn remove_unscrupulous_items(n: u32, l: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 153_000
			.saturating_add((21_484_000 as Weight).saturating_mul(n as Weight))
			// Standard Error: 59_000
			.saturating_add((3_772_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	// Storage: Alliance Members (r:1 w:0)
	// Storage: AllianceMotion ProposalOf (r:1 w:1)
	// Storage: AllianceMotion Proposals (r:1 w:1)
	// Storage: AllianceMotion ProposalCount (r:1 w:1)
	// Storage: AllianceMotion Voting (r:0 w:1)
	/// The range of component `b` is `[1, 1024]`.
	/// The range of component `x` is `[2, 10]`.
	/// The range of component `y` is `[0, 90]`.
	/// The range of component `p` is `[1, 100]`.
	fn propose_proposed(b: u32, x: u32, y: u32, p: u32, ) -> Weight {
		(22_575_000 as Weight)
			// Standard Error: 0
			.saturating_add((11_000 as Weight).saturating_mul(b as Weight))
			// Standard Error: 23_000
			.saturating_add((158_000 as Weight).saturating_mul(x as Weight))
			// Standard Error: 2_000
			.saturating_add((90_000 as Weight).saturating_mul(y as Weight))
			// Standard Error: 2_000
			.saturating_add((216_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))
	}
	// Storage: Alliance Members (r:2 w:0)
	// Storage: AllianceMotion Voting (r:1 w:1)
	/// The range of component `x` is `[3, 10]`.
	/// The range of component `y` is `[2, 90]`.
	fn vote(x: u32, y: u32, ) -> Weight {
		(45_486_000 as Weight)
			// Standard Error: 29_000
			.saturating_add((78_000 as Weight).saturating_mul(x as Weight))
			// Standard Error: 2_000
			.saturating_add((128_000 as Weight).saturating_mul(y as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: Alliance Members (r:1 w:0)
	// Storage: AllianceMotion ProposalOf (r:1 w:1)
	// Storage: AllianceMotion Proposals (r:1 w:1)
	// Storage: AllianceMotion Voting (r:0 w:1)
	/// The range of component `p` is `[1, 100]`.
	fn veto(p: u32, ) -> Weight {
		(35_296_000 as Weight)
			// Standard Error: 2_000
			.saturating_add((171_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	// Storage: Alliance Members (r:1 w:0)
	// Storage: AllianceMotion Voting (r:1 w:1)
	// Storage: AllianceMotion Members (r:1 w:0)
	// Storage: AllianceMotion Proposals (r:1 w:1)
	// Storage: AllianceMotion ProposalOf (r:0 w:1)
	/// The range of component `x` is `[2, 10]`.
	/// The range of component `y` is `[2, 90]`.
	/// The range of component `p` is `[1, 100]`.
	fn close_early_disapproved(x: u32, y: u32, p: u32, ) -> Weight {
		(39_252_000 as Weight)
			// Standard Error: 18_000
			.saturating_add((75_000 as Weight).saturating_mul(x as Weight))
			// Standard Error: 1_000
			.saturating_add((107_000 as Weight).saturating_mul(y as Weight))
			// Standard Error: 1_000
			.saturating_add((170_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	// Storage: Alliance Members (r:1 w:0)
	// Storage: AllianceMotion Voting (r:1 w:1)
	// Storage: AllianceMotion Members (r:1 w:0)
	// Storage: AllianceMotion ProposalOf (r:1 w:1)
	// Storage: AllianceMotion Proposals (r:1 w:1)
	/// The range of component `b` is `[1, 1024]`.
	/// The range of component `x` is `[2, 10]`.
	/// The range of component `y` is `[2, 90]`.
	/// The range of component `p` is `[1, 100]`.
	fn close_early_approved(_b: u32, _x: u32, y: u32, p: u32, ) -> Weight {
		(50_357_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((103_000 as Weight).saturating_mul(y as Weight))
			// Standard Error: 1_000
			.saturating_add((204_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	// Storage: Alliance Members (r:1 w:0)
	// Storage: AllianceMotion Voting (r:1 w:1)
	// Storage: AllianceMotion Members (r:1 w:0)
	// Storage: AllianceMotion Prime (r:1 w:0)
	// Storage: AllianceMotion Proposals (r:1 w:1)
	// Storage: AllianceMotion ProposalOf (r:0 w:1)
	/// The range of component `x` is `[2, 10]`.
	/// The range of component `y` is `[2, 90]`.
	/// The range of component `p` is `[1, 100]`.
	fn close_disapproved(_x: u32, y: u32, p: u32, ) -> Weight {
		(41_258_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((111_000 as Weight).saturating_mul(y as Weight))
			// Standard Error: 1_000
			.saturating_add((186_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	// Storage: Alliance Members (r:1 w:0)
	// Storage: AllianceMotion Voting (r:1 w:1)
	// Storage: AllianceMotion Members (r:1 w:0)
	// Storage: AllianceMotion Prime (r:1 w:0)
	// Storage: AllianceMotion Proposals (r:1 w:1)
	// Storage: AllianceMotion ProposalOf (r:0 w:1)
	/// The range of component `b` is `[1, 1024]`.
	/// The range of component `x` is `[2, 10]`.
	/// The range of component `y` is `[2, 90]`.
	/// The range of component `p` is `[1, 100]`.
	fn close_approved(_b: u32, x: u32, y: u32, p: u32, ) -> Weight {
		(40_490_000 as Weight)
			// Standard Error: 16_000
			.saturating_add((119_000 as Weight).saturating_mul(x as Weight))
			// Standard Error: 1_000
			.saturating_add((93_000 as Weight).saturating_mul(y as Weight))
			// Standard Error: 1_000
			.saturating_add((195_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	// Storage: Alliance Members (r:2 w:3)
	// Storage: AllianceMotion Members (r:1 w:1)
	/// The range of component `x` is `[2, 10]`.
	/// The range of component `y` is `[0, 90]`.
	/// The range of component `z` is `[0, 100]`.
	fn init_members(_x: u32, y: u32, z: u32, ) -> Weight {
		(35_186_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((161_000 as Weight).saturating_mul(y as Weight))
			// Standard Error: 1_000
			.saturating_add((127_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))
	}
	// Storage: Alliance Rule (r:0 w:1)
	fn set_rule() -> Weight {
		(18_189_000 as Weight)
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: Alliance Announcements (r:1 w:1)
	fn announce() -> Weight {
		(21_106_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: Alliance Announcements (r:1 w:1)
	fn remove_announcement() -> Weight {
		(22_208_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: Alliance Members (r:4 w:1)
	// Storage: Alliance UnscrupulousAccounts (r:1 w:0)
	// Storage: System Account (r:1 w:1)
	// Storage: Alliance DepositOf (r:0 w:1)
	fn join_alliance() -> Weight {
		(53_771_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(6 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	// Storage: Alliance Members (r:4 w:1)
	// Storage: Alliance UnscrupulousAccounts (r:1 w:0)
	fn nominate_ally() -> Weight {
		(41_912_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: Alliance Members (r:3 w:2)
	// Storage: AllianceMotion Proposals (r:1 w:0)
	// Storage: AllianceMotion Members (r:0 w:1)
	// Storage: AllianceMotion Prime (r:0 w:1)
	fn elevate_ally() -> Weight {
		(36_811_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))
	}
	// Storage: Alliance Members (r:4 w:2)
	// Storage: AllianceMotion Proposals (r:1 w:0)
	// Storage: AllianceMotion Members (r:0 w:1)
	// Storage: AllianceMotion Prime (r:0 w:1)
	// Storage: Alliance RetiringMembers (r:0 w:1)
	fn give_retirement_notice() -> Weight {
		(41_079_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(5 as Weight))
	}
	// Storage: Alliance RetiringMembers (r:1 w:1)
	// Storage: Alliance Members (r:1 w:1)
	// Storage: Alliance DepositOf (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn retire() -> Weight {
		(42_703_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))
	}
	// Storage: Alliance Members (r:3 w:1)
	// Storage: AllianceMotion Proposals (r:1 w:0)
	// Storage: Alliance DepositOf (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	// Storage: AllianceMotion Members (r:0 w:1)
	// Storage: AllianceMotion Prime (r:0 w:1)
	fn kick_member() -> Weight {
		(61_370_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(6 as Weight))
			.saturating_add(RocksDbWeight::get().writes(5 as Weight))
	}
	// Storage: Alliance UnscrupulousAccounts (r:1 w:1)
	// Storage: Alliance UnscrupulousWebsites (r:1 w:1)
	/// The range of component `n` is `[1, 100]`.
	/// The range of component `l` is `[1, 255]`.
	fn add_unscrupulous_items(n: u32, l: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 2_000
			.saturating_add((1_385_000 as Weight).saturating_mul(n as Weight))
			// Standard Error: 1_000
			.saturating_add((119_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	// Storage: Alliance UnscrupulousAccounts (r:1 w:1)
	// Storage: Alliance UnscrupulousWebsites (r:1 w:1)
	/// The range of component `n` is `[1, 100]`.
	/// The range of component `l` is `[1, 255]`.
	fn remove_unscrupulous_items(n: u32, l: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 153_000
			.saturating_add((21_484_000 as Weight).saturating_mul(n as Weight))
			// Standard Error: 59_000
			.saturating_add((3_772_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
}
