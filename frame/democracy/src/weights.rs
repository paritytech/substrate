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

//! Autogenerated weights for pallet_democracy
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2021-08-06, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 128

// Executed Command:
// target/release/substrate
// benchmark
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_democracy
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/democracy/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs


#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_democracy.
pub trait WeightInfo {
	fn propose() -> Weight;
	fn second(s: u32, ) -> Weight;
	fn vote_new(r: u32, ) -> Weight;
	fn vote_existing(r: u32, ) -> Weight;
	fn emergency_cancel() -> Weight;
	fn blacklist(p: u32, ) -> Weight;
	fn external_propose(v: u32, ) -> Weight;
	fn external_propose_majority() -> Weight;
	fn external_propose_default() -> Weight;
	fn fast_track() -> Weight;
	fn veto_external(v: u32, ) -> Weight;
	fn cancel_proposal(p: u32, ) -> Weight;
	fn cancel_referendum() -> Weight;
	fn cancel_queued(r: u32, ) -> Weight;
	fn on_initialize_base(r: u32, ) -> Weight;
	fn delegate(r: u32, ) -> Weight;
	fn undelegate(r: u32, ) -> Weight;
	fn clear_public_proposals() -> Weight;
	fn note_preimage(b: u32, ) -> Weight;
	fn note_imminent_preimage(b: u32, ) -> Weight;
	fn reap_preimage(b: u32, ) -> Weight;
	fn unlock_remove(r: u32, ) -> Weight;
	fn unlock_set(r: u32, ) -> Weight;
	fn remove_vote(r: u32, ) -> Weight;
	fn remove_other_vote(r: u32, ) -> Weight;
}

/// Weights for pallet_democracy using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	// Storage: Democracy PublicPropCount (r:1 w:1)
	// Storage: Democracy Blacklist (r:1 w:0)
	// Storage: Democracy PublicProps (r:1 w:1)
	// Storage: Democracy DepositOf (r:0 w:1)
	fn propose() -> Weight {
		(60_473_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	// Storage: Democracy DepositOf (r:1 w:1)
	fn second(s: u32, ) -> Weight {
		(40_878_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((157_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: Democracy VotingOf (r:1 w:1)
	// Storage: Democracy ReferendumInfoOf (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	fn vote_new(r: u32, ) -> Weight {
		(46_689_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((179_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	// Storage: Democracy VotingOf (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: Democracy ReferendumInfoOf (r:1 w:1)
	fn vote_existing(r: u32, ) -> Weight {
		(46_624_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((174_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	// Storage: Democracy Cancellations (r:1 w:1)
	// Storage: Democracy ReferendumInfoOf (r:1 w:1)
	fn emergency_cancel() -> Weight {
		(27_730_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	// Storage: Democracy ReferendumInfoOf (r:1 w:1)
	// Storage: Democracy PublicProps (r:1 w:1)
	// Storage: Democracy NextExternal (r:1 w:1)
	// Storage: Democracy Blacklist (r:0 w:1)
	// Storage: System Account (r:1 w:1)
	// Storage: Democracy DepositOf (r:1 w:1)
	fn blacklist(p: u32, ) -> Weight {
		(80_687_000 as Weight)
			// Standard Error: 4_000
			.saturating_add((495_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(6 as Weight))
	}
	// Storage: Democracy NextExternal (r:1 w:1)
	// Storage: Democracy Blacklist (r:1 w:0)
	fn external_propose(v: u32, ) -> Weight {
		(13_725_000 as Weight)
			// Standard Error: 0
			.saturating_add((91_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: Democracy NextExternal (r:0 w:1)
	fn external_propose_majority() -> Weight {
		(3_044_000 as Weight)
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: Democracy NextExternal (r:0 w:1)
	fn external_propose_default() -> Weight {
		(3_026_000 as Weight)
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: Democracy ReferendumInfoOf (r:0 w:1)
	// Storage: Democracy NextExternal (r:1 w:1)
	// Storage: Democracy ReferendumCount (r:1 w:1)
	fn fast_track() -> Weight {
		(28_457_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	// Storage: Democracy Blacklist (r:1 w:1)
	// Storage: Democracy NextExternal (r:1 w:1)
	fn veto_external(v: u32, ) -> Weight {
		(29_556_000 as Weight)
			// Standard Error: 0
			.saturating_add((134_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	// Storage: System Account (r:1 w:1)
	// Storage: Democracy PublicProps (r:1 w:1)
	// Storage: Democracy DepositOf (r:1 w:1)
	fn cancel_proposal(p: u32, ) -> Weight {
		(54_400_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((483_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	// Storage: Democracy ReferendumInfoOf (r:0 w:1)
	fn cancel_referendum() -> Weight {
		(17_561_000 as Weight)
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: Scheduler Agenda (r:1 w:1)
	// Storage: Scheduler Lookup (r:1 w:1)
	fn cancel_queued(r: u32, ) -> Weight {
		(30_399_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((1_695_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	// Storage: Democracy ReferendumCount (r:1 w:0)
	// Storage: Democracy ReferendumInfoOf (r:1 w:0)
	// Storage: Democracy LowestUnbaked (r:1 w:0)
	// Storage: Democracy NextExternal (r:1 w:0)
	// Storage: Democracy PublicProps (r:1 w:0)
	// Storage: Democracy LastTabledWasExternal (r:1 w:0)
	fn on_initialize_base(r: u32, ) -> Weight {
		(7_195_000 as Weight)
			// Standard Error: 4_000
			.saturating_add((5_121_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
	}
	// Storage: Democracy ReferendumInfoOf (r:1 w:1)
	// Storage: Democracy VotingOf (r:3 w:3)
	// Storage: Balances Locks (r:1 w:1)
	fn delegate(r: u32, ) -> Weight {
		(55_542_000 as Weight)
			// Standard Error: 6_000
			.saturating_add((7_310_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes(4 as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	// Storage: Democracy ReferendumInfoOf (r:1 w:1)
	// Storage: Democracy VotingOf (r:2 w:2)
	fn undelegate(r: u32, ) -> Weight {
		(24_376_000 as Weight)
			// Standard Error: 6_000
			.saturating_add((7_301_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	// Storage: Democracy PublicProps (r:0 w:1)
	fn clear_public_proposals() -> Weight {
		(3_214_000 as Weight)
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: Democracy Preimages (r:1 w:1)
	fn note_preimage(b: u32, ) -> Weight {
		(45_495_000 as Weight)
			// Standard Error: 0
			.saturating_add((3_000 as Weight).saturating_mul(b as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: Democracy Preimages (r:1 w:1)
	fn note_imminent_preimage(b: u32, ) -> Weight {
		(29_427_000 as Weight)
			// Standard Error: 0
			.saturating_add((3_000 as Weight).saturating_mul(b as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: Democracy Preimages (r:1 w:1)
	// Storage: System Account (r:1 w:0)
	fn reap_preimage(b: u32, ) -> Weight {
		(40_908_000 as Weight)
			// Standard Error: 0
			.saturating_add((2_000 as Weight).saturating_mul(b as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	// Storage: Democracy VotingOf (r:1 w:1)
	fn unlock_remove(r: u32, ) -> Weight {
		(39_745_000 as Weight)
			// Standard Error: 0
			.saturating_add((45_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	// Storage: Democracy VotingOf (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn unlock_set(r: u32, ) -> Weight {
		(37_365_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((166_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	// Storage: Democracy VotingOf (r:1 w:1)
	// Storage: Democracy ReferendumInfoOf (r:1 w:1)
	fn remove_vote(r: u32, ) -> Weight {
		(21_066_000 as Weight)
			// Standard Error: 0
			.saturating_add((162_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	// Storage: Democracy VotingOf (r:1 w:1)
	// Storage: Democracy ReferendumInfoOf (r:1 w:1)
	fn remove_other_vote(r: u32, ) -> Weight {
		(21_045_000 as Weight)
			// Standard Error: 0
			.saturating_add((166_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	// Storage: Democracy PublicPropCount (r:1 w:1)
	// Storage: Democracy Blacklist (r:1 w:0)
	// Storage: Democracy PublicProps (r:1 w:1)
	// Storage: Democracy DepositOf (r:0 w:1)
	fn propose() -> Weight {
		(60_473_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	// Storage: Democracy DepositOf (r:1 w:1)
	fn second(s: u32, ) -> Weight {
		(40_878_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((157_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: Democracy VotingOf (r:1 w:1)
	// Storage: Democracy ReferendumInfoOf (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	fn vote_new(r: u32, ) -> Weight {
		(46_689_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((179_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	// Storage: Democracy VotingOf (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: Democracy ReferendumInfoOf (r:1 w:1)
	fn vote_existing(r: u32, ) -> Weight {
		(46_624_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((174_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	// Storage: Democracy Cancellations (r:1 w:1)
	// Storage: Democracy ReferendumInfoOf (r:1 w:1)
	fn emergency_cancel() -> Weight {
		(27_730_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	// Storage: Democracy ReferendumInfoOf (r:1 w:1)
	// Storage: Democracy PublicProps (r:1 w:1)
	// Storage: Democracy NextExternal (r:1 w:1)
	// Storage: Democracy Blacklist (r:0 w:1)
	// Storage: System Account (r:1 w:1)
	// Storage: Democracy DepositOf (r:1 w:1)
	fn blacklist(p: u32, ) -> Weight {
		(80_687_000 as Weight)
			// Standard Error: 4_000
			.saturating_add((495_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(6 as Weight))
	}
	// Storage: Democracy NextExternal (r:1 w:1)
	// Storage: Democracy Blacklist (r:1 w:0)
	fn external_propose(v: u32, ) -> Weight {
		(13_725_000 as Weight)
			// Standard Error: 0
			.saturating_add((91_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: Democracy NextExternal (r:0 w:1)
	fn external_propose_majority() -> Weight {
		(3_044_000 as Weight)
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: Democracy NextExternal (r:0 w:1)
	fn external_propose_default() -> Weight {
		(3_026_000 as Weight)
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: Democracy ReferendumInfoOf (r:0 w:1)
	// Storage: Democracy NextExternal (r:1 w:1)
	// Storage: Democracy ReferendumCount (r:1 w:1)
	fn fast_track() -> Weight {
		(28_457_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	// Storage: Democracy Blacklist (r:1 w:1)
	// Storage: Democracy NextExternal (r:1 w:1)
	fn veto_external(v: u32, ) -> Weight {
		(29_556_000 as Weight)
			// Standard Error: 0
			.saturating_add((134_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	// Storage: System Account (r:1 w:1)
	// Storage: Democracy PublicProps (r:1 w:1)
	// Storage: Democracy DepositOf (r:1 w:1)
	fn cancel_proposal(p: u32, ) -> Weight {
		(54_400_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((483_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	// Storage: Democracy ReferendumInfoOf (r:0 w:1)
	fn cancel_referendum() -> Weight {
		(17_561_000 as Weight)
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: Scheduler Agenda (r:1 w:1)
	// Storage: Scheduler Lookup (r:1 w:1)
	fn cancel_queued(r: u32, ) -> Weight {
		(30_399_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((1_695_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	// Storage: Democracy ReferendumCount (r:1 w:0)
	// Storage: Democracy ReferendumInfoOf (r:1 w:0)
	// Storage: Democracy LowestUnbaked (r:1 w:0)
	// Storage: Democracy NextExternal (r:1 w:0)
	// Storage: Democracy PublicProps (r:1 w:0)
	// Storage: Democracy LastTabledWasExternal (r:1 w:0)
	fn on_initialize_base(r: u32, ) -> Weight {
		(7_195_000 as Weight)
			// Standard Error: 4_000
			.saturating_add((5_121_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
	}
	// Storage: Democracy ReferendumInfoOf (r:1 w:1)
	// Storage: Democracy VotingOf (r:3 w:3)
	// Storage: Balances Locks (r:1 w:1)
	fn delegate(r: u32, ) -> Weight {
		(55_542_000 as Weight)
			// Standard Error: 6_000
			.saturating_add((7_310_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	// Storage: Democracy ReferendumInfoOf (r:1 w:1)
	// Storage: Democracy VotingOf (r:2 w:2)
	fn undelegate(r: u32, ) -> Weight {
		(24_376_000 as Weight)
			// Standard Error: 6_000
			.saturating_add((7_301_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	// Storage: Democracy PublicProps (r:0 w:1)
	fn clear_public_proposals() -> Weight {
		(3_214_000 as Weight)
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: Democracy Preimages (r:1 w:1)
	fn note_preimage(b: u32, ) -> Weight {
		(45_495_000 as Weight)
			// Standard Error: 0
			.saturating_add((3_000 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: Democracy Preimages (r:1 w:1)
	fn note_imminent_preimage(b: u32, ) -> Weight {
		(29_427_000 as Weight)
			// Standard Error: 0
			.saturating_add((3_000 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: Democracy Preimages (r:1 w:1)
	// Storage: System Account (r:1 w:0)
	fn reap_preimage(b: u32, ) -> Weight {
		(40_908_000 as Weight)
			// Standard Error: 0
			.saturating_add((2_000 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	// Storage: Democracy VotingOf (r:1 w:1)
	fn unlock_remove(r: u32, ) -> Weight {
		(39_745_000 as Weight)
			// Standard Error: 0
			.saturating_add((45_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	// Storage: Democracy VotingOf (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn unlock_set(r: u32, ) -> Weight {
		(37_365_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((166_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	// Storage: Democracy VotingOf (r:1 w:1)
	// Storage: Democracy ReferendumInfoOf (r:1 w:1)
	fn remove_vote(r: u32, ) -> Weight {
		(21_066_000 as Weight)
			// Standard Error: 0
			.saturating_add((162_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	// Storage: Democracy VotingOf (r:1 w:1)
	// Storage: Democracy ReferendumInfoOf (r:1 w:1)
	fn remove_other_vote(r: u32, ) -> Weight {
		(21_045_000 as Weight)
			// Standard Error: 0
			.saturating_add((166_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
}
