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

//! Autogenerated weights for `pallet_tx_pause`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2023-08-24, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `runner-aahe6cbd-project-145-concurrent-0`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("dev")`, DB CACHE: `1024`

// Executed Command:
// target/production/substrate-node
// benchmark
// pallet
// --steps=50
// --repeat=20
// --extrinsic=*
// --wasm-execution=compiled
// --heap-pages=4096
// --json-file=/builds/parity/mirrors/substrate/.git/.artifacts/bench.json
// --pallet=pallet_tx_pause
// --chain=dev
// --header=./HEADER-APACHE2
// --output=./frame/tx-pause/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(missing_docs)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use core::marker::PhantomData;

/// Weight functions needed for `pallet_tx_pause`.
pub trait WeightInfo {
	fn pause() -> Weight;
	fn unpause() -> Weight;
}

/// Weights for `pallet_tx_pause` using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: `TxPause::PausedCalls` (r:1 w:1)
	/// Proof: `TxPause::PausedCalls` (`max_values`: None, `max_size`: Some(532), added: 3007, mode: `MaxEncodedLen`)
	fn pause() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `3`
		//  Estimated: `3997`
		// Minimum execution time: 15_096_000 picoseconds.
		Weight::from_parts(15_437_000, 3997)
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: `TxPause::PausedCalls` (r:1 w:1)
	/// Proof: `TxPause::PausedCalls` (`max_values`: None, `max_size`: Some(532), added: 3007, mode: `MaxEncodedLen`)
	fn unpause() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `565`
		//  Estimated: `3997`
		// Minimum execution time: 21_546_000 picoseconds.
		Weight::from_parts(22_178_000, 3997)
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
}

// For backwards compatibility and tests.
impl WeightInfo for () {
	/// Storage: `TxPause::PausedCalls` (r:1 w:1)
	/// Proof: `TxPause::PausedCalls` (`max_values`: None, `max_size`: Some(532), added: 3007, mode: `MaxEncodedLen`)
	fn pause() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `3`
		//  Estimated: `3997`
		// Minimum execution time: 15_096_000 picoseconds.
		Weight::from_parts(15_437_000, 3997)
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: `TxPause::PausedCalls` (r:1 w:1)
	/// Proof: `TxPause::PausedCalls` (`max_values`: None, `max_size`: Some(532), added: 3007, mode: `MaxEncodedLen`)
	fn unpause() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `565`
		//  Estimated: `3997`
		// Minimum execution time: 21_546_000 picoseconds.
		Weight::from_parts(22_178_000, 3997)
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
}
