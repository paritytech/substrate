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

//! Autogenerated weights for pallet_transaction_storage
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2022-11-07, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! HOSTNAME: `bm2`, CPU: `Intel(R) Core(TM) i7-7700K CPU @ 4.20GHz`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// ./target/production/substrate
// benchmark
// pallet
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_transaction_storage
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/transaction-storage/src/weights.rs
// --header=./HEADER-APACHE2
// --template=./.maintain/frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_transaction_storage.
pub trait WeightInfo {
	fn store(l: u32, ) -> Weight;
	fn renew() -> Weight;
	fn check_proof_max() -> Weight;
}

/// Weights for pallet_transaction_storage using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	// Storage: TransactionStorage ByteFee (r:1 w:0)
	// Storage: TransactionStorage EntryFee (r:1 w:0)
	// Storage: unknown [0x3a65787472696e7369635f696e646578] (r:1 w:0)
	// Storage: TransactionStorage BlockTransactions (r:1 w:1)
	/// The range of component `l` is `[1, 8388608]`.
	fn store(l: u32, ) -> Weight {
		// Minimum execution time: 46_730 nanoseconds.
		Weight::from_ref_time(46_922_000 as u64)
			// Standard Error: 2
			.saturating_add(Weight::from_ref_time(5_601 as u64).saturating_mul(l as u64))
			.saturating_add(T::DbWeight::get().reads(4 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: TransactionStorage Transactions (r:1 w:0)
	// Storage: unknown [0x3a65787472696e7369635f696e646578] (r:1 w:0)
	// Storage: TransactionStorage ByteFee (r:1 w:0)
	// Storage: TransactionStorage EntryFee (r:1 w:0)
	// Storage: TransactionStorage BlockTransactions (r:1 w:1)
	fn renew() -> Weight {
		// Minimum execution time: 56_802 nanoseconds.
		Weight::from_ref_time(58_670_000 as u64)
			.saturating_add(T::DbWeight::get().reads(5 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: TransactionStorage ProofChecked (r:1 w:1)
	// Storage: TransactionStorage StoragePeriod (r:1 w:0)
	// Storage: TransactionStorage ChunkCount (r:1 w:0)
	// Storage: System ParentHash (r:1 w:0)
	// Storage: TransactionStorage Transactions (r:1 w:0)
	fn check_proof_max() -> Weight {
		// Minimum execution time: 74_016 nanoseconds.
		Weight::from_ref_time(94_111_000 as u64)
			.saturating_add(T::DbWeight::get().reads(5 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	// Storage: TransactionStorage ByteFee (r:1 w:0)
	// Storage: TransactionStorage EntryFee (r:1 w:0)
	// Storage: unknown [0x3a65787472696e7369635f696e646578] (r:1 w:0)
	// Storage: TransactionStorage BlockTransactions (r:1 w:1)
	/// The range of component `l` is `[1, 8388608]`.
	fn store(l: u32, ) -> Weight {
		// Minimum execution time: 46_730 nanoseconds.
		Weight::from_ref_time(46_922_000 as u64)
			// Standard Error: 2
			.saturating_add(Weight::from_ref_time(5_601 as u64).saturating_mul(l as u64))
			.saturating_add(RocksDbWeight::get().reads(4 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	// Storage: TransactionStorage Transactions (r:1 w:0)
	// Storage: unknown [0x3a65787472696e7369635f696e646578] (r:1 w:0)
	// Storage: TransactionStorage ByteFee (r:1 w:0)
	// Storage: TransactionStorage EntryFee (r:1 w:0)
	// Storage: TransactionStorage BlockTransactions (r:1 w:1)
	fn renew() -> Weight {
		// Minimum execution time: 56_802 nanoseconds.
		Weight::from_ref_time(58_670_000 as u64)
			.saturating_add(RocksDbWeight::get().reads(5 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	// Storage: TransactionStorage ProofChecked (r:1 w:1)
	// Storage: TransactionStorage StoragePeriod (r:1 w:0)
	// Storage: TransactionStorage ChunkCount (r:1 w:0)
	// Storage: System ParentHash (r:1 w:0)
	// Storage: TransactionStorage Transactions (r:1 w:0)
	fn check_proof_max() -> Weight {
		// Minimum execution time: 74_016 nanoseconds.
		Weight::from_ref_time(94_111_000 as u64)
			.saturating_add(RocksDbWeight::get().reads(5 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
}
