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

//! Autogenerated weights for pallet_transaction_storage
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2021-08-07, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 128

// Executed Command:
// target/release/substrate
// benchmark
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_transaction_storage
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/transaction-storage/src/weights.rs
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
	// Storage: TransactionStorage MaxTransactionSize (r:1 w:0)
	// Storage: TransactionStorage ByteFee (r:1 w:0)
	// Storage: TransactionStorage EntryFee (r:1 w:0)
	// Storage: unknown [0x3a65787472696e7369635f696e646578] (r:1 w:0)
	// Storage: TransactionStorage BlockTransactions (r:1 w:1)
	// Storage: TransactionStorage MaxBlockTransactions (r:1 w:0)
	fn store(l: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 0
			.saturating_add((8_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(T::DbWeight::get().reads(6 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: TransactionStorage Transactions (r:1 w:0)
	// Storage: TransactionStorage ByteFee (r:1 w:0)
	// Storage: TransactionStorage EntryFee (r:1 w:0)
	// Storage: unknown [0x3a65787472696e7369635f696e646578] (r:1 w:0)
	// Storage: TransactionStorage BlockTransactions (r:1 w:1)
	// Storage: TransactionStorage MaxBlockTransactions (r:1 w:0)
	fn renew() -> Weight {
		(67_532_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(6 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: TransactionStorage ProofChecked (r:1 w:1)
	// Storage: TransactionStorage StoragePeriod (r:1 w:0)
	// Storage: TransactionStorage ChunkCount (r:1 w:0)
	// Storage: System ParentHash (r:1 w:0)
	// Storage: TransactionStorage Transactions (r:1 w:0)
	fn check_proof_max() -> Weight {
		(182_886_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	// Storage: TransactionStorage MaxTransactionSize (r:1 w:0)
	// Storage: TransactionStorage ByteFee (r:1 w:0)
	// Storage: TransactionStorage EntryFee (r:1 w:0)
	// Storage: unknown [0x3a65787472696e7369635f696e646578] (r:1 w:0)
	// Storage: TransactionStorage BlockTransactions (r:1 w:1)
	// Storage: TransactionStorage MaxBlockTransactions (r:1 w:0)
	fn store(l: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 0
			.saturating_add((8_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(RocksDbWeight::get().reads(6 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: TransactionStorage Transactions (r:1 w:0)
	// Storage: TransactionStorage ByteFee (r:1 w:0)
	// Storage: TransactionStorage EntryFee (r:1 w:0)
	// Storage: unknown [0x3a65787472696e7369635f696e646578] (r:1 w:0)
	// Storage: TransactionStorage BlockTransactions (r:1 w:1)
	// Storage: TransactionStorage MaxBlockTransactions (r:1 w:0)
	fn renew() -> Weight {
		(67_532_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(6 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: TransactionStorage ProofChecked (r:1 w:1)
	// Storage: TransactionStorage StoragePeriod (r:1 w:0)
	// Storage: TransactionStorage ChunkCount (r:1 w:0)
	// Storage: System ParentHash (r:1 w:0)
	// Storage: TransactionStorage Transactions (r:1 w:0)
	fn check_proof_max() -> Weight {
		(182_886_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
}
