// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! Utilities for cli.
#![cfg_attr(not(feature = "std"), no_std)]

use sp_runtime::traits::{StaticLookup, SignedExtension};
pub use pallet_balances::Call as BalancesCall;

/// AccountIndex type for Runtime
pub type IndexFor<R> = <R as frame_system::Trait>::Index;
/// Balance type
pub type BalanceFor<R> = <R as pallet_balances::Trait>::Balance;
/// Call type for Runtime
pub type CallFor<R> = <R as frame_system::Trait>::Call;
/// Address type for runtime.
pub type AddressFor<R> = <<R as frame_system::Trait>::Lookup as StaticLookup>::Source;
/// Hash for runtime.
pub type HashFor<R> = <R as frame_system::Trait>::Hash;
/// AccountId type for runtime.
pub type AccountIdFor<R> = <R as frame_system::Trait>::AccountId;

/// Runtime adapter for signing utilities
pub trait RuntimeAdapter: frame_system::Trait + pallet_balances::Trait {
    /// extras
    type Extra: SignedExtension;

    /// build extras for inclusion in extrinsics
    fn build_extra(index: IndexFor<Self>) -> Self::Extra;
}

