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

//! FRAME utilities
//!
#![cfg_attr(not(feature = "std"), no_std)]

use sp_runtime::traits::{StaticLookup, SignedExtension};
pub use pallet_balances::Call as BalancesCall;
use sp_runtime::generic::Era;

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

///
/// Strongly typed interface for the `SignedExtensions` that should be included in extrinsics
/// for them to valid for your runtime.
///
/// ```rust,ignore
/// use runtime::{Runtime, SignedExtra};
/// use frame_utils::IndexFor;
/// use sp_runtime::generic;
///
/// impl RuntimeAdapter for Runtime {
///     type Extra = SignedExtra;
///
///     fn construct_extras(index: IndexFor<Self>) -> Self::Extra {
///         // take the biggest period possible.
///         let period = BlockHashCount::get()
///             .checked_next_power_of_two()
///             .map(|c| c / 2)
///             .unwrap_or(2) as u64;
///         let current_block = System::block_number()
///             .saturated_into::<u64>()
///             // The `System::block_number` is initialized with `n+1`,
///             // so the actual block number is `n`.
///             .saturating_sub(1);
///
///         (
///             frame_system::CheckSpecVersion::new(),
///             frame_system::CheckTxVersion::new(),
///             frame_system::CheckGenesis::new(),
///             frame_system::CheckEra::from(generic::Era::mortal(period, current_block)),
///             frame_system::CheckNonce::from(index),
///             frame_system::CheckWeight::new(),
///         )
///     }
/// }
///
/// ```
///
pub trait SignedExtensionProvider: frame_system::Trait {
    /// Concrete SignedExtension type.
    type Extra: SignedExtension;

    /// construct extras and optionally additional_signed data for inclusion in extrinsics.
    fn construct_extras(nonce: IndexFor<Self>, era: Era, prior_block_hash: Option<Self::Hash>) -> (
        Self::Extra,
        Option<<Self::Extra as SignedExtension>::AdditionalSigned>
    );
}

