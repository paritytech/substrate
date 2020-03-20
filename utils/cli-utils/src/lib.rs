// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

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
