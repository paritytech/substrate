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

//! # StakeTracker
//!
//! FRAME stake tracker pallet
//!
//! ## Overview
//!
//! The stake-tracker pallet is responsible to listen to staking events and forward those events to
//! one or multiple types (e.g. pallets) that implement the [`sp_staking::OnStakingUpdate`] trait.
//!
//! ### Example
//!
//! //TODO
//!
//! ## Pallet API
//!
//! (Reminder: inside the [`pallet`] module, a template that leads the reader to the relevant items
//! is auto-generated. There is no need to repeat things like "See Config trait for ...", which are
//! generated inside [`pallet`] here anyways. You can use the below line as-is:)
//!
//! See the [`pallet`] module for more information about the interfaces this pallet exposes,
//! including its configuration trait, dispatchables, storage items, events and errors.
//!
//! (The audience of this is those who want to know how this pallet works, to the extent of being
//! able to build something on top of it, like a DApp or another pallet.)
//!
//! This section can most often be left as-is.
//!
//! ## Low Level / Implementation Details
//!
//! (The format of this section is up to you, but we suggest the Design-oriented approach that
//! follows.)
//!
//! (The audience of this would be your future self, or anyone who wants to gain a deep
//! understanding of how the pallet works so that they can eventually propose optimizations to it.)
//!
//! ### Design Goals (optional)
//!
//! (Describe your goals with the pallet design.)

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

use frame_election_provider_support::SortedListProvider;
use frame_support::traits::Currency;
use sp_staking::StakingInterface;

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

/// The balance type of this pallet.
pub type BalanceOf<T> = <<T as Config>::Staking as StakingInterface>::Balance;

#[frame_support::pallet]
pub mod pallet {
	use crate::*;
	use frame_election_provider_support::VoteWeight;
	use frame_support::pallet_prelude::*;

	/// The current storage version.
	const STORAGE_VERSION: StorageVersion = StorageVersion::new(0);

	#[pallet::pallet]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type Currency: Currency<Self::AccountId, Balance = BalanceOf<Self>>;

		type Staking: StakingInterface<AccountId = Self::AccountId>;

		type VoterList: SortedListProvider<Self::AccountId, Score = VoteWeight>;
		type TargetList: SortedListProvider<Self::AccountId, Score = BalanceOf<Self>>;
	}

	impl<T: Config> Pallet<T> {}
}
