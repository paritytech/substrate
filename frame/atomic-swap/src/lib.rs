// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! # Atomic swap support pallet

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

mod tests;

use sp_std::prelude::*;
use sp_core::H256;
use frame_support::{
	dispatch::DispatchResult, decl_module, decl_storage, decl_event,
	traits::{Currency, ReservableCurrency},
};
use frame_system::{self as system, ensure_signed};
use codec::{Encode, Decode};
use sp_runtime::RuntimeDebug;

/// Pending atomic swap operation.
#[derive(Clone, RuntimeDebug, Eq, PartialEq, Encode, Decode)]
pub struct PendingSwap<AccountId, Balance, BlockNumber> {
	/// Source of the swap.
	pub source: AccountId,
	/// Balance value of the swap.
	pub balance: Balance,
	/// End block of the lock.
	pub end_block: BlockNumber,
}

/// Balance type from the pallet's point of view.
pub type BalanceFor<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

/// AccountId type from the pallet's point of view.
pub type AccountIdFor<T> = <T as frame_system::Trait>::AccountId;

/// BlockNumber type from the pallet's point of view.
pub type BlockNumberFor<T> = <T as frame_system::Trait>::BlockNumber;

/// PendingSwap type from the pallet's point of view.
pub type PendingSwapFor<T> = PendingSwap<AccountIdFor<T>, BalanceFor<T>, BlockNumberFor<T>>;

/// Atomic swap's pallet configuration trait.
pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
	/// The currency mechanism.
	type Currency: ReservableCurrency<Self::AccountId>;
}

decl_storage! {
	trait Store for Module<T: Trait> as Example {
		pub PendingSwaps: double_map
			hasher(twox_64_concat) T::AccountId, hasher(blake2_128_concat) H256
			=> Option<PendingSwapFor<T>>;
	}
}

decl_event!(
	/// Event of atomic swap pallet.
	pub enum Event<T> where
		Balance = BalanceFor<T>,
		AccountId = AccountIdFor<T>,
		PendingSwap = PendingSwapFor<T>,
	{
		/// Swap created.
		NewSwap(AccountId, H256, PendingSwap),
		/// Swap claimed.
		SwapClaimed(AccountId, H256, Balance),
		/// Swap cancelled.
		SwapCancelled(AccountId, H256, Balance),
	}
);

decl_module! {
	/// Module definition of atomic swap pallet.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;

		#[weight = 0]
		fn create_swap(
			origin,
			_target: AccountIdFor<T>,
			_hashed_proof: H256,
			_balance: BalanceFor<T>,
			_duration: BlockNumberFor<T>,
		) -> DispatchResult {
			ensure_signed(origin)?;
			unimplemented!()
		}

		#[weight = 0]
		fn claim_swap(
			origin,
			_hashed_proof: H256,
			_proof: Vec<u8>,
		) -> DispatchResult {
			ensure_signed(origin)?;
			unimplemented!()
		}

		#[weight = 0]
		fn cancel_swap(
			origin,
			_target: AccountIdFor<T>,
			_hashed_proof: H256,
		) -> DispatchResult {
			ensure_signed(origin)?;
			unimplemented!()
		}
	}
}
