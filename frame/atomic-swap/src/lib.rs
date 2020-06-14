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
use sp_io::hashing::blake2_256;
use frame_support::{
	decl_module, decl_storage, decl_event, decl_error, ensure,
	traits::{Currency, ReservableCurrency, BalanceStatus},
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

/// Hashed proof type.
pub type HashedProof = [u8; 32];

/// Atomic swap's pallet configuration trait.
pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
	/// The currency mechanism.
	type Currency: ReservableCurrency<Self::AccountId>;
}

decl_storage! {
	trait Store for Module<T: Trait> as AtomicSwap {
		pub PendingSwaps: double_map
			hasher(twox_64_concat) T::AccountId, hasher(blake2_128_concat) HashedProof
			=> Option<PendingSwapFor<T>>;
	}
}

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// Swap already exists.
		AlreadyExist,
		/// Swap proof is invalid.
		InvalidProof,
		/// Swap does not exist.
		NotExist,
		/// Duration has not yet passed for the swap to be cancelled.
		DurationNotPassed,
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
		NewSwap(AccountId, HashedProof, PendingSwap),
		/// Swap claimed.
		SwapClaimed(AccountId, HashedProof, Balance),
		/// Swap cancelled.
		SwapCancelled(AccountId, HashedProof, Balance),
	}
);

decl_module! {
	/// Module definition of atomic swap pallet.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		fn deposit_event() = default;

		#[weight = 0]
		fn create_swap(
			origin,
			target: AccountIdFor<T>,
			hashed_proof: HashedProof,
			balance: BalanceFor<T>,
			duration: BlockNumberFor<T>,
		) {
			let source = ensure_signed(origin)?;
			ensure!(
				PendingSwaps::<T>::get(&target, hashed_proof).is_none(),
				Error::<T>::AlreadyExist
			);

			T::Currency::reserve(&source, balance)?;

			let swap = PendingSwap {
				source,
				balance,
				end_block: frame_system::Module::<T>::block_number() + duration,
			};
			PendingSwaps::<T>::insert(target, hashed_proof, swap);
		}

		#[weight = 0]
		fn claim_swap(
			origin,
			proof: Vec<u8>,
		) {
			let target = ensure_signed(origin)?;
			let hashed_proof = blake2_256(&proof);

			let swap = PendingSwaps::<T>::get(&target, hashed_proof)
				.ok_or(Error::<T>::InvalidProof)?;
			T::Currency::repatriate_reserved(
				&swap.source,
				&target,
				swap.balance,
				BalanceStatus::Free,
			)?;
			PendingSwaps::<T>::remove(target, hashed_proof);
		}

		#[weight = 0]
		fn cancel_swap(
			origin,
			target: AccountIdFor<T>,
			hashed_proof: HashedProof,
		) {
			ensure_signed(origin)?;

			let swap = PendingSwaps::<T>::get(&target, hashed_proof)
				.ok_or(Error::<T>::NotExist)?;
			ensure!(
				frame_system::Module::<T>::block_number() >= swap.end_block,
				Error::<T>::DurationNotPassed,
			);

			T::Currency::unreserve(
				&swap.source,
				swap.balance,
			);
			PendingSwaps::<T>::remove(&target, hashed_proof);
		}
	}
}
