// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! # Fees Module

// https://github.com/paritytech/substrate/issues/2052

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use runtime_io::with_storage;
use rstd::{prelude::*, result};
use parity_codec::{HasCompact, Encode, Decode};
//use srml_support::{StorageValue, StorageMap, EnumerableStorageMap, dispatch::Result};
use srml_support::{decl_module, decl_event, decl_storage, ensure};
use srml_support::traits::{
	Currency, OnFreeBalanceZero, OnUnbalanced, Imbalance,
};
use primitives::Permill;

// we will need the `BalanceOf` type for account balances
type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;

pub trait Trait: 'static + system::Trait {
	/// Currency
	pub type Currency: Currency<Self::AccountId>;

	/// Type that determines how many funds go to the block author.
	pub type ToBlockAuthor: Fn() -> Permill;

	/// Type that determines how many funds go to the treasury.
	pub type ToTreasury: Fn() -> Permill;
}

decl_event!(
	pub enum Event<T> where AccountId = <T as system::Trait>::AccountId {

		/// The block has been finalized and fees distributed. `BalanceOf` to `AccountId` (block author),
		/// `BalanceOf` to the Treasury, and `BalanceOf` burned.
		Distribution(AccountId, BalanceOf, BalanceOf, BalanceOf),
	}
);

decl_storage! {
	trait Store for Module<T: Trait> as Fees {

		/// The cumulative fees for a block.
		///
		/// Fees will be added to this until the block is finalized, at which point
		/// one portion of the fees will go to the block author, one portion will
		/// go to the Treasury (if implemented), and the remainder will be burned.
		TotalBlockFees get(total_block_fees): T::BalanceOf;
	}
}

decl_module! {
	pub struct Module<T::Trait> for enum Call where origin: T::Origin {

		fn deposit_event<T>() = default;

	}
}

impl<T::Trait> Module<T> {

	/// Should be called when a block has been finalized. This function cannot fail.
	///
	/// Needs to:
	/// - Ensure that (% to author) + (% to treasury) <= 100
	/// - Transfer funds to author
	/// - Transfer funds to treasury
	/// - Burn remainder and update `TotalIssuance`
	/// - Emit an event
	pub fn distribute_fees_on_finalize(origin) {

		match get_total_fees(n) {
			Some(f) => let total_fees = f,
			_ => let total_fees = Zero::zero(),
		}

		if let Some(get_total_fees(n)) {
			total_fees = get_total_fees(n);
		}

		Self::deposit_event(RawEvent::Distribution(&1,1,2,3));
	}

	// Go through all transactions in a block and get cumulative fees.
	//
	// Is it possible to do this without a loop?
	fn get_total_fees(n: T::BlockNumber) -> Option<T::BalanceOf> {
	}
}

impl<T::Trait> ToBlockAuthor<T> {

	fn transfer_to_author(author: T::AccountId, amount: T::BalanceOf) {

	}
}

impl<T::Trait> ToTreasury<T> {

	fn transfer_to_treasury(amount: T::BalanceOf) {

	}

}
