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

pub enum Priority {

	/// Pay fees to the block author before the Treasury.
	Author,

	/// Pay fees to the Treasury before the block author.
	Treasury,
}

impl Default for Priority {
	fn default() -> Self {
		Priority::Treasury
	}
}

pub trait Trait: system::Trait {
	/// Currency
	pub type Currency: Currency<Self::AccountId>;

	/// Type that determines how many funds go to the block author.
	pub type ToBlockAuthor: Fn() -> Permill;

	/// Type that determines how many funds go to the Treasury.
	pub type ToTreasury: Fn() -> Permill;

	/// Handler for the unbalanced reduction when taking transaction fees.
	type TransactionPayment: OnUnbalanced<NegativeImbalance<Self>>;

	/// Handler for the unbalanced reduction when taking fees associated with balance
	/// transfer (which may also include account creation).
	type TransferPayment: OnUnbalanced<NegativeImbalance<Self>>;

	/// Handler for the unbalanced reduction when removing a dust account.
	type DustRemoval: OnUnbalanced<NegativeImbalance<Self>>;
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

		/// Proportion of fees that will go to the block author when a block is finalized.
		pub FeesToBlockAuthor get(fees_to_block_author) config(): Permill;

		/// Proportion of fees that will go to the Treasury when a block is finalized.
		/// Note that the Treasury may burn some portion of funds it receives.
		pub FeesToTreasury get(fees_to_treasury) config(): Permill;

		/// Who gets paid first. Only relevant if you configure your
		/// (`FeesToBlockAuthor` + `FeesToTreasury`) > 100%. `Priority` will keep the selected
		/// fees the same and reduce the fees of the other so that exactly 100% of the fees
		/// are handled.
		pub Priority get(priority) config(): Priority = Priority::default();
	}
}

decl_module! {
	pub struct Module<T::Trait> for enum Call where origin: T::Origin {

		fn deposit_event<T>() = default;

		/// Should be called when a block has been finalized. This function cannot fail.
		///
		/// Needs to:
		/// - Ensure that (% to author) + (% to Treasury) <= 100
		/// - Transfer funds to author
		/// - Transfer funds to Treasury
		/// - Burn remainder and update `TotalIssuance`
		/// - Emit an event
		fn on_finalize() {

			ensure!(Self::fees_to_block_author() < Permill::from_percent(100),
				"You can't pay more than 100% of fees to the block author.");

			ensure!(Self::fees_to_treasury() < Permill::from_percent(100),
				"You can't pay more than 100% of fees to the Treasury.");

			if Self::fees_to_block_author() + Self::fees_to_treasury() > Permill::from_percent(100) {
				match priority {
					// Shouldn't need `saturating_sub` here as already ensured that the second term is <100, but being safe
					Priority::Author => {
						<FeesToTreasury<T>>::set(Permill::from_percent(100)
							.saturating_sub(Self::fees_to_block_author()));
					},
					Priority::Treasury => {
						<FeesToBlockAuthor<T>>::set(Permill::from_percent(100)
							.saturating_sub(Self::fees_to_treasury()));
					},
				}
			}

			// Transfer fees to author and Treasury
			let mut total_fees = Self::total_block_fees();

			// TODO: has Mul impl
			let total_fees_to_author = total_fees * Self::fees_to_block_author() / 1_000_000;
			let total_fees_to_treasury = total_fees * Self::fees_to_treasury() / 1_000_000;

			// Burn remaining fees
			let fees_to_burn = total_fees
								.saturating_sub(total_fees_to_author)
								.saturating_sub(total_fees_to_treasury);

			T::OnUnbalanced::on_imbalanced(NegativeImbalance::new(fees_to_burn));

			// Emit an event
			Self::deposit_event(RawEvent::Distribution(&1, // `AccountId` of block author
													total_fees_to_author,
													total_fees_to_treasury,
													fees_to_burn));
		}

	}
}

/// Opaque, move-only struct with private fields that serves as a token denoting that
/// funds have been created without any equal and opposite accounting.
#[must_use]
pub struct PositiveImbalance<T: Trait<I>, I: Instance=DefaultInstance>(T::BalanceOf);

impl<T: Trait<I>, I: Instance> PositiveImbalance<T, I> {
	/// Create a new positive imbalance from a balance.
	pub fn new(amount: T::BalanceOf) -> Self {
		PositiveImbalance(amount)
	}
}

/// Opaque, move-only struct with private fields that serves as a token denoting that
/// funds have been destroyed without any equal and opposite accounting.
#[must_use]
pub struct NegativeImbalance<T: Trait<I>, I: Instance=DefaultInstance>(T::BalanceOf);

impl<T: Trait<I>, I: Instance> NegativeImbalance<T, I> {
	/// Create a new negative imbalance from a balance.
	pub fn new(amount: T::BalanceOf) -> Self {
		NegativeImbalance(amount)
	}
}

impl<T: Trait<I>, I: Instance> Imbalance<T::BalanceOf> for PositiveImbalance<T, I> {
	type Opposite = NegativeImbalance<T, I>;

	fn zero() -> Self {
		Self(Zero::zero())
	}

	fn drop_zero(self) -> result::Result<(), Self> {
		if self.0.is_zero() {
			Ok(())
		} else {
			Err(self)
		}
	}

	fn split(self, amount: T::BalanceOf) -> (Self, Self) {
		let first = self.0.min(amount);
		let second = self.0 - first;

		mem::forget(self);
		(Self(first), Self(second))
	}

	fn merge(mut self, other: Self) -> Self {
		self.0 = self.0.saturating_add(other.0);
		mem::forget(other);

		self
	}

	fn subsume(&mut self, other: Self) {
		self.0 = self.0.saturating_add(other.0);
		mem::forget(other);
	}

	fn offset(self, other: Self::Opposite) -> result::Result<Self, Self::Opposite> {
		let (a, b) = (self.0, other.0);
		mem::forget((self, other));

		if a >= b {
			Ok(Self(a - b))
		} else {
			Err(NegativeImbalance::new(b - a))
		}
	}

	fn peek(&self) -> T::BalanceOf {
		self.0.clone()
	}
}

impl<T: Trait<I>, I: Instance> Imbalance<T::BalanceOf> for NegativeImbalance<T, I> {
	type Opposite = PositiveImbalance<T, I>;

	fn zero() -> Self {
		Self(Zero::zero())
	}

	fn drop_zero(self) -> result::Result<(), Self> {
		if self.0.is_zero() {
			Ok(())
		} else {
			Err(self)
		}
	}

	fn split(self, amount: T::BalanceOf) -> (Self, Self) {
		let first = self.0.min(amount);
		let second = self.0 - first;

		mem::forget(self);
		(Self(first), Self(second))
	}

	fn merge(mut self, other: Self) -> Self {
		self.0 = self.0.saturating_add(other.0);
		mem::forget(other);

		self
	}

	fn subsume(&mut self, other: Self) {
		self.0 = self.0.saturating_add(other.0);
		mem::forget(other);
	}

	fn offset(self, other: Self::Opposite) -> result::Result<Self, Self::Opposite> {
		let (a, b) = (self.0, other.0);
		mem::forget((self, other));

		if a >= b {
			Ok(Self(a - b))
		} else {
			Err(PositiveImbalance::new(b - a))
		}
	}

	fn peek(&self) -> T::BalanceOf {
		self.0.clone()
	}
}

impl<T: Trait<I>, I: Instance> Drop for PositiveImbalance<T, I> {
	/// Basic drop handler will just square up the total issuance.
	fn drop(&mut self) {
		<balances::TotalIssuance<T, I>>::mutate(
			|v| *v = v.saturating_add(self.0)
		);
	}
}

impl<T: Trait<I>, I: Instance> Drop for NegativeImbalance<T, I> {
	/// Basic drop handler will just square up the total issuance.
	fn drop(&mut self) {
		<balances::TotalIssuance<T, I>>::mutate(
			|v| *v = v.saturating_sub(self.0)
		);
	}
}

impl<T: Trait<I>, I: Instance> Clone for PositiveImbalance<T, I> {
	fn clone(&self) -> Self { unimplemented!() }
}

impl<T: Trait<I>, I: Instance> PartialEq for PositiveImbalance<T, I> {
	fn eq(&self, _: &Self) -> bool { unimplemented!() }
}

impl<T: Trait<I>, I: Instance> Clone for NegativeImbalance<T, I> {
	fn clone(&self) -> Self { unimplemented!() }
}

impl<T: Trait<I>, I: Instance> PartialEq for NegativeImbalance<T, I> {
	fn eq(&self, _: &Self) -> bool { unimplemented!() }
}

impl<T::Trait> OnUnbalanced<T> {

	fn on_unbalanced(amount: T::BalanceOf) { drop(amount); }
}

//
pub trait OnUnbalanced<T::BalanceOf> {
	/// Handler for some imbalance. Infallible.
	fn on_unbalanced(amount: T::BalanceOf);
}

impl<Imbalance: Drop> OnUnbalanced<Imbalance> for () {
	fn on_unbalanced(amount: Imbalance) { drop(amount); }
}
