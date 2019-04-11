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
use rstd::{prelude::*, result, mem};
use parity_codec::{HasCompact, Encode, Decode};
//use srml_support::{StorageValue, StorageMap, EnumerableStorageMap, dispatch::Result};
use srml_support::{decl_module, decl_event, decl_storage, ensure};
use srml_support::traits::{
	Currency, OnFreeBalanceZero, OnUnbalanced, Imbalance,
};
use primitives::Permill;
use primitives::sr25519; // hack to get an account id, remove when we have working get_block_author

// we will need the `BalanceOf` type for account balances
type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;

// Only used to inform the final Event if the issuance changed and in what direction
enum BurnOrMint {
	Burn,
	Mint,
	Null,
}

pub trait Trait: system::Trait {
	/// Currency
	pub type Currency: Currency<Self::AccountId>;

	/// Type that determines how many funds go to the block author.
	pub type ToBlockAuthor: BlockPayout<BalanceOf>;

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
		/// `BalanceOf` burned or minted.
		Distribution(AccountId, BalanceOf, BalanceOf, BurnOrMint),
	}
);

decl_storage! {
	trait Store for Module<T: Trait> as Fees {

		/// The cumulative fees for a block.
		///
		/// Fees will be added to this until the block is finalized, at which point
		/// one portion of the fees will go to the block author, one portion will
		/// go to the Treasury (if implemented), and the remainder will be burned.
		TotalBlockFees get(total_block_fees): map T::BlockNumber => T::BalanceOf;

		/// Cumulative new issuance for a block.
		///
		/// When new units are minted (e.g. for rewarding a validator), they will
		/// get added to this storage item. When a block is finalized, its issuance
		/// will be updated accordingly.
		TotalBlockMint get(block_new_issuance): map T::BlockNumber => T::BalanceOf;

		/// Proportion of fees that will go to the block author when a block is finalized.
		pub FeesToBlockAuthor get(fees_to_block_author) config(): Permill;
	}
}

decl_module! {
	pub struct Module<T::Trait> for enum Call where origin: T::Origin {

		fn deposit_event<T>() = default;

		/// Should be called when a block has been finalized. This function cannot fail.
		///
		/// Modules that take fees or mint rewards should pass those values into
		/// `take_fee` or `issue_units`, respectively. They will be accumulated
		/// into storage items that are private to this module.
		///
		/// When a block is finalized, this function will distribute fees as configured
		/// in the chain spec (some going to the block author, some being burned) and
		/// update the total issuance accounting for all mints and burns in a block.
		///
		/// TODO: Send some funds to the Treasury.
		fn on_finalize(n: T::BlockNumber) {

			// Should probably be handled somewhere else, like in config, so that this won't fail.
			ensure!(Self::fees_to_block_author() < Permill::from_percent(100),
				"You can't pay more than 100% of fees to the block author.");

			let mut total_fees = Self::total_block_fees();
			let fees_to_author = Self::fees_to_block_author().mul(total_fees);

			// Author
			let author = get_block_author(n);
			let author_balance = Self::free_balance(author);
			let would_create = author_balance.is_zero(); // Impossible, but safe
			let new_author_balance = author_balance.saturating_add(fees_to_author);

			if would_create && new_author_balance < T::Currency::minimum_balance() {
				// Normally would return an error, but this can't fail. Burn everything instead.
				// Issue some kind of warning?
				let fees_to_author = Zero::zero();
			}

			// Burn remaining fees
			let units2burn = total_fees.saturating_sub(fees_to_author);

			// Burn or mint tokens
			let units2mint = Self::block_new_issuance(n);

			if units2burn > units2mint {
				let imbalance = NegativeImbalance::new(units2burn.saturating_sub(units2mint));
				let bm = BurnOrMint::Burn;
			} else if units2mint > units2burn {
				let imbalance = PositiveImbalance::new(units2mint.saturating_sub(units2burn));
				let bm = BurnOrMint::Mint;
			} else {
				let imbalance = PositiveImbalance::new(Zero::zero());
				let bm = BurnOrMint::Null;
			}

			let imbalance_mag = imbalance.peek();

			// Send fees to author
			T::BlockPayout::pay_block_author(author, new_author_balance);

			// Update total issuance
			T::OnUnbalanced::on_imbalanced(imbalance);

			// Emit an event
			Self::deposit_event(RawEvent::Distribution(
				&author, // `AccountId` of block author
				fees_to_author,
				imbalance_mag,
				bm));
		}

	}
}

impl Module {
	/// Take a transaction fee. This will add it to the fees for the block.
	pub fn take_fee(n: T::BlockNumber, fee: T::BalanceOf) {
		let current_block_fees = Self::total_block_fees(n);
		let new_block_fees = current_block_fees + fee;
		<TotalBlockFees<T>>::insert(n, new_block_fees);
	}

	/// Account for new tokens minted, e.g. a reward
	pub fn issue_units(n: T::BlockNumber, units: T::BalanceOf) {
		let current_new_issuance = Self::block_new_issuance(n);
		let new_units_minted = current_new_issuance + units;
		<TotalBlockMint<T>>::insert(n, new_units_minted)
	}

	// https://github.com/paritytech/substrate/issues/2232
	// Currently a hack to get an AccountId into the dispatchable.
	// Will need to write a real function here.
	fn get_block_author(n: T::BlockNumber) -> T::AccountId {
		let s = "dummy author account";
		sr25519::Pair::from_string(&format!("//{}", s), None)
			.expect("static values are valid; qed")
			.public()
	}
}

pub trait OnUnbalanced<T::BalanceOf> {
	/// Handler for some imbalance. Infallible.
	fn on_unbalanced(amount: T::BalanceOf);
}

impl<Imbalance: Drop> OnUnbalanced<Imbalance> for () {
	fn on_unbalanced(amount: Imbalance) { drop(amount); }
}

pub trait BlockPayout<T::BalanceOf> {
	fn pay_block_author(author: T::AccountId, amount: T::BalanceOf);
}

impl BlockPayout {
	fn pay_block_author(author: T::AccountId, amount: T::BalanceOf) {
		T::Currency::set_free_balance(author, amount);
	}
}

/*

	Below here is copied in from the balances module to avoid the Subtrait/ElevatedTrait
	hack. Will need updating to integrate with other modules from here.

*/

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
