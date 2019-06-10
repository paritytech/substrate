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

#![deny(missing_docs, rust_2018_idioms)]

//! Slashing interface
//!
//! That gives functionality to specialize slashing and misconduct for a given type
//! In order to customize severity level and misconduct fees.
//!

mod types;
#[cfg(test)]
mod tests;

pub use types::Unresponsive;

use parity_codec::Codec;
use primitives::traits::{SimpleArithmetic, MaybeSerializeDebug};
use srml_support::traits::Currency;

type BalanceOf<T> = <<T as OnSlashing>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;
type NegativeImbalanceOf<T> =
	<<T as OnSlashing>::Currency as Currency<<T as system::Trait>::AccountId>>::NegativeImbalance;
type Severity<T> = <<T as OnSlashing>::Misconduct as Misconduct>::Severity;

/// Estimates severity level based on misconduct
pub trait Misconduct {
	/// Severity
	type Severity: SimpleArithmetic + Codec + Copy + MaybeSerializeDebug + Default;
	/// Increase severity level on misconduct.
	fn on_misconduct(&mut self);
	/// Decrease severity level after a certain point up to the implementor to determine when.
	fn on_signal(&mut self);
	/// Get the severity level
	fn severity(&self) -> Self::Severity;
}

/// Calculates the amount to be slashed
pub trait Slashing: OnSlashing {
	/// Calculates the amount to be slashed
	fn amount(free_balance: BalanceOf<Self>, severity: Severity<Self>) -> BalanceOf<Self>;
}

/// Wrapper interface sits between `Balance` and `Slashing`
pub trait OnSlashing: system::Trait {
	/// Balance
	type Currency: Currency<Self::AccountId>;

	/// Slashing
	type Slashing: Slashing;

	/// Misconduct
	type Misconduct: Misconduct;

	/// Slash the given account `who`
	//
	// Note, `free_balance` could be fetched using `Currency::free_balance()`
	// but it is an explicit parameter to make it easier to test.
	fn slash(
		who: &Self::AccountId,
		free_balance: BalanceOf<Self>,
		misconduct: &mut Self::Misconduct
	) -> (NegativeImbalanceOf<Self>, BalanceOf<Self>);

	/// Decrease severity level after a certain point up to the implementor to determine when.
	fn on_signal(misconduct: &mut Self::Misconduct);
}
