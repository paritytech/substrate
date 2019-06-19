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

#![warn(missing_docs, rust_2018_idioms)]

//! # Slashing interface
//!
//!	The Slashing interface specifies an API to punish entities that has put some
//!	`stake` in the system but has not discharged its duties properly
//!
//! ## Overview
//!
//! The Slashing interfaces specifies a generic API with functionality to specialize
//! any kind of misconduct with possibility to increase the punishment on concurrent misconducts.
//! It need to be implemented on top of some module that implements the `Balance` module.
//! In order to punish concurrent misconduct there something called `severity level` which may
//! be used to increase or decrease the punishment for a given misconduct.
//!
//! ### Terminology
//!
//! - Slash: The punishment of a staker by reducing its funds.
//! - Staking: The process of locking up funds for some time, placing them at risk of slashing
//!
//! ## Usage
//!
//! The following example show how to implement and use the `Slashing interface` on your custom module
//! with a `Unresponsive` misconduct which is slashed 0.00001% for isolated misconducts and increases
//! exponentially on concurrent misconducts.
//!
//!	### Example
//!
//! ```
//!	use srml_slashing::{Slashing, Misconduct, OnSlashing};
//!	use srml_support::traits::Currency;
//!	use rstd::{cmp, marker::PhantomData};
//!
//! pub trait Trait: system::Trait {
//!		type Currency: Currency<Self::AccountId>;
//! }
//!
//!	#[derive(Copy, Clone, Eq, PartialEq)]
//!	struct Unresponsive {
//!		severity: u64,
//!	}
//!
//!	impl Default for Unresponsive {
//!		fn default() -> Self {
//!			Self { severity: 100_000 }
//!		}
//!	}
//!
//!	impl Misconduct for Unresponsive {
//!		type Severity = u64;
//!
//!		fn on_misconduct(&mut self) {
//!			self.severity = cmp::max(1, self.severity / 2);
//!		}
//!
//!		fn on_signal(&mut self) {
//!			self.severity = cmp::min(100_000, self.severity * 2);
//!		}
//!
//!		fn severity(&self) -> Self::Severity {
//!			self.severity
//!		}
//!	}
//!
//! struct Balance<T>(PhantomData<T>);
//!
//! impl<T: Trait> OnSlashing<T> for Balance<T> {
//!
//!		fn on_slash(who: &T::AccountId, misconduct: &impl Misconduct) {
//!			// This doesn't compile, see `srml/staking/slash.rs` for a more elaborate example
//!			// let balance = T::Currency::free_balance(who);
//!			// let severity = misconduct.severity();
//!			// let slash = balance / severity;
//!			// T::Currency::on_slash(who, balance);
//!		}
//! }
//!
//!	struct SlashingWrapper<T>(PhantomData<T>);
//!
//!	impl<T: Trait> Slashing<T> for SlashingWrapper<T> {
//!		type Slash = Balance<T>;
//!
//!		fn slash(who: &T::AccountId, misconduct: &mut impl Misconduct) {
//!			Self::Slash::on_slash(&who, misconduct);
//!			misconduct.on_misconduct();
//!		}
//!
//!		fn on_signal(misconduct: &mut impl Misconduct) {
//!			misconduct.on_signal();
//!		}
//!	}
//!
//! fn main() {
//!		let misconduct = Unresponsive::default();
//!		let who = 0;
//!		// MyModule is type that implements `Trait`
//!		// SlashingWrapper::<MyModule>::slash(&who, &mut misconduct);
//! }
//! ```

use parity_codec::Codec;
use primitives::traits::{SimpleArithmetic, MaybeSerializeDebug};

/// Pre-defined misconduct types
pub mod misconduct;

/// Estimates severity level based on misconduct
pub trait Misconduct: {
	/// Severity, must be able to encode in `u128` otherwise into() will be lossy
	// TODO(niklasad1): better way than the hack?!
	type Severity: SimpleArithmetic + Codec + Copy + MaybeSerializeDebug + Default + Into<u128>;

	/// Increase severity level on misconduct.
	fn on_misconduct(&mut self);
	/// Decrease severity level after a certain point up to the implementor to determine when.
	fn on_signal(&mut self);
	/// Get the severity level
	fn severity(&self) -> Self::Severity;
}

/// Slashing interface
pub trait OnSlashing<AccountId> {
	/// Slash validator `who` based on severity_level `severity`
	fn on_slash(who: &AccountId, misconduct: &impl Misconduct);
}

/// Slashing wrapper interface on top of `OnSlashing`
pub trait Slashing<AccountId> {
	/// Specify which `OnSlashing` implementation to use
	type Slash: OnSlashing<AccountId>;

	/// Slash the given account `who`
	fn slash(who: &AccountId, misconduct: &mut impl Misconduct);

	/// Decrease severity level after a certain point up to the implementer to determine when.
	fn on_signal(misconduct: &mut impl Misconduct);
}
