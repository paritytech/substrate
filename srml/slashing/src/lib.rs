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
//!
//! ### Terminology
//!
//! - Slash: The punishment of a staker by reducing its funds.
//! - Staking: The process of locking up funds for some time, placing them at risk of slashing
//!
//! ## Usage
//!
//! The following example show how to implement and use the `Slashing interface` on your custom module
//! with a `Unresponsive` misconduct.
//!
//!	### Example
//!
//! ```
//!	use srml_slashing::{CheckpointMisconduct, ContinuousMisconduct, Fraction, Misconduct, OnSlashing, Slashing};
//!	use srml_support::traits::Currency;
//!	use rstd::{cmp, marker::PhantomData};
//!
//! pub trait Trait: system::Trait {
//!		type Currency: Currency<Self::AccountId>;
//! }
//!
//!	struct Unresponsive;
//!
//!	impl Misconduct for Unresponsive {
//!		type Severity = u64;
//!	}
//!
//! impl CheckpointMisconduct for Unresponsive {
//!		fn severity(&self, k: u64, n: u64) -> Fraction<Self::Severity> {
//!			let denominator = 20 * n;
//!			let numerator = 3*k - 3;
//!
//!			if numerator / n > 1 {
//!				Fraction::new(1, 1)
//!			} else {
//!				Fraction::new(denominator, numerator)
//!			}
//!		}
//!	}
//!
//! struct Balance<T>(PhantomData<T>);
//!
//! impl<T: Trait> OnSlashing<T::AccountId> for Balance<T> {
//!
//!		fn on_slash(who: &T::AccountId, severity: Fraction<u64>) {
//!			// This doesn't compile, see `srml/staking/slash.rs` for a more elaborate example
//!			// let balance = T::Currency::free_balance(who);
//!			// let slash = balance / severity;
//!			// T::Currency::on_slash(who, balance);
//!		}
//! }
//!
//!	struct SlashingWrapper<T>(PhantomData<T>);
//!
//!	impl<T: Trait> Slashing<T::AccountId> for SlashingWrapper<T> {
//!		type Slash = Balance<T>;
//!
//!		fn slash(who: &T::AccountId, misconduct: &mut impl ContinuousMisconduct) -> u8 {
//!			let severity = misconduct.severity();
//!			Self::Slash::on_slash(&who, severity);
//!			misconduct.on_misconduct();
//!			severity.as_misconduct_level()
//!		}
//!
//!		fn slash_on_checkpoint(
//!			misbehaved: &[T::AccountId],
//!			total_validators: u64,
//!			misconduct: &impl CheckpointMisconduct
//!		) -> u8 {
//!			let severity = misconduct.severity(misbehaved.len() as u64, total_validators);
//!
//!			for who in misbehaved {
//!				Self::Slash::on_slash(who, severity);
//!			}
//!
//!			severity.as_misconduct_level()
//!		}
//!	}
//!
//! fn main() {
//!		let unresponsive = Unresponsive;
//!		let misbehaved_validators = vec![1, 2, 3, 4, 5, 6];
//!		let total_validators = 100;
//!		// MyModule is type that implements `Trait`
//!		// SlashingWrapper::<MyModule>::slash_on_checkpoint(&misbehaved_validators, total_validators, &unresponsive);
//! }
//! ```

use parity_codec::Codec;
use primitives::traits::{SimpleArithmetic, MaybeSerializeDebug};

/// Pre-defined types
pub mod misconduct;

mod types;

pub use types::Fraction;

// The specification specifices four different misconduct levels:
//		1) Slashing: 0 <= x <= 0.001
//		2) Slashing: 0.001 < x <= 0.01
//		3) Slashing: 0.01 < x <= 0.1
//		4) Slashing: 0.1 < x <= 1.0
type MisconductLevel = u8;

/// Base trait for representing misconducts
pub trait Misconduct {
	/// Severity represented as a fraction
	type Severity: SimpleArithmetic + Codec + Copy + MaybeSerializeDebug + Default + Into<u128>;
}

/// Behaviour based on misconduct reporting on end of era / timeslot.
/// In those cases the reporter will keep state and report it.
pub trait CheckpointMisconduct: Misconduct {

	/// Estimate severity based `number of misbehaved validators` and `number of validators`
	// TODO: use `Fraction<Self::Severity> instead
	fn severity(&self, num_misbehaved: u64, num_validators: u64) -> Fraction<u64>;
}

/// Behaviour based on continuously reporting of misconducts
/// The type the implements is expected to keep `severity`as part of the type
pub trait ContinuousMisconduct: Misconduct {
	/// Estimate severity based on previous state
	// TODO: use `Fraction<Self::Severity> instead
	fn severity(&self) -> Fraction<u64>;

	/// Increase severity based on previous state
	fn on_misconduct(&mut self);

	/// Decrease severity based on previous state
	fn on_signal(&mut self);
}

/// Slashing interface
pub trait OnSlashing<AccountId> {
	/// Slash validator `who` based on severity_level `severity`
	// TODO: use `Fraction<Misconduct::Severity> instead
	fn on_slash(who: &AccountId, severity: Fraction<u64>);
}

/// Slashing wrapper interface on top of `OnSlashing`
pub trait Slashing<AccountId> {
	/// Specify which `OnSlashing` implementation to use
	type Slash: OnSlashing<AccountId>;

	/// Slash the given account `who`
	/// Returns the misconduct level
	fn slash(who: &AccountId, misconduct: &mut impl ContinuousMisconduct) -> MisconductLevel;

	/// Attempt to slash a list of `misbehaved` validators in the end of a time slot
	/// Returns the misconduct level for all misbehaved validators
	fn slash_on_checkpoint(
		misbehaved: &[AccountId],
		total_validators: u64,
		misconduct: &impl CheckpointMisconduct
	) -> MisconductLevel;
}
