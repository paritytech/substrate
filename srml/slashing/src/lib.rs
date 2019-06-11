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

//! Slashing interface
//!
//! That gives functionality to specialize slashing and misconduct for a given type
//! In order to customize severity level and misconduct fees.
//!

mod types;

use parity_codec::Codec;
use primitives::traits::{SimpleArithmetic, MaybeSerializeDebug};

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

/// Slashing interface
pub trait OnSlashing<AccountId, M: Misconduct> {
	/// Slash validator `who` based on severity_level `severity`
	fn on_slash(who: &AccountId, misconduct: M);
}

/// Slashing wrapper interface on top of `OnSlashing`
pub trait Slashing<AccountId, M: Misconduct> {
	/// ..
	type Slash: OnSlashing<AccountId, M>;

	/// Slash the given account `who`
	fn slash(who: &AccountId, misconduct: M);

	/// Decrease severity level after a certain point up to the implementer to determine when.
	fn on_signal(misconduct: M);
}
