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

//! TODO

#![warn(missing_docs, rust_2018_idioms)]
#![cfg_attr(not(feature = "std"), no_std)]

use rstd::vec::Vec;
use parity_codec::Codec;
use primitives::traits::{SimpleArithmetic, MaybeSerializeDebug};

mod fraction;
pub use fraction::Fraction;

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

/// Report misbehaviour but don't apply slashing
pub fn report_misconduct<MR, AccountId, Exposure>(
	misbehaved: Vec<(AccountId, Exposure)>,
	misconduct: &mut MR
)
where
	MR: MisconductReporter<AccountId, Exposure>,
{
	misconduct.on_misconduct(misbehaved);
}

/// Slash the misbehaviours
pub fn slash<M, OS, AccountId, Exposure>(slash: &M) -> u8
where
	M: Misconduct<AccountId, Exposure>,
	OS: OnSlashing<AccountId, Exposure, M::Severity>,
{
	let seve = slash.severity();
	let misbehaved = slash.misbehaved();
	OS::slash(&misbehaved, seve);
	slash.as_misconduct_level(seve)
}

/// Report misconducts
pub trait MisconductReporter<AccountId, Exposure>
{
	/// Report misconduct
	fn on_misconduct(&mut self, misbehaved: Vec<(AccountId, Exposure)>);
}

/// Misconduct interface
pub trait Misconduct<AccountId, Exposure> {
	/// Severity
	type Severity: SimpleArithmetic + Codec + Copy + MaybeSerializeDebug + Default;

	/// Get estimated severity level
	// TODO: replace this with Self::Severity
	fn severity(&self) -> Fraction<Self::Severity>;

	/// Convert severity level into misconduct level (1, 2, 3 or 4)
	fn as_misconduct_level(&self, severity: Fraction<Self::Severity>) -> u8;

	/// Get all misbehaved validators of the current era
	fn misbehaved(&self) -> Vec<(AccountId, Exposure)>;
}

/// Slash misbehaved, should be implemented by some `module` that has access to `Currency`
pub trait OnSlashing<AccountId, Exposure, Severity> {
	/// Slash
	fn slash(who: &[(AccountId, Exposure)], severity: Fraction<Severity>);
}
