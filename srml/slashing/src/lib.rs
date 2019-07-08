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

/// Report rolling data misconduct and apply slash accordingly
pub fn rolling_data<M, OS, AccountId, Exposure>(
	misbehaved: &[(AccountId, Exposure)],
	misconduct: &mut M
) -> u8
where
	M: Misconduct<AccountId, Exposure>,
	OS: OnSlashing<AccountId, Exposure, M::Severity>,
{
	let seve = misconduct.on_misconduct(misbehaved);
	OS::slash(misbehaved, seve);
	misconduct.as_misconduct_level(seve)
}

/// Report misconduct during an era but do not perform any slashing
pub fn era_data<M, OS, AccountId, Exposure>(misbehaved: &[(AccountId, Exposure)], misconduct: &mut M)
where
	M: Misconduct<AccountId, Exposure>,
	OS: OnSlashing<AccountId, Exposure, M::Severity>,
{
	misconduct.on_misconduct(misbehaved);
}

/// Slash in the end of era
pub fn end_of_era<E, OS, AccountId, Exposure>(end_of_era: &E) -> u8
where
	E: OnEndEra<AccountId, Exposure>,
	OS: OnSlashing<AccountId, Exposure, E::Severity>,
{
	let seve = end_of_era.severity();
	let misbehaved = end_of_era.misbehaved();
	OS::slash(&misbehaved, seve);
	end_of_era.as_misconduct_level(seve)
}

/// Base trait for representing misconducts
pub trait Misconduct<AccountId, Exposure>
{
	/// Severity
	type Severity: SimpleArithmetic + Codec + Copy + MaybeSerializeDebug + Default;

	/// Report misconduct and estimates the current severity level
	// TODO: replace this with Self::Severity
	fn on_misconduct(&mut self, misbehaved: &[(AccountId, Exposure)]) -> Fraction<Self::Severity>;

	/// Convert severity level into misconduct level (1, 2, 3 or 4)
	fn as_misconduct_level(&self, severity: Fraction<Self::Severity>) -> u8;
}

/// Apply slash in the end of the era
pub trait OnEndEra<AccountId, Exposure>: Misconduct<AccountId, Exposure> {
	/// Get severity level accumulated during the current the era
	// TODO: replace this with Self::Severity
	fn severity(&self) -> Fraction<Self::Severity>;

	/// Get all misbehaved validators of the current era
	fn misbehaved(&self) -> Vec<(AccountId, Exposure)>;
}

/// Slash misbehaved, should be implemented by some `module` that has access to `Currency`
pub trait OnSlashing<AccountId, Exposure, Severity> {
	/// Slash
	fn slash(who: &[(AccountId, Exposure)], severity: Fraction<Severity>);
}
