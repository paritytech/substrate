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
pub fn rolling_data<M, OS, SR, ExposedStake>(
	misbehaved: &[SR],
	misconduct: &mut M
) -> u8
where
	M: Misconduct<ExposedStake>,
	SR: SlashRecipient<M::AccountId, ExposedStake>,
	OS: OnSlashing<M, SR, ExposedStake>,
{
	let seve = misconduct.on_misconduct(misbehaved);
	OS::slash(misbehaved, seve);
	misconduct.as_misconduct_level(seve)
}

/// Report misconduct during an era but do not perform any slashing
pub fn era_data<M, OS, SR, ExposedStake>(who: &[SR], misconduct: &mut M)
where
	M: Misconduct<ExposedStake>,
	SR: SlashRecipient<M::AccountId, ExposedStake>,
	OS: OnSlashing<M, SR, ExposedStake>,
{
	let seve = misconduct.on_misconduct(who);
	OS::slash(who, seve);
}

/// Slash in the end of era
pub fn end_of_era<E, OS, SR, ExposedStake>(end_of_era: &E) -> u8
where
	E: OnEndEra<ExposedStake>,
	OS: OnSlashing<E, SR, ExposedStake>,
	SR: SlashRecipient<E::AccountId, ExposedStake>,
{
	let seve = end_of_era.severity();
	let misbehaved = end_of_era.misbehaved::<SR>();
	OS::slash(&misbehaved, seve);
	end_of_era.as_misconduct_level(seve)
}

/// Base trait for representing misconducts
pub trait Misconduct<ExposedStake>: system::Trait
{
	/// Severity represented as a fraction
	type Severity: SimpleArithmetic + Codec + Copy + MaybeSerializeDebug + Default + Into<u128>;

	/// Report misconduct and estimates the current severity level
	fn on_misconduct<SR>(&mut self, misbehaved: &[SR]) -> Fraction<Self::Severity>
	where
		SR: SlashRecipient<Self::AccountId, ExposedStake>;

	/// Convert severity level into misconduct level (1, 2, 3 or 4)
	fn as_misconduct_level(&self, severity: Fraction<Self::Severity>) -> u8;
}

/// Apply slash in the end of the era
pub trait OnEndEra<ExposedStake>: Misconduct<ExposedStake> {
	/// Get severity level accumulated during the current the era
	fn severity(&self) -> Fraction<Self::Severity>;

	/// Get all misbehaved validators of the current era
	fn misbehaved<SR>(&self) -> Vec<SR> where SR: SlashRecipient<Self::AccountId, ExposedStake>;
}

/// Slash misbehaved, should be implemented by some `module` that has access to `Currency`
pub trait OnSlashing<M, SR, Balance>
where
	M: Misconduct<Balance>,
	SR: SlashRecipient<M::AccountId, Balance>
{
	/// Slash
	fn slash(who: &[SR], severity: Fraction<M::Severity>);
}

/// A snapshot of the stake backing a single validator in the system.
/// In which includes the portions of each nominator stash
pub trait SlashRecipient<AccountId, ExposedStake>
{
	/// Get the account id of the misbehaved validator
	fn account_id(&self) -> &AccountId;

	/// Get account id of each of the nominators and its exposed stake
	fn nominators(&self) -> &[(AccountId, ExposedStake)];
}
