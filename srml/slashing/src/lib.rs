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

/// Nominator exposure
#[derive(Default)]
pub struct NominatorExposure<AccountId, Balance> {
	/// The stash account of the nominator in question.
	account_id: AccountId,
	/// Amount of funds exposed.
	value: Balance,
}

/// Exposure for a reported validator
pub struct SlashRecipient<AccountId, Balance> {
	/// Validator account id
	pub account_id: AccountId,
	/// Own balance
	pub value: Balance,
	/// The portions of nominators stashes that are exposed.
	pub nominators: Vec<NominatorExposure<AccountId, Balance>>,
}

/// Report rolling data misconduct and apply slash accordingly
// Pre-condition: the actual implementor of `OnSlashing` has access to
// `session_index` and `number of validators`
pub fn rolling_data<M, OS, Balance>(
	misbehaved: &[SlashRecipient<M::AccountId, Balance>],
	misconduct: &mut M
) -> u8
where
	M: Misconduct,
	OS: OnSlashing<M, Balance>,
{
	let seve = misconduct.on_misconduct(misbehaved);
	OS::slash(misbehaved, seve);
	misconduct.as_misconduct_level(seve)
}

/// Report era misconduct but do not perform any slashing
pub fn era_data<M, OS, Balance>(who: &[SlashRecipient<M::AccountId, Balance>], misconduct: &mut M)
where
	M: Misconduct,
	OS: OnSlashing<M, Balance>,
{
	let seve = misconduct.on_misconduct(who);
	OS::slash(who, seve);
}

/// Slash in the end of era
///
/// Safety: Make sure call this exactly once and in the end of era
pub fn end_of_era<E, Balance, OS>(end_of_era: &E) -> u8
where
	E: OnEndEra,
	OS: OnSlashing<E, Balance>,
{
	let seve = end_of_era.severity();
	let misbehaved = end_of_era.misbehaved();
	OS::slash(&misbehaved[..], seve);
	end_of_era.as_misconduct_level(seve)
}

/// Base trait for representing misconducts
pub trait Misconduct: system::Trait {
	/// Severity represented as a fraction
	type Severity: SimpleArithmetic + Codec + Copy + MaybeSerializeDebug + Default + Into<u128>;

	/// Report misconduct and estimates the current severity level
	fn on_misconduct<Balance>(
		&mut self,
		misbehaved: &[SlashRecipient<Self::AccountId, Balance>]
	) -> Fraction<Self::Severity>;

	/// Convert severity level into misconduct level (1, 2, 3 or 4)
	fn as_misconduct_level(&self, severity: Fraction<Self::Severity>) -> u8;
}

/// Apply slash that occurred only during the era
pub trait OnEndEra: Misconduct {
	/// Get severity level accumulated during the current the era
	fn severity(&self) -> Fraction<Self::Severity>;

	/// Get all misbehaved validators of the current era
	fn misbehaved<Balance>(&self) -> Vec<SlashRecipient<Self::AccountId, Balance>>;
}

/// Slash misbehaved, should be implemented by some `module` that has access to currency
// In practice this is likely to be the `Staking module`
pub trait OnSlashing<M: Misconduct, Balance> {
	/// Slash
	fn slash(who: &[SlashRecipient<M::AccountId, Balance>], severity: Fraction<M::Severity>);
}
