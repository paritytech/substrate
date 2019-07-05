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

/// Nominator exposure
#[derive(Default)]
pub struct NominatorExposure<AccountId, Balance> {
	/// The stash account of the nominator in question.
	account_id: AccountId,
	/// Amount of funds exposed.
	value: Balance,
}

/// Exposure for a reported validator
#[derive(Default)]
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
	fn on_misconduct<B>(&mut self, misbehaved: &[SlashRecipient<Self::AccountId, B>]) -> Fraction<Self::Severity>;

	/// Convert severity level into misconduct level (1, 2, 3 or 4)
	fn as_misconduct_level(&self, severity: Fraction<Self::Severity>) -> u8;
}

/// Apply slash that occurred only during the era
pub trait OnEndEra: Misconduct {
	/// Get severity level accumulated during the current the era
	fn severity(&self) -> Fraction<Self::Severity>;

	/// Get all misbehaved validators of the current era
	fn misbehaved<B>(&self) -> Vec<SlashRecipient<Self::AccountId, B>>;
}

/// Slash misbehaved, should be implemented by some `module` that has access to currency
// In practice this is likely to be the `Staking module`
pub trait OnSlashing<M: Misconduct, Balance> {
	/// Slash
	fn slash(who: &[SlashRecipient<M::AccountId, Balance>], severity: Fraction<M::Severity>);
}

#[cfg(test)]
mod test {
	use super::*;
	use primitives::traits::{IdentityLookup, Convert};
	use primitives::testing::{Header, UintAuthorityId};
	use substrate_primitives::H256;
	use srml_staking::EraIndex;
	use srml_support::{impl_outer_origin, parameter_types, traits::{Currency, Get}};
	use rstd::marker::PhantomData;

	type AccountId = u64;
	type BlockNumber = u64;
	type Balance = u64;
	type Staking = srml_staking::Module<Test>;
	type BalanceOf<T> = <<T as srml_staking::Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;
	type ExtendedBalance = u128;

	pub struct CurrencyToVoteHandler;

	impl Convert<u64, u64> for CurrencyToVoteHandler {
		fn convert(x: u64) -> u64 { x }
	}
	impl Convert<u128, u64> for CurrencyToVoteHandler {
		fn convert(x: u128) -> u64 {
			x as u64
		}
	}

	pub struct ExistentialDeposit;
	impl Get<u64> for ExistentialDeposit {
		fn get() -> u64 {
			0
		}
	}

	#[derive(Clone, PartialEq, Eq, Debug)]
	pub struct Test;

	impl_outer_origin!{
		pub enum Origin for Test {}
	}

	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = ::primitives::traits::BlakeTwo256;
		type AccountId = AccountId;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
	}

	impl balances::Trait for Test {
		type Balance = Balance;
		type OnFreeBalanceZero = Staking;
		type OnNewAccount = ();
		type Event = ();
		type TransactionPayment = ();
		type TransferPayment = ();
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type TransferFee = TransferFee;
		type CreationFee = CreationFee;
		type TransactionBaseFee = TransactionBaseFee;
		type TransactionByteFee = TransactionByteFee;
	}

	impl srml_staking::Trait for Test {
		type Currency = balances::Module<Self>;
		type CurrencyToVote = CurrencyToVoteHandler;
		type OnRewardMinted = ();
		type Event = ();
		type Slash = ();
		type Reward = ();
		type SessionsPerEra = SessionsPerEra;
		type BondingDuration = BondingDuration;
	}

	impl session::Trait for Test {
		type SelectInitialValidators = Staking;
		type OnSessionEnding = Staking;
		type Keys = UintAuthorityId;
		type ShouldEndSession = session::PeriodicSessions<Period, Offset>;
		type SessionHandler = ();
		type Event = ();
	}

	parameter_types! {
		pub const SessionsPerEra: session::SessionIndex = 3;
		pub const BondingDuration: EraIndex = 3;
	}

	parameter_types! {
		pub const Period: BlockNumber = 1;
		pub const Offset: BlockNumber = 0;
	}

	parameter_types! {
		pub const TransferFee: u64 = 0;
		pub const CreationFee: u64 = 0;
		pub const TransactionBaseFee: u64 = 0;
		pub const TransactionByteFee: u64 = 0;
	}

	impl Misconduct for Test {
		type Severity = u64;

		fn as_misconduct_level(&self, _severity: Fraction<Self::Severity>) -> u8 {
			1
		}

		fn on_misconduct<B>(&mut self, _misbehaved: &[SlashRecipient<Self::AccountId, B>]) -> Fraction<Self::Severity> {
			Fraction::zero()
		}
	}

	pub struct StakingSlasher<T, U> {
		t: PhantomData<T>,
		u: PhantomData<U>,
	}

	impl<T, B> OnSlashing<T, B> for StakingSlasher<T, B>
	where
		T: srml_staking::Trait + Misconduct,
		B: Into<u128> + Clone,
	{
		fn slash(to_punish: &[SlashRecipient<T::AccountId, B>], severity: Fraction<T::Severity>) {
			// hack to convert both to `u128` and calculate the amount to slash
			// then convert it back `BalanceOf<T>`
			let to_balance = |b: ExtendedBalance|
				<T::CurrencyToVote as Convert<ExtendedBalance, BalanceOf<T>>>::convert(b);
			let slash = |balance: u128, severity: Fraction<T::Severity>| {
				let d = balance.saturating_mul(severity.denominator().into());
				let n = severity.numerator().into();
				to_balance(d.checked_div(n).unwrap_or(0))
			};

			for who in to_punish {
				let balance: u128 = who.value.clone().into();
				let slash_amount = slash(balance, severity);

				// slash the validator
				T::Currency::slash(&who.account_id, slash_amount);

				// slash nominators for the same severity
				for nominator in &who.nominators {
					let balance: u128 = nominator.value.clone().into();
					let slash_amount = slash(balance, severity);
					T::Currency::slash(&nominator.account_id, slash_amount);
				}
			}
		}
	}

	// TODO(niklasad1): no Externalities-provided that's why it will panic
	#[test]
	#[should_panic]
	fn it_works() {
		let mut misconduct = Test;
		let misbehaved: Vec<SlashRecipient<u64, u64>> = vec![SlashRecipient::default(), SlashRecipient::default()];

		era_data::<_, StakingSlasher<Test, u64>, _>(&misbehaved, &mut misconduct);
		let _ = rolling_data::<_, StakingSlasher<Test, u64>, _>(&misbehaved, &mut misconduct);
	}
}
