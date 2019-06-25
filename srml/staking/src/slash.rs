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

use crate::{BalanceOf, Module, Trait};
use rstd::marker::PhantomData;
use srml_slashing::{OnSlashing, Misconduct, Fraction};
use primitives::traits::Convert;

type ExtendedBalance = u128;

/// OnSlashing implementation for `Staking`
pub struct StakingSlasher<T>(PhantomData<T>);

impl<T: Trait> OnSlashing<T::AccountId> for StakingSlasher<T> {
	fn on_slash<M: Misconduct>(who: &T::AccountId, severity: Fraction<M::Severity>) {
		// hack to convert both to `u128` and calculate the amount to slash
		// then convert it back `BalanceOf<T>`
		let to_balance = |b: ExtendedBalance|
			<T::CurrencyToVote as Convert<ExtendedBalance, BalanceOf<T>>>::convert(b);
		let to_u128 = |b: BalanceOf<T>|
			<T::CurrencyToVote as Convert<BalanceOf<T>, u64>>::convert(b) as ExtendedBalance;

		let balance = to_u128(<Module<T>>::slashable_balance(&who));
		let slash = to_balance((balance / severity.numerator().into()) * severity.denominator().into());
		<Module<T>>::slash_validator(who, slash);
	}
}

#[cfg(test)]
mod tests {
	use crate::mock::*;
	use srml_slashing::{Slashing, misconduct};
	use runtime_io::with_externalities;

	#[test]
	fn it_works() {
		with_externalities(&mut ExtBuilder::default()
			.build(),
		|| {
			// ensure 11, 21, 31 and 41 are `stakers`
			assert_eq!(Staking::bonded(&11), Some(10));
			assert_eq!(Staking::bonded(&21), Some(20));
			assert_eq!(Staking::bonded(&31), Some(30));
			assert_eq!(Staking::bonded(&41), Some(40));

			assert_eq!(1125, Staking::slashable_balance(&11));
			assert_eq!(1000, Balances::free_balance(&11));

			// Slash 1.5%
			//
			// Slashable balance: 1125
			//
			// 0.015 -> Fraction { denominator: 3 / numerator: 200)
			// (1125 / 200) * 3 = 15
			// (1125 * 0.015) = 16.875
			//
			// Illustration that we loose  accurancy representing it as a `Fraction`
			assert_eq!(Staking::slash_on_checkpoint(&[11, 21, 31, 41], 30, &misconduct::Unresponsive), 3);
			assert_eq!(985, Balances::free_balance(&11));
		});
	}
}
