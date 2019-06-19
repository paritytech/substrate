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
use srml_slashing::{OnSlashing, Misconduct};
use primitives::traits::Convert;

type ExtendedBalance = u128;

/// OnSlashing implementation for `Staking`
pub struct StakingSlasher<T>(PhantomData<T>);

impl<T: Trait> OnSlashing<T::AccountId> for StakingSlasher<T>
{
	fn on_slash(who: &T::AccountId, misconduct: &impl Misconduct) {
		// hack to convert both to `u128` and calculate the amount to slash
		// then convert it back `BalanceOf<T>`
		let to_balance = |b: ExtendedBalance|
			<T::CurrencyToVote as Convert<ExtendedBalance, BalanceOf<T>>>::convert(b);
		let to_u128 = |b: BalanceOf<T>|
			<T::CurrencyToVote as Convert<BalanceOf<T>, u64>>::convert(b) as ExtendedBalance;

		let balance = to_u128(<Module<T>>::slashable_balance(&who));
		let severity: ExtendedBalance = misconduct.severity().into();
		let slash = to_balance(balance / severity);
		<Module<T>>::slash_validator(who, slash);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::mock::*;
	use srml_slashing::{Slashing, misconduct::{Unresponsive, BlockProduction}};
	use rstd::cmp;
	use runtime_io::with_externalities;

	struct SlashWrapper<T>(PhantomData<T>);

	impl<T: Trait> Slashing<T::AccountId> for SlashWrapper<T> {
		type Slash = StakingSlasher<T>;

		fn slash(who: &T::AccountId, misconduct: &mut impl Misconduct) {
			Self::Slash::on_slash(&who, misconduct);
			misconduct.on_misconduct();
		}

		fn on_signal(misconduct: &mut impl Misconduct) {
			misconduct.on_signal();
		}
	}

	#[test]
	fn it_works() {
		with_externalities(&mut ExtBuilder::default().build(),
		|| {
			let mut ur = Unresponsive::default();
			let mut bp = BlockProduction::default();
			SlashWrapper::<Test>::slash(&0, &mut ur);
			SlashWrapper::<Test>::slash(&0, &mut bp);
		});
	}
}
