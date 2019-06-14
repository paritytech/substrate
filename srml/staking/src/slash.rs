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

use srml_slashing::{OnSlashing, Misconduct};
use crate::{BalanceOf, Module, Trait};
use srml_support::traits::Currency;
use rstd::marker::PhantomData;

/// OnSlashing implementation for `Staking`
pub struct StakingSlasher<T, M> {
	t: PhantomData<T>,
	m: PhantomData<M>,
}

impl<T: Trait, M: Misconduct> OnSlashing<T::AccountId, M> for StakingSlasher<T, M>
where
	M::Severity: Into<BalanceOf<T>>
{
	fn on_slash(who: &T::AccountId, misconduct: M) {
		let balance = T::Currency::free_balance(&who);
		let slash = balance / misconduct.severity().into();
		<Module<T>>::slash_validator(who, slash);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::mock::*;
	use srml_slashing::Slashing;
	use rstd::cmp;
	use runtime_io::with_externalities;

	type Balance = balances::Module<Test>;

	#[derive(Copy, Clone, Eq, PartialEq)]
	struct MisconductT {
		severity: u64,
	}

	impl Default for MisconductT {
		fn default() -> Self {
			Self { severity: 1000 }
		}
	}

	impl Misconduct for MisconductT {
		type Severity = u64;

		fn on_misconduct(&mut self) {
			self.severity = cmp::max(1, self.severity / 2);
		}

		fn on_signal(&mut self) {
			self.severity = cmp::min(100_000, self.severity * 2);
		}

		fn severity(&self) -> Self::Severity {
			self.severity
		}
	}

	struct SlashWrapper;

	impl Slashing<u64, MisconductT> for SlashWrapper {
		type Slash = StakingSlasher<Test, MisconductT>;

		fn slash(who: &u64, mut misconduct: MisconductT) {
			Self::Slash::on_slash(&who, misconduct);
			misconduct.on_misconduct();
		}

		fn on_signal(mut misconduct: MisconductT) {
			misconduct.on_signal();
		}
	}

	#[test]
	fn it_works() {
		with_externalities(&mut ExtBuilder::default().build(),
		|| {
			let who = 0;
			let _ = Balance::deposit_creating(&who, 100_000);
			assert_eq!(Balance::free_balance(&who), 100_000);
			let mut misconduct = MisconductT::default();
			SlashWrapper::slash(&who, misconduct);
		});
	}
}
