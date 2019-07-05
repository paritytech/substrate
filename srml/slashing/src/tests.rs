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

use crate::*;
use crate::mock::*;
use runtime_io::with_externalities;
use srml_support::traits::Currency;

#[test]
fn slash_nominator_based_on_exposure() {
	with_externalities(&mut ExtBuilder::default()
		.nominate(false)
		.build(),
	|| {
		let mut misconduct = Test;

		let _ = Balances::make_free_balance_be(&11, 3000);
		let _ = Balances::make_free_balance_be(&21, 1000);
		let _ = Balances::make_free_balance_be(&5, 300);
		let _ = Balances::make_free_balance_be(&6, 500);

		assert_eq!(3000, Balances::free_balance(&11));
		assert_eq!(1000, Balances::free_balance(&21));
		assert_eq!(300, Balances::free_balance(&5));
		assert_eq!(500, Balances::free_balance(&6));


		let x = SlashRecipient {
			account_id: 11,
			value: Balances::free_balance(&11),
			nominators: vec![
				NominatorExposure { account_id: 5, value: 50 },
				NominatorExposure { account_id: 6, value: 60 }
			]
		};

		let y = SlashRecipient {
			account_id: 21,
			value: Balances::free_balance(&21),
			nominators: vec![
				NominatorExposure { account_id: 5, value: 100 },
				NominatorExposure { account_id: 6, value: 10 }
			]
		};

		let misbehaved = vec![x, y];

		// dummy impl slash 10%
		let _ = rolling_data::<_, StakingSlasher<Test, u64>, _>(&misbehaved, &mut misconduct);

		assert_eq!(2700, Balances::free_balance(&11));
		assert_eq!(900, Balances::free_balance(&21));
		// slash 0.1 * 50 + 0.1*100 = 15
		assert_eq!(285, Balances::free_balance(&5));
		// slash 0.1 * 60 + 0.1*10 = 7
		assert_eq!(493, Balances::free_balance(&6));
	});
}
