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
		.build(),
	|| {
		let mut misconduct = Test;

		let _ = Balances::make_free_balance_be(&11, 3000);
		let _ = Balances::make_free_balance_be(&21, 1000);
		let _ = Balances::make_free_balance_be(&101, 300);


		assert_eq!(3000, Balances::free_balance(&11));
		assert_eq!(1000, Balances::free_balance(&21));
		assert_eq!(300, Balances::free_balance(&101));

		let misbehaved = vec![
			MockSlashRecipient { account_id: 11, others: vec![(101, 30)] },
			MockSlashRecipient { account_id: 21, others: vec![(101, 70)] },
		];

		// dummy impl slash 10%
		let _ = rolling_data::<_, StakingSlasher<Test, MockSlashRecipient, u64>, _, _>
			(&misbehaved, &mut misconduct);

		assert_eq!(2700, Balances::free_balance(&11));
		assert_eq!(900, Balances::free_balance(&21));
		// 30 * 0.1 + 70 * 0.1 = 10
		assert_eq!(290, Balances::free_balance(&101));
	});
}
