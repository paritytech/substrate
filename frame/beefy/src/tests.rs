// Copyright (C) 2020 - 2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use std::vec;

use codec::Encode;

use sp_core::H256;
use sp_runtime::DigestItem;

use frame_support::traits::OnInitialize;

use crate::mock::*;

fn init_block(block: u64) {
	System::set_block_number(block);
	Session::on_initialize(block);
}

pub fn beefy_log(log: ConsensusLog<BeefyId>) -> DigestItem<H256> {
	DigestItem::Consensus(BEEFY_ENGINE_ID, log.encode())
}

#[test]
fn genesis_session_initializes_authorities() {
	let want = vec![mock_beefy_id(1), mock_beefy_id(2), mock_beefy_id(3), mock_beefy_id(4)];

	new_test_ext(vec![1, 2, 3, 4]).execute_with(|| {
		let authorities = Beefy::authorities();

		assert!(authorities.len() == 2);
		assert_eq!(want[0], authorities[0]);
		assert_eq!(want[1], authorities[1]);

		assert!(Beefy::validator_set_id() == 0);

		let next_authorities = Beefy::next_authorities();

		assert!(next_authorities.len() == 2);
		assert_eq!(want[0], next_authorities[0]);
		assert_eq!(want[1], next_authorities[1]);
	});
}

#[test]
fn session_change_updates_authorities() {
	new_test_ext(vec![1, 2, 3, 4]).execute_with(|| {
		init_block(1);

		assert!(0 == Beefy::validator_set_id());

		// no change - no log
		assert!(System::digest().logs.is_empty());

		init_block(2);

		assert!(1 == Beefy::validator_set_id());

		let want = beefy_log(ConsensusLog::AuthoritiesChange {
			new_validator_set: vec![mock_beefy_id(3), mock_beefy_id(4)],
			new_validator_set_id: 1,
		});

		let log = System::digest().logs[0].clone();

		assert_eq!(want, log);
	});
}
#[test]
fn session_change_updates_next_authorities() {
	let want = vec![mock_beefy_id(1), mock_beefy_id(2), mock_beefy_id(3), mock_beefy_id(4)];

	new_test_ext(vec![1, 2, 3, 4]).execute_with(|| {
		init_block(1);

		let next_authorities = Beefy::next_authorities();

		assert!(next_authorities.len() == 2);
		assert_eq!(want[0], next_authorities[0]);
		assert_eq!(want[1], next_authorities[1]);

		init_block(2);

		let next_authorities = Beefy::next_authorities();

		assert!(next_authorities.len() == 2);
		assert_eq!(want[2], next_authorities[0]);
		assert_eq!(want[3], next_authorities[1]);
	});
}
