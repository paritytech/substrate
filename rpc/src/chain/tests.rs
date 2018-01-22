// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

use polkadot_executor as executor;
use client;
use super::*;

#[test]
fn should_return_header() {
	let client = client::new_in_mem(executor::executor()).unwrap();

	assert_matches!(
		ChainApi::header(&client, "6fa40c5311d3803c6c2880a71ac6302ae1d832fa58ed0d1069f8e4227082f063".into()),
		Ok(Some(ref x)) if x == &block::Header {
			parent_hash: 0.into(),
			number: 0,
			state_root: 0.into(),
			parachain_activity: Default::default(),
			logs: vec![],
		}
	);

	assert_matches!(
		ChainApi::header(&client, 5.into()),
		Ok(None)
	);
}
