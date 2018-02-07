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

use substrate_executor as executor;
use client;
use super::*;

#[test]
fn should_return_header() {
	let client = client::new_in_mem(executor::executor()).unwrap();

	assert_matches!(
		ChainApi::header(&client, "af65e54217fb213853703d57b80fc5b2bb834bf923046294d7a49bff62f0a8b2".into()),
		Ok(Some(ref x)) if x == &block::Header {
			parent_hash: 0.into(),
			number: 0,
			state_root: 0.into(),
			transaction_root: Default::default(),
			digest: Default::default(),
		}
	);

	assert_matches!(
		ChainApi::header(&client, 5.into()),
		Ok(None)
	);
}
