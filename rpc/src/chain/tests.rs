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

use super::*;

use test_helpers::Blockchain;

#[test]
fn should_return_header() {
	let state = Blockchain::default();

	assert_matches!(
		ChainApi::header(&state, 0.into()),
		Ok(Some(ref x)) if x == &block::Header {
			parent_hash: 0.into(),
			state_root: 0.into(),
			timestamp: 0,
			number: 0,
		}
	);

	assert_matches!(
		ChainApi::header(&state, 5.into()),
		Ok(None)
	);
}
