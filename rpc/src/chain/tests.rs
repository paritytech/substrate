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

use primitives::block;
use super::*;

#[test]
fn should_return_header() {
	let state = Chain::new();

	assert_matches!(
		state.header(5u64),
		Ok(ref x) if x == &block::Header {
			parent_hash: 5.into(),
			state_root: 3.into(),
			timestamp: 10,
			number: 5,
		}
	)
}
