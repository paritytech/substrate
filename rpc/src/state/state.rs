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

use primitives::{Address, U256, H256};

use super::{error, StateApi};

/// Relay chain state-related method calls.
#[derive(Debug)]
pub struct State;

impl State {
	/// Create new state API.
	pub fn new() -> Self {
		State
	}
}

impl StateApi for State {
	fn storage(&self, _address: Address, _idx: U256) -> error::Result<H256> {
		bail!(error::ErrorKind::Unimplemented)
	}
}
