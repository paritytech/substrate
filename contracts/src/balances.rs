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

use primitives::Address;
use primitives::uint::U256;
use state_machine::{Externalities, StaticExternalities};

use error::Result;
use executor::RustExecutor;

#[derive(Debug, Serialize, Deserialize)]
pub struct Transfer {
	/// Transfer value
	value: U256,
	/// Transfer destination
	to: Address,
	/// Replay protection
	nonce: U256,
	/// Data authorizing the transfer (we can derive sender from it)
	authentication_data: Vec<u8>,
}

/// Balances contract rust implementation.
#[derive(Debug, Default)]
pub struct Contract;
impl Contract {
	/// Returns a balance of given address.
	pub fn balance_of<E: StaticExternalities<RustExecutor>>(&self, _ext: &E, _data: Address) -> Result<U256> {
		unimplemented!()
	}

	/// Returns the next nonce to authorize the transfer from given address.
	pub fn next_nonce<E: StaticExternalities<RustExecutor>>(&self, _ext: &E, _data: Address) -> Result<U256> {
		unimplemented!()
	}

	/// Checks preconditions for transfer.
	/// Should verify:
	/// - signature
	/// - replay protection
	/// - enough balance
	pub fn transfer_preconditions<E: StaticExternalities<RustExecutor>>(&self, _db: &E, _data: Transfer) -> Result<bool> {
		unimplemented!()
	}

	/// Perform a transfer.
	/// This should first make sure that precondtions are satisfied and later perform the transfer.
	pub fn transfer<E: Externalities<RustExecutor>>(&self, _ext: &mut E, _data: Transfer) -> Result<bool> {
		unimplemented!()
	}
}
