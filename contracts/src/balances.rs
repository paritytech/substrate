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
use state_machine::Externalities;

use error::Result;
use executor::RustExecutor;

type BalanceOf = Address;
type Transfer = (Address, U256, Address);

#[derive(Debug, Default)]
pub struct Contract;
impl Contract {
	pub fn balance_of<E: Externalities<RustExecutor>>(&self, _ext: &E, _data: BalanceOf) -> Result<U256> {
		unimplemented!()
	}

	pub fn transfer_preconditions<E: Externalities<RustExecutor>>(&self, _db: &E, _data: Transfer) -> Result<bool> {
		unimplemented!()
	}

	pub fn transfer<E: Externalities<RustExecutor>>(&self, _ext: &mut E, _data: Transfer) -> Result<bool> {
		unimplemented!()
	}
}
