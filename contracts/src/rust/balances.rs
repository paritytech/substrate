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

use primitives::{Address, contract};
use primitives::uint::U256;

use rust::contracts::Balances;

use {Externalities};

#[derive(Debug, Default)]
pub struct Contract;

impl<E: Externalities> Balances<E> for Contract {
	type BalanceOf = Address;
	type Transfer = (Address, U256, Address);

	fn balance_of(&self, _ext: &E, _data: Self::BalanceOf) -> contract::Result<U256> {
		unimplemented!()
	}

	fn transfer_preconditions(&self, _db: &E, _data: Self::Transfer) -> contract::Result<bool> {
		unimplemented!()
	}

	fn transfer(&self, _ext: &mut E, _data: Self::Transfer) -> contract::Result<bool> {
		unimplemented!()
	}
}
