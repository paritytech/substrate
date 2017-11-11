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

use primitives::{contract, Address};
use primitives::uint::U256;

use rust::contracts::Authentication;

use {Externalities};

#[derive(Debug, Default)]
pub struct Contract;

impl<E: Externalities> Authentication<E> for Contract {
	type AuthData = (Vec<u8>, Vec<u8>);

	fn check_auth(&self, ext: &E, data: Self::AuthData) -> contract::Result<Option<Vec<Address>>> {
		unimplemented!()
	}
}
