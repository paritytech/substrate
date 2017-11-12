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
use state_machine::Externalities;

use error::Result;
use executor::RustExecutor;

/// Data and some sort of Authentication Data
type DataAndAuth = (Vec<u8>, Vec<u8>);

/// Authentication contract rust implementation.
#[derive(Debug, Default)]
pub struct Contract;
impl Contract {
	/// Verify authentication data.
	///
	/// Given Message and Authentication Data verifies it and returns:
	/// 1. None in case it doesn't match (i.e. signature is invalid)
	/// 2. A address who signed that Message.
	pub fn check_auth<E: Externalities<RustExecutor>>(&self, _ext: &E, _data: DataAndAuth) -> Result<Option<Address>> {
		unimplemented!()
	}
}
