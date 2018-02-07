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

//! Polkadot client API. This builds upon a substrate client to add strongly-typed
//! wrappers for state-fetching functions.

extern crate substrate_client as s_client;
extern crate substrate_state_machine as s_state_machine;

use s_client::Client;
use s_client::backend::Backend as ClientBackend;
use s_state_machine::backend::Backend as StateBackend;

/// An implementation of the polkadot client API.
pub trait PolkadotClient {
	type Error;
}

impl<B, E> PolkadotClient for Client<B, E> where
	B: ClientBackend,
	E: s_state_machine::CodeExecutor,
	s_client::error::Error: From<<<B as ClientBackend>::State as StateBackend>::Error>
{
	type Error = s_client::error::Error;

}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
