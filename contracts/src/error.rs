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

//! Rust executor possible errors.

#![allow(missing_docs)]

use serializer;
use state_machine;

error_chain! {
	foreign_links {
		InvalidData(serializer::Error);
	}

	errors {
		/// Method is not found
		MethodNotFound(t: String) {
			description("method not found"),
			display("Method not found: '{}'", t),
		}

		/// Code is invalid (expected single byte)
		InvalidCode(c: Vec<u8>) {
			description("invalid code"),
			display("Invalid Code: {:?}", c),
		}

		/// Externalities have failed.
		Externalities(e: Box<state_machine::Error>) {
			description("externalities failure"),
			display("Externalities error: {}", e),
		}
	}
}
