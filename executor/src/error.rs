// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Rust executor possible errors.

use serializer;

error_chain! {
	foreign_links {
		InvalidData(serializer::Error) #[doc = "Unserializable Data"];
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
		Externalities {
			description("externalities failure"),
			display("Externalities error"),
		}

		/// Invalid index.
		InvalidIndex {
			description("index given was not in range"),
			display("Invalid index provided"),
		}

		/// Invalid return type.
		InvalidReturn {
			description("u64 was not returned"),
			display("Invalid type returned (should be u64)"),
		}

		/// Runtime failed.
		Runtime {
			description("runtime failure"),
			display("Runtime error"),
		}

		/// Runtime failed.
		InvalidMemoryReference {
			description("invalid memory reference"),
			display("Invalid memory reference"),
		}
	}
}
