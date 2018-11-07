// Copyright 2018 Parity Technologies (UK) Ltd.
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

use state_machine;
use std::error;

error_chain! {
	errors {
		/// Execution error.
		Execution(e: Box<state_machine::Error>) {
			description("Execution error"),
			display("Execution: {}", e),
		}

		/// Error decoding call result.
		CallResultDecode(method: &'static str) {
			description("Error decoding call result")
			display("Error decoding call result of {}", method)
		}

		/// Generic error.
		//TODO: Find a better way than using a `Box`.
		GenericError(e: Box<dyn error::Error + Send>) {
			description("Generic error")
			display("Generic error while calling an api: {}", e)
		}
	}
}

impl From<Box<state_machine::Error>> for Error {
	fn from(e: Box<state_machine::Error>) -> Self {
		ErrorKind::Execution(e).into()
	}
}
