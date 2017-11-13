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

//! Polkadot client possible errors.

use primitives::block;
use state_machine;

error_chain! {
	errors {
		/// Backend error.
		Backend {
			description("Unrecoverable backend error"),
			display("Backend error"),
		}

		/// Unknown block.
		UnknownBlock(h: block::HeaderHash) {
			description("unknown block"),
			display("UnknownBlock: {}", h),
		}

		/// Execution error.
		Execution(e: Box<state_machine::Error>) {
			description("execution error"),
			display("Execution: {}", e),
		}
	}
}

// TODO [ToDr] Temporary, state_machine::Error should be a regular error not Box.
impl From<Box<state_machine::Error>> for Error {
	fn from(e: Box<state_machine::Error>) -> Self {
		ErrorKind::Execution(e).into()
	}
}
