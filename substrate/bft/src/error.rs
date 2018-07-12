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

//! Error types in the BFT service.

error_chain! {
	errors {
		/// Missing state at block with given descriptor.
		StateUnavailable(b: String) {
			description("State missing at given block."),
			display("State unavailable at block {}", b),
		}

		/// I/O terminated unexpectedly
		IoTerminated {
			description("I/O terminated unexpectedly."),
			display("I/O terminated unexpectedly."),
		}

		/// Unable to schedule wakeup.
		FaultyTimer(e: ::tokio::timer::Error) {
			description("Timer error"),
			display("Timer error: {}", e),
		}

		/// Unable to propose a block.
		CannotPropose {
			description("Unable to create block proposal."),
			display("Unable to create block proposal."),
		}

		/// Error checking signature
		InvalidSignature(s: ::ed25519::Signature, a: ::primitives::AuthorityId) {
			description("Message signature is invalid"),
			display("Message signature {:?} by {:?} is invalid.", s, a),
		}

		/// Account is not an authority.
		InvalidAuthority(a: ::primitives::AuthorityId) {
			description("Message sender is not a valid authority"),
			display("Message sender {:?} is not a valid authority.", a),
		}

		/// Authoring interface does not match the runtime.
		InvalidRuntime {
			description("Authoring for current runtime is not supported"),
			display("Authoring for current runtime is not supported."),
		}

		/// Justification requirements not met.
		InvalidJustification {
			description("Invalid justification"),
			display("Invalid justification."),
		}

		/// Some other error.
		Other(e: Box<::std::error::Error + Send>) {
			description("Other error")
			display("Other error: {}", e.description())
		}
	}
}

impl From<::rhododendron::InputStreamConcluded> for Error {
	fn from(_: ::rhododendron::InputStreamConcluded) -> Error {
		ErrorKind::IoTerminated.into()
	}
}
