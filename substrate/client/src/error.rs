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

use std;
use state_machine;
use primitives::hexdisplay::HexDisplay;
use runtime_primitives::ApplyError;

error_chain! {
	errors {
		/// Backend error.
		Backend(s: String) {
			description("Unrecoverable backend error"),
			display("Backend error: {}", s),
		}

		/// Unknown block.
		UnknownBlock(h: String) {
			description("unknown block"),
			display("UnknownBlock: {}", &*h),
		}

		/// Applying extrinsic error.
		ApplyExtinsicFailed(e: ApplyError) {
			description("Extrinsic error"),
			display("Extrinsic error: {:?}", e),
		}

		/// Execution error.
		Execution(e: Box<state_machine::Error>) {
			description("execution error"),
			display("Execution: {}", e),
		}

		/// Blockchain error.
		Blockchain(e: Box<std::error::Error + Send>) {
			description("Blockchain error"),
			display("Blockchain: {}", e),
		}

		/// Attempt to read storage yet nothing set for that key.
		NoValueForKey(key: Vec<u8>) {
			description("storage doesn't contain key"),
			display("Storage does not contain the key entry: {}", HexDisplay::from(key)),
		}

		/// Invalid state data.
		AuthLenEmpty {
			description("authority count state error"),
			display("Current state of blockchain has no authority count value"),
		}

		/// Invalid state data.
		AuthEmpty(i: u32) {
			description("authority value state error"),
			display("Current state of blockchain has no authority value for index {}", i),
		}

		/// Invalid state data.
		AuthLenInvalid {
			description("authority count state error"),
			display("Current state of blockchain has invalid authority count value"),
		}

		/// Cound not get runtime version.
		VersionInvalid {
			description("Runtime version error"),
			display("On-chain runtime does not specify version"),
		}

		/// Invalid state data.
		AuthInvalid(i: u32) {
			description("authority value state error"),
			display("Current state of blockchain has invalid authority value for index {}", i),
		}

		/// Bad justification for header.
		BadJustification(h: String) {
			description("bad justification for header"),
			display("bad justification for header: {}", &*h),
		}

		/// Not available on light client.
		NotAvailableOnLightClient {
			description("not available on light client"),
			display("This method is not currently available when running in light client mode"),
		}

		/// Invalid remote execution proof.
		InvalidExecutionProof {
			description("invalid execution proof"),
			display("Remote node has responded with invalid execution proof"),
		}

		/// Remote fetch has been cancelled.
		RemoteFetchCancelled {
			description("remote fetch cancelled"),
			display("Remote data fetch has been cancelled"),
		}

		/// Remote fetch has been failed.
		RemoteFetchFailed {
			description("remote fetch failed"),
			display("Remote data fetch has been failed"),
		}

		/// Error decoding call result.
		CallResultDecode(method: &'static str) {
			description("Error decoding call result")
			display("Error decoding call result of {}", method)
		}
	}
}

// TODO [ToDr] Temporary, state_machine::Error should be a regular error not Box.
impl From<Box<state_machine::Error>> for Error {
	fn from(e: Box<state_machine::Error>) -> Self {
		ErrorKind::Execution(e).into()
	}
}

impl From<state_machine::backend::Void> for Error {
	fn from(e: state_machine::backend::Void) -> Self {
		match e {}
	}
}

impl Error {
	/// Chain a blockchain error.
	pub fn from_blockchain(e: Box<std::error::Error + Send>) -> Self {
		ErrorKind::Blockchain(e).into()
	}

	/// Chain a state error.
	pub fn from_state(e: Box<state_machine::Error + Send>) -> Self {
		ErrorKind::Execution(e).into()
	}
}

impl state_machine::Error for Error {}
