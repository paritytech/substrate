// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Substrate client possible errors.

#![allow(missing_docs)]

use std;
use state_machine;
use runtime_primitives::ApplyError;
use consensus;

error_chain! {
	links {
		Consensus(consensus::Error, consensus::ErrorKind);
	}
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
		ApplyExtrinsicFailed(e: ApplyError) {
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

		/// Invalid authorities set received from the runtime.
		InvalidAuthoritiesSet {
			description("authorities set is invalid"),
			display("Current state of blockchain has invalid authorities set"),
		}

		/// Could not get runtime version.
		VersionInvalid {
			description("Runtime version error"),
			display("On-chain runtime does not specify version"),
		}

		/// Genesis config is invalid.
		GenesisInvalid {
			description("Genesis config error"),
			display("Genesis config provided is invalid"),
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

		/// Invalid remote header proof.
		InvalidHeaderProof {
			description("invalid header proof"),
			display("Remote node has responded with invalid header proof"),
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

		/// Changes tries are not supported.
		ChangesTriesNotSupported {
			description("changes tries are not supported"),
			display("Changes tries are not supported by the runtime"),
		}

		/// Key changes query has failed.
		ChangesTrieAccessFailed(e: String) {
			description("invalid changes proof"),
			display("Failed to check changes proof: {}", e),
		}

		/// Last finalized block not parent of current.
		NonSequentialFinalization(s: String) {
			description("Did not finalize blocks in sequential order."),
			display("Did not finalize blocks in sequential order."),
		}

		/// Safety violation: new best block not descendent of last finalized.
		NotInFinalizedChain {
			description("Potential long-range attack: block not in finalized chain."),
			display("Potential long-range attack: block not in finalized chain."),
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
