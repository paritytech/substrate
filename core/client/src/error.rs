// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//! Substrate client possible errors.

// Silence: `use of deprecated item 'std::error::Error::cause': replaced by Error::source, which can support downcasting`
// https://github.com/paritytech/substrate/issues/1547
#![allow(deprecated)]
#![allow(missing_docs)]

use std;
use state_machine;
use runtime_primitives::ApplyError;
use consensus;
use error_chain::*;

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

		/// Invalid remote CHT-based proof.
		InvalidCHTProof {
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

		/// Error decoding call result.
		CallResultDecode(method: &'static str) {
			description("Error decoding call result")
			display("Error decoding call result of {}", method)
		}

		/// Error converting a parameter between runtime and node.
		RuntimeParamConversion(param: &'static str) {
			description("Error converting parameter between runtime and node")
			display("Error converting `{}` between runtime and node", param)
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

		/// Hash that is required for building CHT is missing.
		MissingHashRequiredForCHT(cht_num: u64, block_number: u64) {
			description("missed hash required for building CHT"),
			display("Failed to get hash of block#{} for building CHT#{}", block_number, cht_num),
		}
	}
}

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
