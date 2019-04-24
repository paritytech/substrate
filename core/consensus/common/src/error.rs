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
//! Error types in Consensus
use runtime_version::RuntimeVersion;
use error_chain::{error_chain, error_chain_processing, impl_error_chain_processed,
	impl_extract_backtrace, impl_error_chain_kind};
use primitives::ed25519::{Public, Signature};

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

		/// Error while working with inherent data.
		InherentData(e: String) {
			description("InherentData error"),
			display("InherentData error: {}", e),
		}

		/// Unable to propose a block.
		CannotPropose {
			description("Unable to create block proposal."),
			display("Unable to create block proposal."),
		}

		/// Error checking signature
		InvalidSignature(s: Signature, a: Public) {
			description("Message signature is invalid"),
			display("Message signature {:?} by {:?} is invalid.", s, a),
		}

		/// Invalid authorities set received from the runtime.
		InvalidAuthoritiesSet {
			description("authorities set is invalid"),
			display("Current state of blockchain has invalid authorities set"),
		}

		/// Account is not an authority.
		InvalidAuthority(a: Public) {
			description("Message sender is not a valid authority"),
			display("Message sender {:?} is not a valid authority.", a),
		}

		/// Authoring interface does not match the runtime.
		IncompatibleAuthoringRuntime(native: RuntimeVersion, on_chain: RuntimeVersion) {
			description("Authoring for current runtime is not supported"),
			display("Authoring for current runtime is not supported. Native ({}) cannot author for on-chain ({}).", native, on_chain),
		}

		/// Authoring interface does not match the runtime.
		RuntimeVersionMissing {
			description("Current runtime has no version"),
			display("Authoring for current runtime is not supported since it has no version."),
		}

		/// Authoring interface does not match the runtime.
		NativeRuntimeMissing {
			description("This build has no native runtime"),
			display("Authoring in current build is not supported since it has no runtime."),
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

		/// Error from the client while importing
		ClientImport(reason: String) {
			description("Import failed"),
			display("Import failed: {}", reason),
		}
	}
}
