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

//! Rust executor possible errors.

// Silence: `use of deprecated item 'std::error::Error::cause': replaced by Error::source, which can support downcasting`
// https://github.com/paritytech/substrate/issues/1547
#![allow(deprecated)]

use state_machine;
use serializer;
use wasmi;
use error_chain::{
	error_chain, error_chain_processing, impl_error_chain_processed,
	impl_extract_backtrace, impl_error_chain_kind
};

error_chain! {
	foreign_links {
		InvalidData(serializer::Error) #[doc = "Unserializable Data"];
		Trap(wasmi::Trap) #[doc = "Trap occured during execution"];
		Wasmi(wasmi::Error) #[doc = "Wasmi loading/instantiating error"];
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

		/// Could not get runtime version.
		VersionInvalid {
			description("Runtime version error"),
			display("On-chain runtime does not specify version"),
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

impl state_machine::Error for Error {}
