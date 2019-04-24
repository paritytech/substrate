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
use error_chain::*;
use client;
use crate::rpc;
use crate::errors;

error_chain! {
	links {
		Client(client::error::Error, client::error::ErrorKind) #[doc = "Client error"];
	}

	errors {
		/// Provided block range couldn't be resolved to a list of blocks.
		InvalidBlockRange(from: String, to: String, details: String) {
			description("Invalid block range"),
			display("Cannot resolve a block range ['{:?}' ... '{:?}]. {}", from, to, details),
		}
		/// Not implemented yet
		Unimplemented {
			description("not implemented yet"),
			display("Method Not Implemented"),
		}
	}
}

impl From<Error> for rpc::Error {
	fn from(e: Error) -> Self {
		match e {
			Error(ErrorKind::Unimplemented, _) => errors::unimplemented(),
			e => errors::internal(e),
		}
	}
}
