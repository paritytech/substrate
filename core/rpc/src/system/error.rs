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
//! System RPC module errors.

use error_chain::*;

use crate::rpc;
use crate::errors;
use crate::system::helpers::Health;

error_chain! {
	errors {
		/// Node is not fully functional
		NotHealthy(h: Health) {
			description("node is not healthy"),
			display("Node is not fully functional: {}", h)
		}

		/// Not implemented yet
		Unimplemented {
			description("not yet implemented"),
			display("Method Not Implemented"),
		}
	}
}

const ERROR: i64 = 2000;

impl From<Error> for rpc::Error {
	fn from(e: Error) -> Self {
		match e {
			Error(ErrorKind::Unimplemented, _) => errors::unimplemented(),
			Error(ErrorKind::NotHealthy(h), _) => rpc::Error {
				code: rpc::ErrorCode::ServerError(ERROR + 1),
				message: "node is not healthy".into(),
				data:serde_json::to_value(h).ok(),
			},
			e => errors::internal(e),
		}
	}
}
