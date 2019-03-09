// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
