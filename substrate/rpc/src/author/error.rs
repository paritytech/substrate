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

//! Authoring RPC module errors.

use extrinsic_pool::txpool;
use rpc;

error_chain! {
	links {
		Pool(txpool::Error, txpool::ErrorKind) #[doc = "Pool error"];
	}
	errors {
		/// Not implemented yet
		Unimplemented {
			description("not yet implemented"),
			display("Method Not Implemented"),
		}
		/// Verification error
		Verification(e: Box<::std::error::Error + Send>) {
			description("extrinsic verification error"),
			display("Extrinsic verification error: {}", e.description()),
		}
	}
}

impl From<Error> for rpc::Error {
	fn from(e: Error) -> Self {
		match e {
			Error(ErrorKind::Unimplemented, _) => rpc::Error {
				code: rpc::ErrorCode::ServerError(-1),
				message: "Not implemented yet".into(),
				data: None,
			},
			// TODO [ToDr] Unwrap Pool errors.
			_ => rpc::Error::internal_error(),
		}
	}
}
