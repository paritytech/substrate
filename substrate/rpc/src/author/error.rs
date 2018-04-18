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

use client;
use rpc;

error_chain! {
	links {
		Client(client::error::Error, client::error::ErrorKind) #[doc = "Client error"];
	}
	errors {
		/// Not implemented yet
		Unimplemented {
			description("not yet implemented"),
			display("Method Not Implemented"),
		}
		/// Invalid format
		InvalidFormat {
			description("invalid format"),
			display("Invalid format for the extrinsic data"),
		}
		/// Some error with the pool since the import failed.
		PoolError {
			description("pool import failed"),
			display("Pool import failed"),
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
			_ => rpc::Error::internal_error(),
		}
	}
}
