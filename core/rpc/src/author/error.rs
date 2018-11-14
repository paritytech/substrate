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

//! Authoring RPC module errors.

use client;
use transaction_pool::txpool;
use rpc;

use errors;

error_chain! {
	links {
		Pool(txpool::error::Error, txpool::error::ErrorKind) #[doc = "Pool error"];
		Client(client::error::Error, client::error::ErrorKind) #[doc = "Client error"];
	}
	errors {
		/// Not implemented yet
		Unimplemented {
			description("not yet implemented"),
			display("Method Not Implemented"),
		}
		/// Incorrect extrinsic format.
		BadFormat {
			description("bad format"),
			display("Invalid extrinsic format"),
		}
		/// Verification error
		Verification(e: Box<::std::error::Error + Send>) {
			description("extrinsic verification error"),
			display("Extrinsic verification error: {}", e.description()),
		}
	}
}

const ERROR: i64 = 1000;

impl From<Error> for rpc::Error {
	fn from(e: Error) -> Self {
		match e {
			Error(ErrorKind::Unimplemented, _) => errors::unimplemented(),
			Error(ErrorKind::BadFormat, _) => rpc::Error {
				code: rpc::ErrorCode::ServerError(ERROR + 1),
				message: "Extrinsic has invalid format.".into(),
				data: None,
			},
			Error(ErrorKind::Verification(e), _) => rpc::Error {
				code: rpc::ErrorCode::ServerError(ERROR + 2),
				message: e.description().into(),
				data: Some(format!("{:?}", e).into()),
			},
			e => errors::internal(e),
		}
	}
}
