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

use error_chain::*;
use client;
use crate::rpc;
use crate::errors;
pub use internal_errors::*;

#[allow(deprecated)]
mod internal_errors {
	use super::*;
	error_chain! {
		foreign_links {
			Client(client::error::Error) #[doc = "Client error"];
		}
		errors {
			/// Not implemented yet
			Unimplemented {
				description("not yet implemented"),
				display("Method Not Implemented"),
			}
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
