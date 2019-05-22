// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Transaction pool error.

// Silence: `use of deprecated item 'std::error::Error::cause': replaced by Error::source, which can support downcasting`
// https://github.com/paritytech/substrate/issues/1547
#![allow(deprecated)]

use client;
use txpool;
use error_chain::{
	error_chain, error_chain_processing, impl_error_chain_processed, impl_extract_backtrace, impl_error_chain_kind
};
use std::convert::TryFrom;

error_chain! {
	foreign_links {
		Client(client::error::Error) #[doc = "Client error"];
	}
	links {
		Pool(txpool::error::Error, txpool::error::ErrorKind) #[doc = "Pool error"];
	}
}

#[allow(deprecated)]
impl txpool::IntoPoolError for Error {
	fn into_pool_error(self) -> ::std::result::Result<txpool::error::Error, Self> {
		match self {
			Error(ErrorKind::Pool(e), c) => Ok(txpool::error::Error(e, c)),
			e => Err(e),
		}
	}
}

impl TryFrom<Error> for txpool::error::Error {
	type Error = Error;

	fn try_from(err: Error) -> ::std::result::Result<txpool::error::Error, Error> {
		match err {
			Error(ErrorKind::Pool(e), c) => Ok(txpool::error::Error(e, c)),
			e => Err(e),
		}
	}
}
