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
//! Transaction pool error.

use client;
use txpool;
use error_chain::{
	error_chain, error_chain_processing, impl_error_chain_processed, impl_extract_backtrace, impl_error_chain_kind
};

error_chain! {
	links {
		Client(client::error::Error, client::error::ErrorKind) #[doc = "Client error"];
		Pool(txpool::error::Error, txpool::error::ErrorKind) #[doc = "Pool error"];
	}
}

impl txpool::IntoPoolError for Error {
	fn into_pool_error(self) -> ::std::result::Result<txpool::error::Error, Self> {
		match self {
			Error(ErrorKind::Pool(e), c) => Ok(txpool::error::Error(e, c)),
			e => Err(e),
		}
	}
}
