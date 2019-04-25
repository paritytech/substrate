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

//! Initialization errors.

// Silence: `use of deprecated item 'std::error::Error::cause': replaced by Error::source, which can support downcasting`
// https://github.com/paritytech/substrate/issues/1547
#![allow(deprecated)]

use client;
use error_chain::{error_chain, error_chain_processing, impl_error_chain_processed,
	impl_extract_backtrace, impl_error_chain_kind};

error_chain! {
	foreign_links {
		Io(::std::io::Error) #[doc="IO error"];
		Cli(::clap::Error) #[doc="CLI error"];
		Service(::service::Error) #[doc="Substrate service error"];
	}
	links {
		Client(client::error::Error, client::error::ErrorKind) #[doc="Client error"];
	}
	errors {
		/// Input error.
		Input(m: String) {
			description("Invalid input"),
			display("{}", m),
		}
	}
}
