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

//! Errors that can occur during the service operation.

// Silence: `use of deprecated item 'std::error::Error::cause': replaced by Error::source, which can support downcasting`
// https://github.com/paritytech/substrate/issues/1547
#![allow(deprecated)]

use client;
use network;
use keystore;
use consensus_common;
use error_chain::*;

error_chain! {
	foreign_links {
		Io(::std::io::Error) #[doc="IO error"];
	}

	links {
		Client(client::error::Error, client::error::ErrorKind) #[doc="Client error"];
		Consensus(consensus_common::Error, consensus_common::ErrorKind) #[doc="Consesus error"];
		Network(network::error::Error, network::error::ErrorKind) #[doc="Network error"];
		Keystore(keystore::Error, keystore::ErrorKind) #[doc="Keystore error"];
	}

	errors {
	}
}
