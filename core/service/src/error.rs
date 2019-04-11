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
		Client(client::error::Error) #[doc="Client error"];
		Io(::std::io::Error) #[doc="IO error"];
	}

	links {
		Consensus(consensus_common::Error, consensus_common::ErrorKind) #[doc="Consensus error"];
		Network(network::error::Error, network::error::ErrorKind) #[doc="Network error"];
		Keystore(keystore::Error, keystore::ErrorKind) #[doc="Keystore error"];
	}

	errors {
	}
}
