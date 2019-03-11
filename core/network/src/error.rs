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

//! Substrate service possible errors.

// Silence: `use of deprecated item 'std::error::Error::cause': replaced by Error::source, which can support downcasting`
// https://github.com/paritytech/substrate/issues/1547
#![allow(deprecated)]

use error_chain::*;
use std::io::Error as IoError;
use network_libp2p::Error as NetworkError;
use client;

error_chain! {
	foreign_links {
		Network(NetworkError) #[doc = "Devp2p error."];
		Io(IoError) #[doc = "IO error."];
	}

	links {
		Client(client::error::Error, client::error::ErrorKind) #[doc="Client error"];
	}

	errors {
	}
}
