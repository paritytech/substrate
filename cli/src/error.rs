// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Initialization errors.

use client;

error_chain! {
	foreign_links {
		Io(::std::io::Error) #[doc="IO error"];
		Cli(::clap::Error) #[doc="CLI error"];
	}
	links {
		Client(client::error::Error, client::error::ErrorKind) #[doc="Client error"];
    }
}
