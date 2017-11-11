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

use std::{error, fmt, result};

use bytes;

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CallData(#[serde(with="bytes")] pub Vec<u8>);

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OutData(#[serde(with="bytes")] pub Vec<u8>);

#[derive(Debug, PartialEq, Eq)]
pub struct Panic;

impl fmt::Display for Panic {
	fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
		write!(fmt, "Panic!")
	}
}

impl error::Error for Panic {
	fn description(&self) -> &str {
		"The execution did blow up."
	}
}

pub type Result<T> = result::Result<T, Panic>;
