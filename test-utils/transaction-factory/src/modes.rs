// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! The transaction factory can operate in different modes. See
//! the `simple_mode` and `complex_mode` modules for details.

use std::str::FromStr;

/// Token distribution modes.
#[derive(Debug, Clone, PartialEq)]
pub enum Mode {
	MasterToN,
	MasterTo1,
	MasterToNToM
}

impl FromStr for Mode {
	type Err = String;
	fn from_str(mode: &str) -> Result<Self, Self::Err> {
		match mode {
			"MasterToN" => Ok(Mode::MasterToN),
			"MasterTo1" => Ok(Mode::MasterTo1),
			"MasterToNToM" => Ok(Mode::MasterToNToM),
			_ => Err(format!("Invalid mode: {}", mode)),
		}
	}
}

