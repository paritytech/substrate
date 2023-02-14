// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use crate::arg_enums::Database;
use clap::Args;

/// Parameters for block import.
#[derive(Debug, Clone, PartialEq, Args)]
pub struct DatabaseParams {
	/// Select database backend to use.
	#[arg(long, alias = "db", value_name = "DB", ignore_case = true, value_enum)]
	pub database: Option<Database>,

	/// Limit the memory the database cache can use.
	#[arg(long = "db-cache", value_name = "MiB")]
	pub database_cache_size: Option<usize>,
}

impl DatabaseParams {
	/// Limit the memory the database cache can use.
	pub fn database(&self) -> Option<Database> {
		self.database
	}

	/// Limit the memory the database cache can use.
	pub fn database_cache_size(&self) -> Option<usize> {
		self.database_cache_size
	}
}
