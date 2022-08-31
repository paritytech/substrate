// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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
use structopt::StructOpt;
use sc_service::TransactionStorageMode;

/// Parameters for block import.
#[derive(Debug, StructOpt)]
pub struct DatabaseParams {
	/// Select database backend to use.
	#[structopt(
		long,
		alias = "db",
		value_name = "DB",
		case_insensitive = true,
	)]
	pub database: Option<Database>,

	/// Limit the memory the database cache can use.
	#[structopt(long = "db-cache", value_name = "MiB")]
	pub database_cache_size: Option<usize>,

	/// Enable storage chain mode
	///
	/// This changes the storage format for blocks bodys. 
	/// If this is enabled, each transaction is stored separately in the
	/// transaction database column and is only referenced by hash
	/// in the block body column.
	#[structopt(long)]
	pub storage_chain: bool,
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

	/// Transaction storage scheme.
	pub fn transaction_storage(&self) -> TransactionStorageMode {
		if self.storage_chain {
			TransactionStorageMode::StorageChain
		} else {
			TransactionStorageMode::BlockBody
		}
	}
}
