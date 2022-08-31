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

//! Transaction pool error.

use sp_transaction_pool::error::Error as TxPoolError;

/// Transaction pool result.
pub type Result<T> = std::result::Result<T, Error>;

/// Transaction pool error type.
#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)]
pub enum Error {
	#[error("Transaction pool error")]
	Pool(#[from] TxPoolError),

	#[error("Blockchain error")]
	Blockchain(#[from] sp_blockchain::Error),

	#[error("Block conversion error: {0}")]
	BlockIdConversion(String),

	#[error("Runtime error: {0}")]
	RuntimeApi(String),
}


impl sp_transaction_pool::error::IntoPoolError for Error {
	fn into_pool_error(self) -> std::result::Result<TxPoolError, Self> {
		match self {
			Error::Pool(e) => Ok(e),
			e => Err(e),
		}
	}
}
