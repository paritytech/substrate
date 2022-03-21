// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Substrate dev API.

pub mod error;

use self::error::Result;
use jsonrpc_derive::rpc;

/// Substrate dev API.
///
/// This API contains unstable and unsafe methods only meant for development nodes. They
/// are all flagged as unsafe for this reason.
#[rpc]
pub trait DevApi<Hash, BlockStats> {
	/// Reexecute the specified `block_hash` and gather statistics while doing so.
	///
	/// This function will require the specified block and its parent to be available
	/// at the queried node. If either the specified block or the parent are not available,
	/// this function will return `None`.
	#[rpc(name = "dev_getBlockStats")]
	fn block_stats(&self, block_hash: Hash) -> Result<Option<BlockStats>>;
}
