// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Substrate dev API containing RPCs that are mainly meant for debugging and stats collection for
//! developers. The endpoints in this RPC module are not meant to be available to non-local users
//! and are all marked `unsafe`.

pub mod error;

use codec::{Decode, Encode};
use jsonrpsee::{core::RpcResult, proc_macros::rpc};
use scale_info::TypeInfo;
use serde::{Deserialize, Serialize};

/// Statistics of a block returned by the `dev_getBlockStats` RPC.
#[derive(Eq, PartialEq, Clone, Copy, Encode, Decode, Debug, TypeInfo, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BlockStats {
	/// The length in bytes of the storage proof produced by executing the block.
	pub witness_len: u64,
	/// The length in bytes of the storage proof after compaction.
	pub witness_compact_len: u64,
	/// Length of the block in bytes.
	///
	/// This information can also be acquired by downloading the whole block. This merely
	/// saves some complexity on the client side.
	pub block_len: u64,
	/// Number of extrinsics in the block.
	///
	/// This information can also be acquired by downloading the whole block. This merely
	/// saves some complexity on the client side.
	pub num_extrinsics: u64,
}

/// Substrate dev API.
///
/// This API contains unstable and unsafe methods only meant for development nodes. They
/// are all flagged as unsafe for this reason.
#[rpc(client, server)]
pub trait DevApi<Hash> {
	/// Reexecute the specified `block_hash` and gather statistics while doing so.
	///
	/// This function requires the specified block and its parent to be available
	/// at the queried node. If either the specified block or the parent is pruned,
	/// this function will return `None`.
	#[method(name = "dev_getBlockStats")]
	fn block_stats(&self, block_hash: Hash) -> RpcResult<Option<BlockStats>>;
}
