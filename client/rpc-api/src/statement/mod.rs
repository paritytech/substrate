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

//! Substrate Statement Store RPC API.

use jsonrpsee::{core::RpcResult, proc_macros::rpc};
use sp_core::Bytes;

pub mod error;

/// Substrate statement RPC API
#[rpc(client, server)]
pub trait StatementApi {
	/// Return all statements, SCALE-encoded.
	#[method(name = "statement_dump")]
	fn dump(&self) -> RpcResult<Vec<Bytes>>;

	/// Return the data of all known statements which include all topics and have no `DecryptionKey`
	/// field.
	#[method(name = "statement_broadcasts")]
	fn broadcasts(&self, match_all_topics: Vec<[u8; 32]>) -> RpcResult<Vec<Bytes>>;

	/// Return the data of all known statements whose decryption key is identified as `dest` (this
	/// will generally be the public key or a hash thereof for symmetric ciphers, or a hash of the
	/// private key for symmetric ciphers).
	#[method(name = "statement_posted")]
	fn posted(&self, match_all_topics: Vec<[u8; 32]>, dest: [u8; 32]) -> RpcResult<Vec<Bytes>>;

	/// Return the decrypted data of all known statements whose decryption key is identified as
	/// `dest`. The key must be available to the client.
	#[method(name = "statement_postedClear")]
	fn posted_clear(
		&self,
		match_all_topics: Vec<[u8; 32]>,
		dest: [u8; 32],
	) -> RpcResult<Vec<Bytes>>;

	/// Submit a pre-encoded statement.
	#[method(name = "statement_submit")]
	fn submit(&self, encoded: Bytes) -> RpcResult<()>;

	/// Remove a statement from the store.
	#[method(name = "statement_remove")]
	fn remove(&self, statement_hash: [u8; 32]) -> RpcResult<()>;
}
