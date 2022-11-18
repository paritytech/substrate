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

#![allow(non_snake_case)]

//! API trait of the archive functions.
use crate::archive::event::{ArchiveEvent, NetworkConfig};
use jsonrpsee::{core::RpcResult, proc_macros::rpc};

#[rpc(client, server)]
pub trait ArchiveApi<Hash> {
	/// Retrieves the body (list of transactions) of an archive block.
	//
	/// Use `chainHead_unstable_body` if instead you want to retrieve the body of a recent block.
	///
	/// # Unstable
	///
	/// This method is unstable and subject to change in the future.
	#[subscription(
		name = "archive_unstable_body",
		unsubscribe = "archive_unstable_stopBody",
		item = ArchiveEvent<String>,
	)]
	fn archive_unstable_body(&self, hash: Hash, networkConfig: Option<NetworkConfig>);

	/// Get the chain's genesis hash.
	///
	/// # Unstable
	///
	/// This method is unstable and subject to change in the future.
	#[method(name = "archive_unstable_genesisHash", blocking)]
	fn archive_unstable_genesis_hash(&self) -> RpcResult<String>;

	/// Retrieves the hashes of the blocks that have the specified height.
	///
	/// If the height parameter is less or equal to the latest finalized block
	/// height, then only finalized blocks are fetched.
	///
	/// # Unstable
	///
	/// This method is unstable and subject to change in the future.
	#[subscription(
		name = "archive_unstable_hashByHeight",
		unsubscribe = "archive_unstable_stopHashByHeight",
		item = ArchiveEvent<String>,
	)]
	fn archive_unstable_hash_by_height(&self, height: String, networkConfig: Option<NetworkConfig>);

	/// Retrieves the header of an archive block.
	///
	/// Use `chainHead_unstable_header` if instead you want to retrieve the header of a
	/// recent block.
	///
	/// # Unstable
	///
	/// This method is unstable and subject to change in the future.
	#[subscription(
		name = "archive_unstable_header",
		unsubscribe = "archive_unstable_stopHeader",
		item = ArchiveEvent<String>,
	)]
	fn archive_unstable_header(&self, hash: Hash, networkConfig: Option<NetworkConfig>);

	/// Return a storage entry at a specific block's state.
	///
	/// Use `chainHead_unstable_storage` if instead you want to retrieve the
	/// storage of a recent block.
	///
	/// # Unstable
	///
	/// This method is unstable and subject to change in the future.
	#[subscription(
		name = "archive_unstable_storage",
		unsubscribe = "archive_unstable_stopStorage",
		item = ArchiveEvent<String>,
	)]
	fn archive_unstable_storage(
		&self,
		hash: Hash,
		key: String,
		childKey: Option<String>,
		networkConfig: Option<NetworkConfig>,
	);
}
