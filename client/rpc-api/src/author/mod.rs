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

//! Substrate block-author/full-node API.

pub mod error;
pub mod hash;

use error::Error;
use jsonrpsee::proc_macros::rpc;
use sc_transaction_pool_api::TransactionStatus;
use sp_core::Bytes;

/// Substrate authoring RPC API
#[rpc(client, server)]
pub trait AuthorApi<Hash, BlockHash> {
	/// Submit hex-encoded extrinsic for inclusion in block.
	#[method(name = "author_submitExtrinsic")]
	async fn submit_extrinsic(&self, extrinsic: Bytes) -> Result<Hash, Error>;

	/// Insert a key into the keystore.
	#[method(name = "author_insertKey")]
	fn insert_key(&self, key_type: String, suri: String, public: Bytes) -> Result<(), Error>;

	/// Generate new session keys and returns the corresponding public keys.
	#[method(name = "author_rotateKeys")]
	fn rotate_keys(&self) -> Result<Bytes, Error>;

	/// Checks if the keystore has private keys for the given session public keys.
	///
	/// `session_keys` is the SCALE encoded session keys object from the runtime.
	///
	/// Returns `true` iff all private keys could be found.
	#[method(name = "author_hasSessionKeys")]
	fn has_session_keys(&self, session_keys: Bytes) -> Result<bool, Error>;

	/// Checks if the keystore has private keys for the given public key and key type.
	///
	/// Returns `true` if a private key could be found.
	#[method(name = "author_hasKey")]
	fn has_key(&self, public_key: Bytes, key_type: String) -> Result<bool, Error>;

	/// Returns all pending extrinsics, potentially grouped by sender.
	#[method(name = "author_pendingExtrinsics")]
	fn pending_extrinsics(&self) -> Result<Vec<Bytes>, Error>;

	/// Remove given extrinsic from the pool and temporarily ban it to prevent reimporting.
	#[method(name = "author_removeExtrinsic")]
	fn remove_extrinsic(
		&self,
		bytes_or_hash: Vec<hash::ExtrinsicOrHash<Hash>>,
	) -> Result<Vec<Hash>, Error>;

	/// Submit an extrinsic to watch.
	///
	/// See [`TransactionStatus`](sc_transaction_pool_api::TransactionStatus) for details on
	/// transaction life cycle.
	#[subscription(
		name = "author_submitAndWatchExtrinsic" => "author_extrinsicUpdate",
		unsubscribe = "author_unwatchExtrinsic",
		item = TransactionStatus<Hash, BlockHash>,
	)]
	fn watch_extrinsic(&self, bytes: Bytes);
}
