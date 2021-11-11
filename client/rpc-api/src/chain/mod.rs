// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Substrate blockchain API.

use jsonrpsee::{proc_macros::rpc, types::RpcResult};
use sp_rpc::{list::ListOrValue, number::NumberOrHex};

pub mod error;

#[rpc(client, server, namespace = "chain")]
pub trait ChainApi<Number, Hash, Header, SignedBlock> {
	/// Get header.
	#[method(name = "getHeader")]
	async fn header(&self, hash: Option<Hash>) -> RpcResult<Option<Header>>;

	/// Get header and body of a relay chain block.
	#[method(name = "getBlock")]
	async fn block(&self, hash: Option<Hash>) -> RpcResult<Option<SignedBlock>>;

	/// Get hash of the n-th block in the canon chain.
	///
	/// By default returns latest block hash.
	#[method(name = "getBlockHash", aliases = ["chain_getHead"])]
	fn block_hash(
		&self,
		hash: Option<ListOrValue<NumberOrHex>>,
	) -> RpcResult<ListOrValue<Option<Hash>>>;

	/// Get hash of the last finalized block in the canon chain.
	#[method(name = "getFinalizedHead", aliases = ["chain_getFinalisedHead"])]
	fn finalized_head(&self) -> RpcResult<Hash>;

	/// All head subscription.
	#[subscription(
		name = "allHead",
		aliases = ["chain_subscribeAllHeads"],
		unsubscribe_aliases = ["chain_unsubscribeAllHeads"],
		item = Header
	)]
	fn subscribe_all_heads(&self) -> RpcResult<()>;

	/// New head subscription.
	#[subscription(
		name = "newHead",
		aliases = ["subscribe_newHead", "chain_subscribeNewHead", "chain_subscribeNewHeads"],
		unsubscribe_aliases = ["chain_unsubscribeNewHead", "chain_unsubscribeNewHeads"],
		item = Header
	)]
	fn subscribe_new_heads(&self) -> RpcResult<()>;

	/// Finalized head subscription.
	#[subscription(
		name = "finalizedHead",
		aliases = ["chain_subscribeFinalisedHeads", "chain_subscribeFinalizedHeads"],
		unsubscribe_aliases = ["chain_unsubscribeFinalizedHeads", "chain_unsubscribeFinalisedHeads"],
		item = Header
	)]
	fn subscribe_finalized_heads(&self) -> RpcResult<()>;
}
