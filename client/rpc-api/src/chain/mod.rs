// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use jsonrpsee::{core::RpcResult, proc_macros::rpc};
use sp_rpc::{list::ListOrValue, number::NumberOrHex};

pub mod error;

#[rpc(client, server)]
pub trait ChainApi<Number, Hash, Header, SignedBlock> {
	/// Get header.
	#[method(name = "chain_getHeader")]
	async fn header(&self, hash: Option<Hash>) -> RpcResult<Option<Header>>;

	/// Get header and body of a relay chain block.
	#[method(name = "chain_getBlock")]
	async fn block(&self, hash: Option<Hash>) -> RpcResult<Option<SignedBlock>>;

	/// Get hash of the n-th block in the canon chain.
	///
	/// By default returns latest block hash.
	#[method(name = "chain_getBlockHash", aliases = ["chain_getHead"])]
	fn block_hash(
		&self,
		hash: Option<ListOrValue<NumberOrHex>>,
	) -> RpcResult<ListOrValue<Option<Hash>>>;

	/// Get hash of the last finalized block in the canon chain.
	#[method(name = "chain_getFinalizedHead", aliases = ["chain_getFinalisedHead"])]
	fn finalized_head(&self) -> RpcResult<Hash>;

	/// All head subscription.
	#[subscription(
		name = "chain_subscribeAllHeads" => "chain_allHead",
		unsubscribe = "chain_unsubscribeAllHeads",
		item = Header
	)]
	fn subscribe_all_heads(&self);

	/// New head subscription.
	#[subscription(
		name = "chain_subscribeNewHeads" => "chain_newHead",
		aliases = ["subscribe_newHead", "chain_subscribeNewHead"],
		unsubscribe = "chain_unsubscribeNewHeads",
		unsubscribe_aliases = ["unsubscribe_newHead", "chain_unsubscribeNewHead"],
		item = Header
	)]
	fn subscribe_new_heads(&self);

	/// Finalized head subscription.
	#[subscription(
		name = "chain_subscribeFinalizedHeads" => "chain_finalizedHead",
		aliases = ["chain_subscribeFinalisedHeads"],
		unsubscribe = "chain_unsubscribeFinalizedHeads",
		unsubscribe_aliases = ["chain_unsubscribeFinalisedHeads"],
		item = Header
	)]
	fn subscribe_finalized_heads(&self);
}
