// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Substrate blockchain API.

pub mod error;
pub mod number;

use jsonrpc_core::Result as RpcResult;
use jsonrpc_core::futures::Future;
use jsonrpc_derive::rpc;
use jsonrpc_pubsub::{typed::Subscriber, SubscriptionId};
use self::error::{FutureResult, Result};

pub use self::gen_client::Client as ChainClient;

/// Substrate blockchain API
#[rpc]
pub trait ChainApi<Number, Hash, Header, SignedBlock> {
	/// RPC metadata
	type Metadata;

	/// Get header of a relay chain block.
	#[rpc(name = "chain_getHeader")]
	fn header(&self, hash: Option<Hash>) -> FutureResult<Option<Header>>;

	/// Get header and body of a relay chain block.
	#[rpc(name = "chain_getBlock")]
	fn block(&self, hash: Option<Hash>) -> FutureResult<Option<SignedBlock>>;

	/// Get hash of the n-th block in the canon chain.
	///
	/// By default returns latest block hash.
	#[rpc(name = "chain_getBlockHash", alias("chain_getHead"))]
	fn block_hash(&self, hash: Option<number::NumberOrHex<Number>>) -> Result<Option<Hash>>;

	/// Get hash of the last finalized block in the canon chain.
	#[rpc(name = "chain_getFinalizedHead", alias("chain_getFinalisedHead"))]
	fn finalized_head(&self) -> Result<Hash>;

	/// New head subscription
	#[pubsub(
		subscription = "chain_newHead",
		subscribe,
		name = "chain_subscribeNewHeads",
		alias("subscribe_newHead", "chain_subscribeNewHead")
	)]
	fn subscribe_new_heads(&self, metadata: Self::Metadata, subscriber: Subscriber<Header>);

	/// Unsubscribe from new head subscription.
	#[pubsub(
		subscription = "chain_newHead",
		unsubscribe,
		name = "chain_unsubscribeNewHeads",
		alias("unsubscribe_newHead", "chain_unsubscribeNewHead")
	)]
	fn unsubscribe_new_heads(&self, metadata: Option<Self::Metadata>, id: SubscriptionId) -> RpcResult<bool>;

	/// New head subscription
	#[pubsub(
		subscription = "chain_finalizedHead",
		subscribe,
		name = "chain_subscribeFinalizedHeads",
		alias("chain_subscribeFinalisedHeads")
	)]
	fn subscribe_finalized_heads(&self, metadata: Self::Metadata, subscriber: Subscriber<Header>);

	/// Unsubscribe from new head subscription.
	#[pubsub(
		subscription = "chain_finalizedHead",
		unsubscribe,
		name = "chain_unsubscribeFinalizedHeads",
		alias("chain_unsubscribeFinalisedHeads")
	)]
	fn unsubscribe_finalized_heads(&self, metadata: Option<Self::Metadata>, id: SubscriptionId) -> RpcResult<bool>;
}
