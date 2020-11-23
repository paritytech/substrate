// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! RPC API for BEEFY.

#![warn(missing_docs)]

use codec::Encode;
use futures::{StreamExt, TryStreamExt};
use jsonrpc_core::futures::{
	future::Executor as Executor01, future::Future as Future01, sink::Sink as Sink01, stream::Stream as Stream01,
};
use jsonrpc_derive::rpc;
use jsonrpc_pubsub::{manager::SubscriptionManager, typed::Subscriber, SubscriptionId};
use log::warn;
use std::sync::Arc;

mod notification;

use sp_runtime::traits::Block as BlockT;

use beefy_gadget::notification::BeefySignedCommitmentStream;

/// Provides RPC methods for interacting with BEEFY.
#[allow(clippy::needless_return)]
#[rpc]
pub trait BeefyApi<Notification, Hash> {
	/// RPC Metadata
	type Metadata;

	/// Returns the block most recently finalized by BEEFY, alongside side its justification.
	#[pubsub(
		subscription = "beefy_justifications",
		subscribe,
		name = "beefy_subscribeJustifications"
	)]
	fn subscribe_justifications(&self, metadata: Self::Metadata, subscriber: Subscriber<Notification>);

	/// Unsubscribe from receiving notifications about recently finalized blocks.
	#[pubsub(
		subscription = "beefy_justifications",
		unsubscribe,
		name = "beefy_unsubscribeJustifications"
	)]
	fn unsubscribe_justifications(
		&self,
		metadata: Option<Self::Metadata>,
		id: SubscriptionId,
	) -> jsonrpc_core::Result<bool>;
}

/// Implements the BeefyApi RPC trait for interacting with BEEFY.
pub struct BeefyRpcHandler<Block: BlockT, Signature> {
	signed_commitment_stream: BeefySignedCommitmentStream<Block, Signature>,
	manager: SubscriptionManager,
}

impl<Block: BlockT, Signature> BeefyRpcHandler<Block, Signature> {
	/// Creates a new BeefyRpcHandler instance.
	pub fn new<E>(signed_commitment_stream: BeefySignedCommitmentStream<Block, Signature>, executor: E) -> Self
	where
		E: Executor01<Box<dyn Future01<Item = (), Error = ()> + Send>> + Send + Sync + 'static,
	{
		let manager = SubscriptionManager::new(Arc::new(executor));
		Self {
			signed_commitment_stream,
			manager,
		}
	}
}

impl<Block, Signature> BeefyApi<notification::SignedCommitment, Block> for BeefyRpcHandler<Block, Signature>
where
	Block: BlockT,
	Signature: Clone + Encode + Send + 'static,
{
	type Metadata = sc_rpc::Metadata;

	fn subscribe_justifications(
		&self,
		_metadata: Self::Metadata,
		subscriber: Subscriber<notification::SignedCommitment>,
	) {
		let stream = self
			.signed_commitment_stream
			.subscribe()
			.map(|x| Ok::<_, ()>(notification::SignedCommitment::new::<Block, Signature>(x)))
			.map_err(|e| warn!("Notification stream error: {:?}", e))
			.compat();

		self.manager.add(subscriber, |sink| {
			let stream = stream.map(Ok);
			sink.sink_map_err(|e| warn!("Error sending notifications: {:?}", e))
				.send_all(stream)
				.map(|_| ())
		});
	}

	fn unsubscribe_justifications(
		&self,
		_metadata: Option<Self::Metadata>,
		id: SubscriptionId,
	) -> jsonrpc_core::Result<bool> {
		Ok(self.manager.cancel(id))
	}
}
