// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use std::sync::Arc;

use sp_runtime::traits::Block as BlockT;

use futures::{FutureExt, SinkExt, StreamExt};
use jsonrpc_derive::rpc;
use jsonrpc_pubsub::{manager::SubscriptionManager, typed::Subscriber, SubscriptionId};
use log::warn;

use beefy_gadget::notification::BeefySignedCommitmentStream;

mod notification;

/// Provides RPC methods for interacting with BEEFY.
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
	fn subscribe_justifications(
		&self,
		metadata: Self::Metadata,
		subscriber: Subscriber<Notification>,
	);

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
pub struct BeefyRpcHandler<Block: BlockT> {
	signed_commitment_stream: BeefySignedCommitmentStream<Block>,
	manager: SubscriptionManager,
}

impl<Block: BlockT> BeefyRpcHandler<Block> {
	/// Creates a new BeefyRpcHandler instance.
	pub fn new<E>(signed_commitment_stream: BeefySignedCommitmentStream<Block>, executor: E) -> Self
	where
		E: futures::task::Spawn + Send + Sync + 'static,
	{
		let manager = SubscriptionManager::new(Arc::new(executor));
		Self { signed_commitment_stream, manager }
	}
}

impl<Block> BeefyApi<notification::SignedCommitment, Block> for BeefyRpcHandler<Block>
where
	Block: BlockT,
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
			.map(|x| Ok::<_, ()>(Ok(notification::SignedCommitment::new::<Block>(x))));

		self.manager.add(subscriber, |sink| {
			stream
				.forward(sink.sink_map_err(|e| warn!("Error sending notifications: {:?}", e)))
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
